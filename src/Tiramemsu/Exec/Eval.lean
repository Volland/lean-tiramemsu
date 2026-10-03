/-
The evaluator: one read program per query, generic over the store (run on a model state for
proofs and tests, on a pinned SQLite snapshot by the API). It computes the reference bag
(`Sem.denote`) with physical choices that change only speed:

- triple patterns are read through the sorted range scans with every position bound by a
  constant or an earlier binding used as a key prefix (constants are dictionary lookups that
  never insert; an unknown constant empties the pattern);
- a `Join` evaluates its non-pattern inputs first, then runs its stored patterns as an index
  nested loop in a greedy order (most bound positions first, then text order), applying each
  pushed filter conjunct as soon as the patterns placed so far bind its variables;
- a `LeftJoin` whose right side is a join of stored patterns passes each left row sideways
  into it;
- every other operator reuses the bag operators of `Sem`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Std.Data.HashMap
import Tiramemsu.Exec.Scan

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem
open Tiramemsu.Engine (RProg ROp)

--# @lat: [[query#Index Nested-Loop Join]]

/-- The evaluator monad: query errors over read programs. -/
abbrev EvM := ExceptT QError RProg

def liftR {α : Type} (p : RProg α) : EvM α := ExceptT.lift p

/-- Decodes an id. -/
def decodeE (x : Int64) : EvM Value := do
  match ← liftR (Term.decode (m := RProg) ⟨x⟩) with
  | .ok v => pure v
  | .error e => throw (.invalidTerm (toString (repr e)))

/-- The id of a value, by dictionary lookup only (`none`: not stored, so nothing matches). -/
def lookupE (v : Value) : EvM (Option Int64) := do
  match ← liftR (Term.lookupValue (m := RProg) v) with
  | .ok o => pure (o.map (·.raw))
  | .error _ => pure none

/-- The store view of a view spec. -/
def resolveViewE (v : View.ViewSpec) : EvM Store.View := liftR (View.resolve v)

/-! ## Stored triple patterns -/

/-- A pattern position under an outer row: `none` can never match, `some none` is free,
`some (some x)` is bound to the id `x`. -/
def posId (E : Env) (a : Row) : TermOrVar → EvM (Option (Option Int64))
  | .var v => do
    match a.get (E.idx v) with
    | some val => return (← lookupE val).map some
    | none => return some none
  | .const c => do return (← lookupE c.canonical).map some
  | .id o => return some (some o.raw)
  | .param _ => return none

/-- Binds or checks a decoded value. -/
def bindE (E : Env) (t : TermOrVar) (x : Int64) (r : Row) : EvM (Option Row) :=
  match t with
  | .var v => do return bindVal E v (← decodeE x) r
  | .const c => do return if (← decodeE x) == c.canonical then some r else none
  | .id o => return if o.raw == x then some r else none
  | .param _ => return none

/-- The graphs of a statement, through its visible memberships. -/
def membershipsE (v : Store.View) (e : Int64) : EvM (List Value) := do
  match ← lookupE (.iri Engine.Vocab.sysInGraph) with
  | none => return []
  | some ig =>
    let ms ← liftR (rangeScan .spo v [e, ig])
    ms.mapM fun m => decodeE m.o

/-- The pattern rows (fresh, unmerged) of one statement. -/
def patRowsOf (E : Env) (v : Store.View) (t : TriplePattern) (r : TripleRow) : EvM (List Row) := do
  let some row ← bindE E t.s r.s (Row.empty E.n) | return []
  let some row ← bindE E t.p r.p row | return []
  let some row ← bindE E t.o r.o row | return []
  let row? ← match t.eid with
    | some ev => do pure (bindVal E ev (← decodeE r.eid) row)
    | none => pure (some row)
  let some row := row? | return []
  match t.graph with
  | .any => return [row]
  | .set gs =>
    let want := gs.filterMap fun g => match g with | .const c => some c.canonical | _ => none
    let ms ← membershipsE v r.eid
    return if ms.any want.contains then [row] else []
  | .var gv =>
    let ms ← membershipsE v r.eid
    return ms.filterMap fun m => bindVal E gv m row

/-- The statements a pattern can match under an outer row, through the index whose prefix is
exactly the bound positions, or the eid lookup when the eid is bound. -/
def candidateScan (E : Env) (v : Store.View) (t : TriplePattern) (a : Row) : EvM (List TripleRow) := do
  let byEid : Option Value := t.eid.bind fun ev => a.get (E.idx ev)
  match byEid with
  | some val =>
    match ← lookupE val with
    | some e => return (← liftR (lookupEid v e)).toList
    | none => return []
  | none =>
    let some s ← posId E a t.s | return []
    let some p ← posId E a t.p | return []
    let some o ← posId E a t.o | return []
    let (ord, pfx) := indexFor s p o
    liftR (rangeScan ord v pfx)

/-- The candidates, with adjacent equal-content statements dropped under `SetOfTriples` without
an eid variable or graph selector. -/
def candidateRows (E : Env) (v : Store.View) (t : TriplePattern) (a : Row) : EvM (List TripleRow) := do
  let rows ← candidateScan E v t a
  let set := E.sem.graphSet == .setOfTriples && t.eid.isNone
  return if set && t.graph == .any then dedupAdj rows else rows

/-- The pattern rows compatible candidates of an outer row (a set under `SetOfTriples`
without an eid variable). -/
def patternRows (E : Env) (v : Store.View) (t : TriplePattern) (a : Row) : EvM Bag := do
  let rows ← candidateRows E v t a
  let out := (← rows.mapM (patRowsOf E v t)).flatten
  let set := E.sem.graphSet == .setOfTriples && t.eid.isNone
  return if set && t.graph != .any then out.eraseDups else out

/-- One index nested-loop step: each outer row merged with its compatible pattern rows. -/
def inljStep (E : Env) (P Q : Schema) (v : Store.View) (t : TriplePattern) (xs : Bag) : EvM Bag := do
  let parts ← xs.mapM fun a => do
    let bs ← patternRows E v t a
    return (bs.filter (compat E.sem.missing P Q a)).map (merge a)
  return parts.flatten

/-! ## Virtual-predicate patterns -/

def instantE (t : Int64) : EvM (Option Value) := do
  return (← liftR (RProg.lift (.txByT t))).map fun x => .dateTime x.instant.toInt (some 0)

def virtualValueE (vp : VirtualPred) (r : TripleRow) : EvM (Option Value) :=
  match vp with
  | .subject => do return some (← decodeE r.s)
  | .predicate => do return some (← decodeE r.p)
  | .object => do return some (← decodeE r.o)
  | .txAdded => return some (.tx r.tAdd.toInt.toNat)
  | .txRetracted => return r.tRet.map fun t => .tx t.toInt.toNat
  | .addedAt => instantE r.tAdd
  | .retractedAt => match r.tRet with
    | some t => instantE t
    | none => return none
  | .validFrom => return r.vFrom.map fun x => .dateTime x.toInt (some 0)
  | .validTo => return r.vTo.map fun x => .dateTime x.toInt (some 0)
  | .retractKind => return r.retKind.map fun k => .int k.toInt

def matchValE (E : Env) (byValue : Bool) (t : TermOrVar) (val : Value) (r : Row) : EvM (Option Row) :=
  match t with
  | .var v => return bindVal E v val r
  | .const c => return (if (if byValue then valueEq val c.canonical else val == c.canonical) then some r else none)
  | .id o => do return if (← decodeE o.raw) == val then some r else none
  | .param _ => return none

/-- The bag of a virtual-predicate pattern: an eid lookup when the subject is a constant,
otherwise every visible statement. -/
def virtualPat (E : Env) (t : TriplePattern) (vp : VirtualPred) : EvM Bag := do
  let v ← resolveViewE t.view
  let rows ← match t.s with
    | .const c => do
      match ← lookupE c.canonical with
      | some e => pure (← liftR (lookupEid v e)).toList
      | none => pure []
    | .id o => do pure (← liftR (lookupEid v o.raw)).toList
    | _ => do
      let rs ← liftR (rangeScan .spo v [])
      pure (rs.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt))
  let out ← (rows.map (View.mask v)).filterMapM fun r => do
    match ← virtualValueE vp r with
    | none => return none
    | some val =>
      match ← matchValE E false t.s (← decodeE r.eid) (Row.empty E.n) with
      | none => return none
      | some row => matchValE E vp.byInstant t.o val row
  return if E.sem.graphSet == .setOfTriples then out.eraseDups else out

/-! ## Join planning -/

/-- A stored (non-virtual) triple pattern. -/
def storedPat? : Op → Option TriplePattern
  | .triple t => if t.p.virtual?.isNone then some t else none
  | _ => none

def TermOrVar.boundBy (bound : List Var) : TermOrVar → Bool
  | .var v => bound.contains v
  | _ => true

/-- The number of positions of a pattern bound by constants or by `bound`. -/
def boundCount (bound : List Var) (t : TriplePattern) : Nat :=
  [t.s, t.p, t.o].countP (TermOrVar.boundBy bound)

/-- The greedy order: repeatedly the pattern with the most bound positions, ties in text order. -/
def greedyOrder (bound0 : List Var) (pats : List (Nat × TriplePattern))
    (count : Value → Option Nat := fun _ => none) : List (Nat × TriplePattern) :=
  go pats.length bound0 pats
where
  /-- The statement count of a pattern's predicate (unknown or variable: largest). -/
  cnt (t : TriplePattern) : Nat := match t.p with
    | .const c => (count c.canonical).getD (2 ^ 62)
    | _ => 2 ^ 63
  better (bound : List Var) (p b : Nat × TriplePattern) : Bool :=
    boundCount bound p.2 > boundCount bound b.2 ||
      (boundCount bound p.2 == boundCount bound b.2 && cnt p.2 < cnt b.2)
  go : Nat → List Var → List (Nat × TriplePattern) → List (Nat × TriplePattern)
    | 0, _, rest => rest
    | _, _, [] => []
    | fuel + 1, bound, rest@(first :: _) =>
      let best := rest.foldl (fun b p => if better bound p b then p else b) first
      best :: go fuel (bound ++ best.2.vars) (rest.filter (·.1 != best.1))

mutual

/-- The variable positions an expression reads, and whether it holds an `EXISTS` (whose
result depends on the whole row). -/
def rvarsOf : RExpr → List Nat × Bool
  | .var i | .bound i => ([i], false)
  | .const _ | .err => ([], false)
  | .exists .. => ([], true)
  | .cmp _ a b | .sameTerm a b | .arith _ a b =>
    let x := rvarsOf a
    let y := rvarsOf b
    (x.1 ++ y.1, x.2 || y.2)
  | .not a | .neg a => rvarsOf a
  | .and xs | .or xs | .coalesce xs | .func _ xs => rvarsOfList xs
  | .inList a xs _ =>
    let x := rvarsOf a
    let y := rvarsOfList xs
    (x.1 ++ y.1, x.2 || y.2)
  | .ite c a b =>
    let x := rvarsOf c
    let y := rvarsOf a
    let z := rvarsOf b
    (x.1 ++ y.1 ++ z.1, x.2 || y.2 || z.2)

def rvarsOfList : List RExpr → List Nat × Bool
  | [] => ([], false)
  | x :: xs =>
    let a := rvarsOf x
    let b := rvarsOfList xs
    (a.1 ++ b.1, a.2 || b.2)

end

/-- The conjuncts of a resolved condition. -/
def splitAnd : RExpr → List RExpr
  | .and xs => xs
  | e => [e]

/-- The conjuncts of a condition. -/
def conjuncts : Expr → List Expr
  | .and xs => xs
  | e => [e]

/-- A pushed conjunct: its resolved condition, the positions it reads and whether it can be
applied early (no `EXISTS`). -/
structure Pushed where
  cond : RExpr
  vars : List Nat
  early : Bool

def Pushed.ofR (c : RExpr) : Pushed :=
  let (vs, ex) := rvarsOf c
  { cond := c, vars := vs, early := !ex }

/-- Runs the stored patterns of a join as an index nested loop from `acc` (rows with schema
`P`), applying each early conjunct once the patterns placed so far bind its variables.
Returns the rows, the final schema and the conjuncts not yet applied. -/
def inljRun (E : Env) (P : Schema) (acc : Bag) (order : List (Nat × TriplePattern))
    (conds : List Pushed) : EvM (Schema × Bag × List Pushed) :=
  go P acc [] conds order
where
  /-- One pattern at a time: scan, merge, then the conjuncts that became applicable. -/
  go (P : Schema) (rows : Bag) (bound : List Nat) (pending : List Pushed) :
      List (Nat × TriplePattern) → EvM (Schema × Bag × List Pushed)
    | [] => return (P, rows, pending)
    | (_, t) :: rest => do
      let v ← resolveViewE t.view
      let Q := E.schemaOf (.triple t)
      let rows ← inljStep E P Q v t rows
      let bound := bound ++ t.vars.map E.idx
      let (now, later) := pending.partition fun c => c.early && c.vars.all bound.contains
      go (Schema.union P Q) (now.foldl (fun r c => filterB c.cond r) rows) bound later rest

/-- A value whose value equality is term identity: the only value `valueEq` to it is itself.
Ids, booleans, plain strings, typed literals and non-skolem IRIs. Not numbers or date-times
(compared by value), dates (beyond the 64-bit range their keys alias), language strings (a
NUL in the text or a tag in another case gives the same sort key) or skolem IRIs (equal to an
id). -/
def identityKey : Value → Bool
  | .iri s => (skolemValue? s).isNone
  | .node _ | .bnode _ | .stmt _ | .tx _ | .bool _ | .str _ | .typed .. => true
  | _ => false

/-- A constant whose value equality is term identity, so an equality with it can become a
key-prefix constraint. -/
def identityConst? : RExpr → Option Value
  | .const k => if identityKey k then some k else none
  | _ => none

/-- `?v = k` with an identity constant: the position and the constant. -/
def prefixEq? : RExpr → Option (Nat × Value)
  | .cmp .eq (.var i) b => (identityConst? b).map (i, ·)
  | .cmp .eq a (.var i) => (identityConst? a).map (i, ·)
  | _ => none

/-- Seeds rows with the constants of pushed equalities on variables the stored patterns bind
(only where the row leaves the variable unbound), so the patterns scan with them as key
prefixes. Only variables no other input can bind are seeded (so they are unbound in every
row, also under `Null3VL`); the equalities stay pushed, so the rows are the same. -/
def seedEqs (P : Schema) (patVars : List Nat) (conds : List Pushed) (rows : Bag) : Bag :=
  let eqs := conds.filterMap fun c =>
    (prefixEq? c.cond).filter fun (i, _) => patVars.contains i && !(P.getD i false)
  rows.map fun r => eqs.foldl (fun r (i, k) => if (r.get i).isNone then r.setAt i (some k) else r) r

/-- The evaluator's path semantics: the pattern rows of a path pattern under an outer row. -/
abbrev PathE := Env → PathPattern → Row → EvM Bag

/-- Path patterns of a join, laterally, in input order. -/
def lateralPathsE (E : Env) (pathE : PathE) (P : Schema) (rows : Bag) : List PathPattern → EvM Bag
  | [] => return rows
  | p :: ps => do
    let Q := E.schemaOf (.path p)
    let parts ← rows.mapM fun a => do
      return ((← pathE E p a).filter (compat E.sem.missing P Q a)).map (merge a)
    lateralPathsE E pathE (Schema.union P Q) parts.flatten ps

/-- The positions every row of both inputs binds and both schemas mark: equal values there are
necessary for compatibility, so they key a hash join. -/
def hashKeys (P Q : Schema) (xs ys : Bag) : List Nat :=
  (List.range (max P.length Q.length)).filter fun i =>
    P.getD i false && Q.getD i false && xs.all (fun r => (r.get i).isSome) && ys.all (fun r => (r.get i).isSome)

/-- The bag join of two inputs, hashing the right one on its key positions (the same bag as
`joinB` up to order). -/
def joinHash (m : Missing) (P Q : Schema) (xs ys : Bag) : Bag :=
  let ks := hashKeys P Q xs ys
  if ks.isEmpty then joinB m P Q xs ys
  else
    let key (r : Row) : List Nat := rowKey (ks.map r.get)
    let idx : Std.HashMap (List Nat) (Array Row) := ys.foldl (fun h b =>
      h.insert (key b) ((h.getD (key b) #[]).push b)) ∅
    xs.flatMap fun a => ((idx.getD (key a) #[]).toList.filter (compat m P Q a)).map (merge a)

/-- The join of the non-pattern inputs, by hash on their shared bound positions. -/
def joinAllHash (m : Missing) (xs : List SBag) : SBag :=
  xs.foldl (fun (P, acc) (Q, ys) => (Schema.union P Q, joinHash m P Q acc ys)) ([], [[]])

/-- A `Join` given the bags of its non-pattern inputs (`none` for stored and path patterns). -/
def joinCore (E : Env) (pathE : PathE) (xs : List Op) (bags : List (Option Bag)) (conds : List Pushed) : EvM Bag := do
  let pairs := xs.zip bags
  let others : List SBag := pairs.filterMap fun (x, b) => match x with
    | .path _ => none
    | _ => b.map fun bag => (E.schemaOf x, bag)
  let (P, acc) := joinAllHash E.sem.missing others
  let pats := (xs.zipIdx.filterMap fun (x, i) => (storedPat? x).map (i, ·))
  let acc := seedEqs P (pats.flatMap fun (_, t) => t.vars.map E.idx) conds acc
  -- the certain variables of the non-pattern inputs and the seeded equalities count as bound
  let bound0 := (pairs.filterMap fun (x, b) => match x, b with
      | .path _, _ => none
      | _, some _ => some (scope x).certainVars
      | _, none => none).flatten ++
    (conds.filterMap fun c => (prefixEq? c.cond).map fun (i, _) => E.vars.getD i "")
  let order := greedyOrder bound0 pats E.predCount
  let (P, rows, rest) ← inljRun E P acc order conds
  let rows ← lateralPathsE E pathE P rows (xs.filterMap Op.pathPat?)
  let rows := rest.foldl (fun r c => filterB c.cond r) rows
  return isoFilter E.iso rows

/-- The stored patterns of a right side that can take bindings sideways. -/
def sidewaysPats : Op → Option (List TriplePattern)
  | .triple t => (storedPat? (.triple t)).map ([·])
  | .join xs =>
    let ps := xs.filterMap storedPat?
    if ps.length == xs.length && !xs.isEmpty then some ps else none
  | _ => none

/-- A `LeftJoin` whose right side is a join of stored patterns: each left row is passed into
the right side's index nested loop. -/
def leftJoinSideways (E : Env) (P : Schema) (c : Option RExpr) (pats : List TriplePattern)
    (xs : Bag) : EvM Bag := do
  let order := greedyOrder [] (pats.zipIdx.map fun (t, i) => (i, t)) E.predCount
  let parts ← xs.mapM fun a => do
    let (_, ms, _) ← inljRun E P [a] order []
    let ms := match c with
      | some e => ms.filter e.holds
      | none => ms
    return (if ms.isEmpty then [a] else ms)
  return isoFilter E.iso parts.flatten

/-- An inline-values row, decoding id cells. -/
def valuesRowE (E : Env) (vs : List Var) (cells : List (Option TermOrVar)) : EvM Row :=
  (vs.zip cells).foldlM (fun r (v, c) => do
    match c with
    | some (.const k) => return r.setAt (E.idx v) (some k.canonical)
    | some (.id o) => return r.setAt (E.idx v) (some (← decodeE o.raw))
    | _ => return r) (Row.empty E.n)

def liftEx {α : Type} : Except QError α → EvM α
  | .ok a => pure a
  | .error e => throw e

mutual

/-- The evaluator. `pathE` evaluates path patterns (the path engine). -/
def eval (E : Env) (pathE : PathE) : Op → EvM Bag
  | .triple t => do
    liftEx (checkOp (.triple t))
    match t.p.virtual? with
    | some vp => virtualPat E t vp
    | none => joinCore E pathE [.triple t] [none] []
  | .path p => do liftEx (checkOp (.path p)); pathE E p []
  | .values vs rows => do
    liftEx (checkOp (.values vs rows))
    rows.mapM (valuesRowE E vs)
  | .join xs => do
    let bags ← evalInputs E pathE xs
    joinCore E pathE xs bags []
  | .leftJoin l r c => do
    let lb ← eval E pathE l
    let c' ← resolveOptX E pathE c
    match (if E.iso.isEmpty then sidewaysPats r else none) with
    | some pats => leftJoinSideways E (E.schemaOf l) c' pats lb
    | none =>
      let rb ← eval E pathE r
      return isoFilter E.iso (leftJoinB E.sem.missing (E.schemaOf l) (E.schemaOf r) c' lb rb)
  | .union xs => do return (← evalList E pathE xs).flatten
  | .filter c x => do
    let cs := splitAnd (← resolveX E pathE c)
    match x with
    | .join xs => do
      let bags ← evalInputs E pathE xs
      joinCore E pathE xs bags (cs.map Pushed.ofR)
    | .triple t =>
      match t.p.virtual? with
      | none => do
        liftEx (checkOp (.triple t))
        joinCore E pathE [.triple t] [none] (cs.map Pushed.ofR)
      | some vp => do
        liftEx (checkOp (.triple t))
        let b ← virtualPat E t vp
        return cs.foldl (fun r c => filterB c r) b
    | other => do
      let b ← eval E pathE other
      return cs.foldl (fun r c => filterB c r) b
  | .extend v e x => do
    liftEx (checkOp (.extend v e x))
    let e' ← resolveX E pathE e
    return extendB (E.idx v) e' (← eval E pathE x)
  | .aggregate g aggs x => do
    liftEx (checkOp (.aggregate g aggs x))
    let as ← resolveAggsX E pathE aggs
    return aggregateB E.n (g.map E.idx) as (← eval E pathE x)
  | .project vs d x => do
    liftEx (checkOp (.project vs d x))
    return projectB (vs.map E.idx) d (← eval E pathE x)
  | .orderLimit keys s l x => do
    liftEx (checkOp (.orderLimit keys s l x))
    let ks ← resolveKeysX E pathE keys
    return orderLimitB E.sem.missing ks (← liftEx (countOf s)) (← liftEx (countOf l)) (← eval E pathE x)

def evalList (E : Env) (pathE : PathE) : List Op → EvM (List Bag)
  | [] => return []
  | x :: xs => do return (← eval E pathE x) :: (← evalList E pathE xs)

/-- The bags of a join's non-pattern inputs (`none` for stored patterns). -/
def evalInputs (E : Env) (pathE : PathE) : List Op → EvM (List (Option Bag))
  | [] => return []
  | x :: xs => do
    let b ← match storedPat? x, x with
      | some t, _ => do liftEx (checkOp (.triple t)); pure none
      | none, .path p => do liftEx (checkOp (.path p)); pure none
      | none, _ => do pure (some (← eval E pathE x))
    return b :: (← evalInputs E pathE xs)

def resolveX (E : Env) (pathE : PathE) : Expr → EvM RExpr
  | .var v => return (if E.vars.contains v then .var (E.idx v) else .err)
  | .const v => return .const v.canonical
  | .param _ => return .err
  | .cmp op a b => do return .cmp op (← resolveX E pathE a) (← resolveX E pathE b)
  | .sameTerm a b => do return .sameTerm (← resolveX E pathE a) (← resolveX E pathE b)
  | .and xs => do return .and (← resolveEsX E pathE xs)
  | .or xs => do return .or (← resolveEsX E pathE xs)
  | .not a => do return .not (← resolveX E pathE a)
  | .bound v => return (if E.vars.contains v then .bound (E.idx v) else .const (.bool false))
  | .inList a xs n => do return .inList (← resolveX E pathE a) (← resolveEsX E pathE xs) n
  | .arith op a b => do return .arith op (← resolveX E pathE a) (← resolveX E pathE b)
  | .neg a => do return .neg (← resolveX E pathE a)
  | .coalesce xs => do return .coalesce (← resolveEsX E pathE xs)
  | .ite c a b => do return .ite (← resolveX E pathE c) (← resolveX E pathE a) (← resolveX E pathE b)
  | .func f args => do
    liftEx (checkExpr (.func f args))
    if f == .regex || f == .replace then
      throw (.unsupported s!"{f.name} (arrives with the SPARQL front end)")
    return .func f (← resolveEsX E pathE args)
  | .exists q n => do return .exists (← eval E pathE q) n

def resolveEsX (E : Env) (pathE : PathE) : List Expr → EvM (List RExpr)
  | [] => return []
  | x :: xs => do return (← resolveX E pathE x) :: (← resolveEsX E pathE xs)

def resolveOptX (E : Env) (pathE : PathE) : Option Expr → EvM (Option RExpr)
  | none => return none
  | some e => do return some (← resolveX E pathE e)

def resolveAggsX (E : Env) (pathE : PathE) :
    List (Var × AggFunc × Option Expr × Bool) → EvM (List (Nat × AggFunc × Option RExpr × Bool))
  | [] => return []
  | (v, f, a, d) :: rest => do
    let a' ← match a with
      | some e => do pure (some (← resolveX E pathE e))
      | none => pure none
    return (E.idx v, f, a', d) :: (← resolveAggsX E pathE rest)

def resolveKeysX (E : Env) (pathE : PathE) :
    List (Expr × Bool) → EvM (List (RExpr × Bool))
  | [] => return []
  | (e, d) :: rest => do return (← resolveX E pathE e, d) :: (← resolveKeysX E pathE rest)

end

end Tiramemsu.Exec

namespace Tiramemsu.Exec

open Tiramemsu.IR Tiramemsu.Sem

/-- Path patterns before the path engine is wired in. -/
def noPaths : PathE := fun _ _ _ => throw (.unsupported "path patterns")

/-- Prepares and evaluates a query: the prepared form (columns, variable table) and the bag. -/
def evalQueryWith (pathE : PathE) (ps : Params) (q : Query)
    (counts : Codec.Value → Option Nat := fun _ => none) : EvM (Prepared × Bag) := do
  let p ← liftEx (prepare ps q)
  return (p, ← eval { p.env {} with predCount := counts } pathE p.root)

end Tiramemsu.Exec
