/-
The reference semantics `denote`: what rows a query means on a model store state. Total and
computable, so it is both the specification of every execution path and the test oracle.

- Each pattern reads the statements visible in its own view and compares decoded values, so a
  constant that is not stored matches nothing without any dictionary lookup.
- Under `SetOfTriples` without an eid variable a pattern yields the set of its rows (one per
  distinct visible `(s, p, o)`); otherwise one row per statement (per membership for
  `Var(?g)`).
- Virtual predicates are computed from statement rows; a variable predicate never sees them.
  Under `AsOf(t)` a statement retracted after `t` reports no retraction (its row is masked as
  the view reads show it), so a past view never changes after later commits.
- Every node runs its local validation rule first (`checkOp`/`checkExpr`), so a validated
  query never fails with `InvalidQuery`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Sem.Ops
import Tiramemsu.IR.Validate

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Store


--# @lat: [[query#Reference Semantics]]

/-- The environment of one evaluation. -/
structure Env where
  st : ModelState
  sem : Semantics
  vars : List Var
  /-- Match groups: `(group, eid column)` of every grouped pattern (relationship isomorphism). -/
  iso : List (Nat × Nat) := []
  /-- Per-predicate statement counts for join ordering (statistics: they change only speed). -/
  predCount : Value → Option Nat := fun _ => none

namespace Env

def n (E : Env) : Nat := E.vars.length
def idx (E : Env) (v : Var) : Nat := E.vars.idxOf v

/-- The schema (possible variables) of an operator. -/
def schemaOf (E : Env) (op : Op) : Schema := let s := scope op; E.vars.map s.binds

end Env

/-! ## Store reads on a model state -/

/-- The store view of a view spec (an instant resolves to the last transaction at or before it). -/
def resolveView (st : ModelState) (v : View.ViewSpec) : Store.View :=
  match v.tx with
  | .now => { tx := .now, valid := v.valid }
  | .history => { tx := .history, valid := v.valid }
  | .asOf (.tx t) => { tx := .asOf t, valid := v.valid }
  | .asOf (.instant ms) => { tx := .asOf ((st.txAtOrBefore ms).map (·.t) |>.getD 0), valid := v.valid }

/-- The statements a view selects, in store order. -/
def visibleRows (st : ModelState) (v : Store.View) : List TripleRow := st.triples.filter v.admits

/-- The value of an id. -/
def decodeId (st : ModelState) (x : Int64) : Except LErr Value :=
  match (Term.decode (m := SnapM) ⟨x⟩) st with
  | .ok (.ok v) => .ok v
  | .ok (.error e) => .error (.invalidTerm (toString (repr e)))
  | .error e => .error (.store e)

/-- The graphs a statement is a member of, by visible memberships of the view. -/
def membershipsOf (st : ModelState) (v : Store.View) (e : Int64) : Except LErr (List Value) := do
  let ms ← ((visibleRows st v).filter (·.s == e)).mapM fun m => do
    if (← decodeId st m.p) == .iri Engine.Vocab.sysInGraph then
      return some (← decodeId st m.o)
    else return none
  return ms.filterMap id

/-! ## Pattern positions -/

/-- Binds a variable to a value, or checks it against the value it already has. -/
def bindVal (E : Env) (v : Var) (val : Value) (r : Row) : Option Row :=
  let i := E.idx v
  match r.get i with
  | some w => if w == val then some r else none
  | none => some (r.setAt i (some val))

/-- Matches a stored position (raw id `x`) against a pattern position. -/
def matchPos (E : Env) (t : TermOrVar) (x : Int64) (r : Row) : Except LErr (Option Row) :=
  match t with
  | .var v => do return bindVal E v (← decodeId E.st x) r
  | .const c => do return if (← decodeId E.st x) == c.canonical then some r else none
  | .id o => .ok (if o.raw == x then some r else none)
  | .param _ => .ok none

/-- Matches a computed position (a value) against a pattern position. `byValue` compares a
constant by value (date-times by instant). -/
def matchVal (E : Env) (byValue : Bool) (t : TermOrVar) (val : Value) (r : Row) : Except LErr (Option Row) :=
  match t with
  | .var v => .ok (bindVal E v val r)
  | .const c => .ok (if (if byValue then valueEq val c.canonical else val == c.canonical) then some r else none)
  | .id o => do return if (← decodeId E.st o.raw) == val then some r else none
  | .param _ => .ok none

def bindOpt {α : Type} (x : Except LErr (Option α)) (f : α → Except LErr (Option α)) :
    Except LErr (Option α) := do
  match ← x with
  | some a => f a
  | none => return none

/-! ## Triple patterns -/

/-- The value of a virtual predicate on a statement row (`none`: absent). -/
def virtualValue (st : ModelState) (vp : VirtualPred) (r : TripleRow) : Except LErr (Option Value) :=
  let inst (t : Int64) : Option Value := (st.txByT t).map fun x => .dateTime x.instant.toInt (some 0)
  match vp with
  | .subject => do return some (← decodeId st r.s)
  | .predicate => do return some (← decodeId st r.p)
  | .object => do return some (← decodeId st r.o)
  | .txAdded => .ok (some (.tx r.tAdd.toInt.toNat))
  | .txRetracted => .ok (r.tRet.map fun t => .tx t.toInt.toNat)
  | .addedAt => .ok (inst r.tAdd)
  | .retractedAt => .ok (r.tRet.bind inst)
  | .validFrom => .ok (r.vFrom.map fun x => .dateTime x.toInt (some 0))
  | .validTo => .ok (r.vTo.map fun x => .dateTime x.toInt (some 0))
  | .retractKind => .ok (r.retKind.map fun k => .int k.toInt)

def _root_.Tiramemsu.IR.VirtualPred.byInstant : VirtualPred → Bool
  | .addedAt | .retractedAt | .validFrom | .validTo => true
  | _ => false

/-- The rows one statement contributes to a virtual-predicate pattern. -/
def virtualRow (E : Env) (t : TriplePattern) (vp : VirtualPred) (r : TripleRow) : Except LErr (Option Row) := do
  match ← virtualValue E.st vp r with
  | none => return none
  | some val =>
    bindOpt (matchVal E false t.s (← decodeId E.st r.eid) (Row.empty E.n)) fun row =>
      matchVal E vp.byInstant t.o val row

/-- The graph-selector expansion of a matched row. -/
def graphRows (E : Env) (v : Store.View) (g : GraphSel) (e : Int64) (row : Row) : Except LErr (List Row) :=
  match g with
  | .any => .ok [row]
  | .set gs => do
    let ms ← membershipsOf E.st v e
    let want := gs.filterMap fun t => match t with | .const c => some c.canonical | _ => none
    return if ms.any want.contains then [row] else []
  | .var gv => do
    let ms ← membershipsOf E.st v e
    return ms.filterMap fun m => bindVal E gv m row

/-- The rows one stored statement contributes to a triple pattern. -/
def storedRows (E : Env) (v : Store.View) (t : TriplePattern) (r : TripleRow) : Except LErr (List Row) := do
  let m ← bindOpt (matchPos E t.s r.s (Row.empty E.n)) fun row =>
    bindOpt (matchPos E t.p r.p row) fun row =>
      bindOpt (matchPos E t.o r.o row) fun row =>
        match t.eid with
        | some ev => do return bindVal E ev (← decodeId E.st r.eid) row
        | none => return some row
  match m with
  | none => return []
  | some row => graphRows E v t.graph r.eid row

def collectRows {α : Type} (xs : List α) (f : α → Except LErr (List Row)) : Except LErr Bag := do
  return (← xs.mapM f).flatten

/-- The bag of a triple pattern. -/
def triplePat (E : Env) (t : TriplePattern) : Except LErr Bag := do
  let v := resolveView E.st t.view
  let rows := visibleRows E.st v
  let bag ← match t.p.virtual? with
    | some vp => collectRows (rows.map (View.mask v)) fun r => do return (← virtualRow E t vp r).toList
    | none => collectRows rows (storedRows E v t)
  return if E.sem.graphSet == .setOfTriples && t.eid.isNone then bag.eraseDups else bag

/-! ## Inline values -/

def cellValue (st : ModelState) : Option TermOrVar → Except LErr (Option Value)
  | some (.const c) => .ok (some c.canonical)
  | some (.id o) => do return some (← decodeId st o.raw)
  | _ => .ok none

def valuesRow (E : Env) (vs : List Var) (cells : List (Option TermOrVar)) : Except LErr Row :=
  (vs.zip cells).foldlM (fun r (v, c) => do
    match ← cellValue E.st c with
    | some val => return r.setAt (E.idx v) (some val)
    | none => return r) (Row.empty E.n)

def valuesB (E : Env) (vs : List Var) (rows : List (List (Option TermOrVar))) : Except LErr Bag :=
  rows.mapM (valuesRow E vs)

/-- A skip or limit after binding. -/
def countOf : Option TermOrVar → Except QError (Option Nat)
  | some (.const (.int n)) => .ok (some n.toNat)
  | _ => .ok none

/-! ## The denotation -/

/-- The meaning of a path pattern under an outer row (its endpoints may be bound by the row):
the pattern rows of the path engine. Supplied by `Tiramemsu.Path.Engine`. -/
abbrev PathSem := Env → PathPattern → Row → Except LErr Bag

def pathPatStub : PathSem := fun _ _ _ => .error (.unsupported "path patterns")

def Op.pathPat? : Op → Option PathPattern
  | .path p => some p
  | _ => none

/-- Path patterns of a join, laterally: each extends every row with its compatible pattern rows
for that row's endpoint bindings, in input order. -/
def lateralPaths (E : Env) (pathB : PathSem) (P : Schema) (rows : Bag) : List PathPattern → Except LErr Bag
  | [] => .ok rows
  | p :: ps => do
    let Q := E.schemaOf (.path p)
    let parts ← rows.mapM fun a => do
      return ((← pathB E p a).filter (compat E.sem.missing P Q a)).map (merge a)
    lateralPaths E pathB (Schema.union P Q) parts.flatten ps

mutual

/-- The reference bag of an operator. -/
def denote (E : Env) (pathB : PathSem) : Op → Except QError Bag
  | .triple t => do checkOp (.triple t); liftL (triplePat E t)
  | .path p => do checkOp (.path p); liftL (pathB E p [])
  | .values vs rows => do checkOp (.values vs rows); liftL (valuesB E vs rows)
  | .join xs => do
    let bs ← denoteInputs E pathB xs
    let others := (xs.zip bs).filterMap fun (x, b) => b.map (E.schemaOf x, ·)
    let (P, rows) := joinAll E.sem.missing E.n others
    let rows ← liftL (lateralPaths E pathB P rows (xs.filterMap Op.pathPat?))
    return isoFilter E.iso rows
  | .leftJoin l r c => do
    let lb ← denote E pathB l
    let rb ← denote E pathB r
    let c' ← resolveOpt E pathB c
    return isoFilter E.iso (leftJoinB E.sem.missing (E.schemaOf l) (E.schemaOf r) c' lb rb)
  | .union xs => do return (← denoteList E pathB xs).flatten
  | .filter c x => do
    let c' ← resolveE E pathB c
    return filterB c' (← denote E pathB x)
  | .extend v e x => do
    checkOp (.extend v e x)
    let e' ← resolveE E pathB e
    return extendB (E.idx v) e' (← denote E pathB x)
  | .aggregate g aggs x => do
    checkOp (.aggregate g aggs x)
    let as ← resolveAggs E pathB aggs
    return aggregateB E.n (g.map E.idx) as (← denote E pathB x)
  | .project vs d x => do
    checkOp (.project vs d x)
    return projectB (vs.map E.idx) d (← denote E pathB x)
  | .orderLimit keys s l x => do
    checkOp (.orderLimit keys s l x)
    let ks ← resolveKeys E pathB keys
    return orderLimitB E.sem.missing ks (← countOf s) (← countOf l) (← denote E pathB x)

def denoteList (E : Env) (pathB : PathSem) : List Op → Except QError (List Bag)
  | [] => .ok []
  | x :: xs => do return (← denote E pathB x) :: (← denoteList E pathB xs)

/-- The bags of a join's inputs, `none` for path patterns (evaluated laterally). -/
def denoteInputs (E : Env) (pathB : PathSem) : List Op → Except QError (List (Option Bag))
  | [] => .ok []
  | .path p :: xs => do checkOp (.path p); return none :: (← denoteInputs E pathB xs)
  | x :: xs => do return some (← denote E pathB x) :: (← denoteInputs E pathB xs)

/-- Resolves an expression: positions for variables, bags for `EXISTS`. -/
def resolveE (E : Env) (pathB : PathSem) : Expr → Except QError RExpr
  | .var v => .ok (if E.vars.contains v then .var (E.idx v) else .err)
  | .const v => .ok (.const v.canonical)
  | .param _ => .ok .err
  | .cmp op a b => do return .cmp op (← resolveE E pathB a) (← resolveE E pathB b)
  | .sameTerm a b => do return .sameTerm (← resolveE E pathB a) (← resolveE E pathB b)
  | .and xs => do return .and (← resolveEs E pathB xs)
  | .or xs => do return .or (← resolveEs E pathB xs)
  | .not a => do return .not (← resolveE E pathB a)
  | .bound v => .ok (if E.vars.contains v then .bound (E.idx v) else .const (.bool false))
  | .inList a xs n => do return .inList (← resolveE E pathB a) (← resolveEs E pathB xs) n
  | .arith op a b => do return .arith op (← resolveE E pathB a) (← resolveE E pathB b)
  | .neg a => do return .neg (← resolveE E pathB a)
  | .coalesce xs => do return .coalesce (← resolveEs E pathB xs)
  | .ite c a b => do return .ite (← resolveE E pathB c) (← resolveE E pathB a) (← resolveE E pathB b)
  | .func f args => do
    checkExpr (.func f args)
    if f == .regex || f == .replace then
      throw (.unsupported s!"{f.name} (arrives with the SPARQL front end)")
    return .func f (← resolveEs E pathB args)
  | .exists q n => do return .exists (← denote E pathB q) n

def resolveEs (E : Env) (pathB : PathSem) : List Expr → Except QError (List RExpr)
  | [] => .ok []
  | x :: xs => do return (← resolveE E pathB x) :: (← resolveEs E pathB xs)

def resolveOpt (E : Env) (pathB : PathSem) : Option Expr → Except QError (Option RExpr)
  | none => .ok none
  | some e => do return some (← resolveE E pathB e)

def resolveAggs (E : Env) (pathB : PathSem) :
    List (Var × AggFunc × Option Expr × Bool) → Except QError (List (Nat × AggFunc × Option RExpr × Bool))
  | [] => .ok []
  | (v, f, a, d) :: rest => do
    let a' ← match a with
      | some e => do pure (some (← resolveE E pathB e))
      | none => pure none
    return (E.idx v, f, a', d) :: (← resolveAggs E pathB rest)

def resolveKeys (E : Env) (pathB : PathSem) :
    List (Expr × Bool) → Except QError (List (RExpr × Bool))
  | [] => .ok []
  | (e, d) :: rest => do return (← resolveE E pathB e, d) :: (← resolveKeys E pathB rest)

end

/-! ## Relationship isomorphism: hidden eid variables -/

mutual

/-- Gives every grouped pattern without an eid variable a hidden one (`~iso<k>`). -/
def isoOp : Op → StateM Nat Op
  | .triple t =>
    match t.isoGroup, t.eid, t.p.virtual? with
    | some _, none, none => do
      let k ← get
      set (k + 1)
      return .triple { t with eid := some s!"~iso{k}" }
    | _, _, _ => return .triple t
  | .join xs => do return .join (← isoOps xs)
  | .union xs => do return .union (← isoOps xs)
  | .leftJoin l r c => do return .leftJoin (← isoOp l) (← isoOp r) c
  | .filter c x => do return .filter c (← isoOp x)
  | .extend v e x => do return .extend v e (← isoOp x)
  | .aggregate g a x => do return .aggregate g a (← isoOp x)
  | .project vs d x => do return .project vs d (← isoOp x)
  | .orderLimit k s l x => do return .orderLimit k s l (← isoOp x)
  | o => return o

def isoOps : List Op → StateM Nat (List Op)
  | [] => return []
  | x :: xs => do return (← isoOp x) :: (← isoOps xs)

end

mutual

/-- Every grouped pattern's `(group, eid variable)`. -/
def isoPairs : Op → List (Nat × Var)
  | .triple t => match t.isoGroup, t.eid with
    | some g, some e => [(g, e)]
    | _, _ => []
  | .join xs | .union xs => isoPairsList xs
  | .leftJoin l r _ => isoPairs l ++ isoPairs r
  | .filter _ x | .extend _ _ x | .aggregate _ _ x | .project _ _ x | .orderLimit _ _ _ x => isoPairs x
  | _ => []

def isoPairsList : List Op → List (Nat × Var)
  | [] => []
  | x :: xs => isoPairs x ++ isoPairsList xs

end

/-- A query prepared for evaluation: parameters bound, hidden match-group variables added
under `RelIsomorphism`, and the variable table. -/
structure Prepared where
  root : Op
  sem : Semantics
  vars : List Var
  iso : List (Nat × Nat)
  columns : List Var

/-- Binds parameters and prepares the tables of a query. -/
def prepare (ps : Params) (q : Query) : Except QError Prepared := do
  let root ← bindOp ps q.root
  let root := if q.sem.matchMode == .relIsomorphism then (isoOp root).run' 0 else root
  -- parameters can make a tree invalid (a parameter predicate bound to a virtual one), so the
  -- prepared tree is validated again: evaluation itself never raises `InvalidQuery`
  validateOp root
  let vars := root.varTable
  let iso := if q.sem.matchMode == .relIsomorphism then
      (isoPairs root).map fun (g, e) => (g, vars.idxOf e)
    else []
  return { root, sem := q.sem, vars, iso, columns := outputVars q.root }

/-- Parameters are complete for a query when it prepares: every parameter is bound, skip and
limit are non-negative integers, and the bound tree passes validation. -/
def Complete (ps : Params) (q : Query) : Prop := ∃ p, prepare ps q = .ok p

def Prepared.env (p : Prepared) (st : ModelState) : Env :=
  { st, sem := p.sem, vars := p.vars, iso := p.iso }

/-- The reference bag of a query (rows over the variable table), with a path semantics. -/
def denoteWith (pathB : PathSem) (st : ModelState) (ps : Params)
    (q : Query) : Except QError Bag := do
  let p ← prepare ps q
  denote (p.env st) pathB p.root

/-- The columns of a result row. -/
def Prepared.project (p : Prepared) (r : Row) : List (Option Value) :=
  p.columns.map fun v => if p.vars.contains v then r.get (p.vars.idxOf v) else none

end Tiramemsu.Sem
