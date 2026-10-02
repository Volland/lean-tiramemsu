/-
Query provenance: an annotated evaluator whose rows carry the ascending, duplicate-free eids of
the stored statements that support them.

Citation rules (query-provenance "What a row cites"):
- a triple-pattern match cites its statement under `BagOfEids` or with an eid variable, and
  under `SetOfTriples` without an eid variable every visible eid with the matched `(s, p, o)`;
  with `Var(?g)` or a one-graph `Set` also the membership statement;
- `Join` cites the union of its inputs, `LeftJoin` the left row's plus the matched right row's,
  `Union` the branch taken; `Filter`, `Extend` and `EXISTS` add nothing;
- a path in `TRAIL` or a shortest mode cites every hop's statement (and, graph-scoped, the
  memberships used); `REACH`, virtual predicates and inline values cite nothing;
- a distinct projection merges equal rows with the union of their citations, an aggregate row
  cites its group, ordering keeps each row's citations.
The rows themselves are computed by the same bag operators as the plain semantics.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Path.Engine

namespace Tiramemsu.Prov

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Exec Tiramemsu.Path
open Tiramemsu.Engine (RProg ROp sortDedup)

--# @lat: [[query#Provenance]]

/-- A row with its citations. -/
abbrev ARow := Row × List Int64

/-- An annotated bag. -/
abbrev ABag := List ARow

def cite (a b : List Int64) : List Int64 := sortDedup (a ++ b)

/-- Groups annotated rows by a key in first-appearance order, uniting citations. -/
def groupCites {κ : Type} [BEq κ] (key : ARow → κ) (xs : ABag) : List (κ × ABag) :=
  let keys := (xs.map key).eraseDups
  keys.map fun k => (k, xs.filter fun r => key r == k)

def unionCites (xs : ABag) : List Int64 := sortDedup (xs.flatMap (·.2))

/-! ## Annotated bag operators -/

def joinAB (m : Missing) (P Q : Schema) (xs ys : ABag) : ABag :=
  xs.flatMap fun (a, ea) => ys.filterMap fun (b, eb) =>
    if compat m P Q a b then some (merge a b, cite ea eb) else none

def joinAllAB (m : Missing) (xs : List (Schema × ABag)) : Schema × ABag :=
  xs.foldl (fun (P, acc) (Q, ys) => (Schema.union P Q, joinAB m P Q acc ys)) ([], [([], [])])

def leftJoinAB (m : Missing) (P Q : Schema) (c : Option RExpr) (xs ys : ABag) : ABag :=
  xs.flatMap fun (a, ea) =>
    let ms := ys.filterMap fun (b, eb) =>
      if compat m P Q a b then
        let r := merge a b
        if (match c with | some e => e.holds r | none => true) then some (r, cite ea eb) else none
      else none
    if ms.isEmpty then [(a, ea)] else ms

def projectAB (keep : List Nat) (distinct : Bool) (xs : ABag) : ABag :=
  let ys := xs.map fun (r, e) => (Row.restrict keep.contains r, e)
  if distinct then (groupCites (·.1) ys).map fun (r, g) => (r, unionCites g) else ys

def aggregateAB (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool)) (xs : ABag) : ABag :=
  if g.isEmpty && xs.isEmpty then [(groupRow' n g aggs ([], []), [])]
  else (groupCites (fun r => groupKey g r.1) xs).map fun (k, grp) =>
    (groupRow' n g aggs (k, grp.map (·.1)), unionCites grp)
where
  groupRow' (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool))
      (kg : List (Option Value) × Bag) : Row :=
    aggs.foldl (fun (r : Row) (i, f, a, d) => r.set i (aggregateOne f a d kg.2))
      ((g.zip kg.1).foldl (fun (r : Row) (i, c) => r.set i c) (Row.empty n))

def orderLimitAB (m : Missing) (keys : List (RExpr × Bool)) (skip limit : Option Nat) (xs : ABag) : ABag :=
  let keyed := xs.map fun ar => (keys.map fun (e, _) => e.eval ar.1, ar)
  let sorted := (keyed.mergeSort fun a b => orderLe m (keys.map (·.2)) (a.1, a.2.1) (b.1, b.2.1)).map (·.2)
  let dropped := sorted.drop (skip.getD 0)
  match limit with
  | some l => dropped.take l
  | none => dropped

def isoFilterAB (cols : List (Nat × Nat)) (xs : ABag) : ABag :=
  if cols.isEmpty then xs else xs.filter fun r => isoOk cols r.1

/-! ## Leaves -/

/-- The memberships of a statement as `(graph, membership eid)`. -/
def membershipsProv (v : Store.View) (e : Int64) : EvM (List (Value × Int64)) := do
  match ← lookupE (.iri Engine.Vocab.sysInGraph) with
  | none => return []
  | some ig =>
    let ms ← liftR (rangeScan .spo v [e, ig])
    ms.mapM fun m => do return (← decodeE m.o, m.eid)

/-- The annotated pattern rows of one statement. -/
def patRowsProv (E : Env) (v : Store.View) (t : TriplePattern) (r : TripleRow) : EvM ABag := do
  let some row ← bindE E t.s r.s (Row.empty E.n) | return []
  let some row ← bindE E t.p r.p row | return []
  let some row ← bindE E t.o r.o row | return []
  let row? ← match t.eid with
    | some ev => do pure (bindVal E ev (← decodeE r.eid) row)
    | none => pure (some row)
  let some row := row? | return []
  match t.graph with
  | .any => return [(row, [r.eid])]
  | .set gs =>
    let want := gs.filterMap fun g => match g with | .const c => some c.canonical | _ => none
    let ms := (← membershipsProv v r.eid).filter fun (g, _) => want.contains g
    if ms.isEmpty then return []
    else return [(row, if gs.length == 1 then cite [r.eid] (ms.map (·.2)) else [r.eid])]
  | .var gv =>
    let ms ← membershipsProv v r.eid
    return ms.filterMap fun (g, me) => (bindVal E gv g row).map (·, cite [r.eid] [me])

/-- The annotated bag of a stored triple pattern (read through the constant key prefix). -/
def triplePatProv (E : Env) (t : TriplePattern) : EvM ABag := do
  let v ← resolveViewE t.view
  let rows ← candidateRows E v { t with eid := t.eid } []
  -- under SetOfTriples without an eid variable every eid of the matched content is cited:
  -- scan without the adjacent deduplication
  let rows ← if E.sem.graphSet == .setOfTriples && t.eid.isNone && t.graph == .any then do
      let some s ← posId E [] t.s | pure []
      let some p ← posId E [] t.p | pure []
      let some o ← posId E [] t.o | pure []
      let (ord, pfx) := indexFor s p o
      liftR (rangeScan ord v pfx)
    else pure rows
  let ann := (← rows.mapM (patRowsProv E v t)).flatten
  if E.sem.graphSet == .setOfTriples && t.eid.isNone then
    return (groupCites (·.1) ann).map fun (r, g) => (r, unionCites g)
  else return ann

/-- The annotated rows of a path pattern under an outer row. -/
def pathProv (opts : PathOpts) (E : Env) (p : PathPattern) (a : Row) : EvM ABag := do
  -- the plain rows, matched with the engine rows they come from
  let s? ← endpoint E a p.start
  let e? ← endpoint E a p.end
  let maxHops := match p.maxHops with
    | some h => some h
    | none => if p.mode == .trail then some opts.maxHops else none
  let graphsOf : EvM (List (Option (List Int64) × Option (Var × Value))) := match p.graph with
    | .any => pure [(none, none)]
    | .set gs => do
      let ids ← gs.filterMapM fun g => match g with
        | .const c => lookupE c.canonical
        | .id o => pure (some o.raw)
        | _ => pure none
      pure [(some ids, none)]
    | .var gv => do
      let v ← resolveViewE p.view
      let gs ← graphsOfView v
      gs.mapM fun g => do pure (some [g], some (gv, ← decodeE g))
  let v ← resolveViewE p.view
  let mut out : ABag := []
  for (graphs, gb) in ← graphsOf do
    let rows ← match s?, e? with
      | some s, _ => do
        match ← lookupE s with
        | none => pure []
        | some sid =>
          let rows ← run opts { start := sid, expr := p.path, mode := p.mode, maxHops, view := p.view, graphs }
          match e? with
          | some e => do
            match ← lookupE e with
            | some eid => pure (rows.filter (·.end == eid))
            | none => pure []
          | none => pure rows
      | none, some e => do
        match ← lookupE e with
        | none => pure []
        | some eid =>
          let rows ← run opts { start := eid, expr := .inv p.path, mode := p.mode, maxHops, view := p.view, graphs }
          pure (rows.map fun r => { r with start := r.end, «end» := r.start, path := r.path.map PathValue.reversed })
      | none, none => throw (.unsupported "path needs a bound endpoint")
    for r in rows do
      if let some row ← patternRow E p r gb then
        let hops := (r.path.map (·.hops)).getD []
        let mut es := if p.mode == .reach then [] else hops.map (·.eid)
        if p.mode != .reach then
          if let some gs := graphs then
            for h in hops do
              let ms ← membershipsProv v h.eid
              for (g, me) in ms do
                if gs.contains (← lookupE g |>.map (·.getD 0)) then es := es ++ [me]
        out := out ++ [(row, sortDedup es)]
  return out

/-! ## The annotated evaluator -/

def lateralPathsAB (E : Env) (opts : PathOpts) (P : Schema) (rows : ABag) : List PathPattern → EvM ABag
  | [] => return rows
  | p :: ps => do
    let Q := E.schemaOf (.path p)
    let parts ← rows.mapM fun (a, ea) => do
      let bs ← pathProv opts E p a
      return bs.filterMap fun (b, eb) => if compat E.sem.missing P Q a b then some (merge a b, cite ea eb) else none
    lateralPathsAB E opts (Schema.union P Q) parts.flatten ps

mutual

/-- The provenance evaluator (`EXISTS` subtrees are evaluated without provenance: tested
statements are not cited). -/
def evalProv (E : Env) (opts : PathOpts) : Op → EvM ABag
  | .triple t => do
    liftEx (checkOp (.triple t))
    match t.p.virtual? with
    | some vp => do return (← virtualPat E t vp).map (·, [])
    | none => triplePatProv E t
  | .path p => do liftEx (checkOp (.path p)); pathProv opts E p []
  | .values vs rows => do
    liftEx (checkOp (.values vs rows))
    return (← rows.mapM (valuesRowE E vs)).map (·, [])
  | .join xs => do
    let bs ← evalProvInputs E opts xs
    let others := (xs.zip bs).filterMap fun (x, b) => b.map (E.schemaOf x, ·)
    let (P, rows) := joinAllAB E.sem.missing others
    let rows ← lateralPathsAB E opts P rows (xs.filterMap Op.pathPat?)
    return isoFilterAB E.iso rows
  | .leftJoin l r c => do
    let lb ← evalProv E opts l
    let rb ← evalProv E opts r
    let c' ← resolveOptX E (Path.evalPath opts) c
    return isoFilterAB E.iso (leftJoinAB E.sem.missing (E.schemaOf l) (E.schemaOf r) c' lb rb)
  | .union xs => do return (← evalProvList E opts xs).flatten
  | .filter c x => do
    let c' ← resolveX E (Path.evalPath opts) c
    return (← evalProv E opts x).filter fun r => c'.holds r.1
  | .extend v e x => do
    liftEx (checkOp (.extend v e x))
    let e' ← resolveX E (Path.evalPath opts) e
    return (← evalProv E opts x).map fun (r, es) => (match e'.eval r with
      | some val => r.setAt (E.idx v) (some val)
      | none => r, es)
  | .aggregate g aggs x => do
    liftEx (checkOp (.aggregate g aggs x))
    let as ← resolveAggsX E (Path.evalPath opts) aggs
    return aggregateAB E.n (g.map E.idx) as (← evalProv E opts x)
  | .project vs d x => do
    liftEx (checkOp (.project vs d x))
    return projectAB (vs.map E.idx) d (← evalProv E opts x)
  | .orderLimit keys s l x => do
    liftEx (checkOp (.orderLimit keys s l x))
    let ks ← resolveKeysX E (Path.evalPath opts) keys
    return orderLimitAB E.sem.missing ks (← liftEx (countOf s)) (← liftEx (countOf l)) (← evalProv E opts x)

def evalProvList (E : Env) (opts : PathOpts) : List Op → EvM (List ABag)
  | [] => return []
  | x :: xs => do return (← evalProv E opts x) :: (← evalProvList E opts xs)

def evalProvInputs (E : Env) (opts : PathOpts) : List Op → EvM (List (Option ABag))
  | [] => return []
  | .path p :: xs => do liftEx (checkOp (.path p)); return none :: (← evalProvInputs E opts xs)
  | x :: xs => do return some (← evalProv E opts x) :: (← evalProvInputs E opts xs)

end

/-- Prepares and evaluates a query with provenance. -/
def evalQueryProv (opts : PathOpts) (ps : Params) (q : Query) : EvM (Prepared × ABag) := do
  let p ← liftEx (prepare ps q)
  return (p, ← evalProv (p.env {}) opts p.root)

end Tiramemsu.Prov
