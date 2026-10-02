/-
The path engine and path patterns.

- `run`: compiles the expression (before any store read), resolves the view, the mentioned
  IRIs, the wildcard's relationship view and the graph set, and searches from a start node.
- Path patterns: evaluated from the start when it is bound (by a constant or the outer row),
  else from the end with the inverse expression (rows reversed, paths read start to end), else
  `Unsupported("path needs a bound endpoint")`. A `Var(?g)` selector evaluates once per graph
  with a visible membership in the view. Without a hop bound, `TRAIL` uses `pathMaxHops`.
- The reference semantics and the evaluator share this engine: the reference semantics runs it
  on the model state (`denotePath`), the evaluator as a read program (`evalPath`).
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Path.Search
import Tiramemsu.Path.Syntax

namespace Tiramemsu.Path

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Exec Tiramemsu.Sem
open Tiramemsu.Engine (RProg ROp)

--# @lat: [[query#Paths#Path Patterns]]

/-- Engine options (Rust `PathOptions`). -/
structure PathOpts where
  maxHops : Nat := 15
  maxStates : Nat := 1000000
  deriving Repr, Inhabited

/-- A path evaluation request (Rust `PathRequest`). -/
structure Request where
  start : Int64
  expr : PathExpr
  mode : PathMode := .reach
  maxHops : Option Nat := none
  view : View.ViewSpec := {}
  /-- `none`: no graph set; `some gs`: graph ids. -/
  graphs : Option (List Int64) := none
  /-- `none`: not time-respecting; `some after` (`none` after: −∞). -/
  timed : Option (Option Int) := none
  deriving Inhabited

/-- The IRIs the alphabet mentions. -/
def Dfa.iris (d : Dfa) : List String :=
  (d.alpha.toList.filterMap fun l => match l with | .pred iri _ _ => some iri | _ => none).eraseDups

/-- Whether the alphabet needs the relationship view. -/
def Dfa.needsRv (d : Dfa) : Bool :=
  d.alpha.toList.any fun l => match l with | .other _ => true | .pred _ _ (some _) => true | _ => false

/-- Runs a request. -/
def run (opts : PathOpts) (req : Request) : EvM (List PathRow) := do
  let dfa ← liftEx (buildDfa (toRE false req.expr))
  let view ← resolveViewE req.view
  let ids ← dfa.iris.filterMapM fun iri => do return (← lookupE (.iri iri)).map (iri, ·)
  let rv ← if dfa.needsRv then loadRv view else pure {}
  let graphs ← match req.graphs with
    | none => pure none
    | some gs => do pure (some (← lookupE (.iri Engine.Vocab.sysInGraph), gs.eraseDups))
  let c : Ctx := { view, dfa, ids, rv, graphs, maxHops := req.maxHops, limit := opts.maxStates,
                   timed := req.timed }
  search c req.mode req.start

/-! ## The database vocabulary -/

/-- Reads `@vocab` and the declared prefixes (`sys:db`, `sys:vocab`, `sys:prefix`) under `Now`. -/
def loadVocab : EvM Path.Vocab := do
  let some db ← lookupE (.iri (Engine.Vocab.sys ++ "db")) | return {}
  let iriOf (x : Int64) : EvM (Option String) := do
    match ← liftR (Term.decode (m := RProg) ⟨x⟩) with
    | .ok (.iri s) => return some s
    | _ => return none
  let strOf' (x : Int64) : EvM (Option String) := do
    match ← liftR (Term.decode (m := RProg) ⟨x⟩) with
    | .ok (.str s) => return some s
    | _ => return none
  let now : Store.View := {}
  let vocabIri ← match ← lookupE (.iri (Engine.Vocab.sys ++ "vocab")) with
    | none => pure none
    | some p => do
      let rows ← liftR (rangeScan .spo now [db, p])
      let rows := rows.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt)
      let vs ← rows.filterMapM fun r => iriOf r.o
      pure vs.getLast?
  let prefixes ← do
    match ← lookupE (.iri (Engine.Vocab.sys ++ "prefix")), ← lookupE (.iri (Engine.Vocab.sys ++ "prefixName")),
        ← lookupE (.iri (Engine.Vocab.sys ++ "prefixIri")) with
    | some pp, some pn, some pi => do
      let rows ← liftR (rangeScan .spo now [db, pp])
      let rows := rows.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt)
      rows.filterMapM fun r => do
        let names ← liftR (rangeScan .spo now [r.o, pn])
        let iris ← liftR (rangeScan .spo now [r.o, pi])
        let first (xs : List TripleRow) := (xs.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt)).head?
        match first names, first iris with
        | some n, some i => do
          match ← strOf' n.o, ← iriOf i.o with
          | some n, some i => return some (n, i)
          | _, _ => return none
        | _, _ => return none
    | _, _, _ => pure []
  return { vocab := vocabIri.getD Engine.Vocab.v, prefixes }

/-- Parses path text, reading the vocabulary only when the text needs it. -/
def parseText (text : String) : EvM PathExpr := do
  let raw ← liftEx (parseRaw text)
  let vc ← if raw.needsVocab then loadVocab else pure {}
  liftEx (raw.resolve vc)

/-! ## Path values as text -/

def jsonEscape (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else if c == '\r' then acc ++ "\\r" else if c == '\t' then acc ++ "\\t"
    else if c.toNat < 0x20 then acc ++ "\\u00" ++ String.ofList [hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
    else acc.push c) "" ++ "\""

/-- The self-describing text of a path value (Rust's decoded `path_json`): nodes and statements
in their lexical forms, virtual hops by their `sys:` IRI. -/
def pathText (p : PathValue) : EvM String := do
  let nodes ← p.nodes.mapM fun n => do return jsonEscape (← decodeE n).lexical
  let edges ← p.hops.mapM fun h => do
    let eid := (← decodeE h.eid).lexical
    let pred ← match virtualPredIri? h.pred with
      | some iri => pure iri
      | none => do pure (← decodeE h.pred).lexical
    return "{\"eid\":" ++ jsonEscape eid ++ ",\"p\":" ++ jsonEscape pred ++ ",\"dir\":\"" ++
      (if h.dir == .out then "out" else "in") ++ "\"}"
  return "{\"nodes\":[" ++ ",".intercalate nodes ++ "],\"edges\":[" ++ ",".intercalate edges ++ "]}"

/-! ## Path patterns -/

/-- The value of an endpoint under a row: bound (a value), or unbound. -/
def endpoint (E : Env) (a : Row) : TermOrVar → EvM (Option Value)
  | .var v => return a.get (E.idx v)
  | .const c => return some c.canonical
  | .id o => do return some (← decodeE o.raw)
  | .param _ => return none

/-- The pattern rows of one engine row. -/
def patternRow (E : Env) (p : PathPattern) (r : PathRow) (g : Option (Var × Value)) : EvM (Option Row) := do
  let mut row := Row.empty E.n
  for (t, x) in [(p.start, r.start), (p.end, r.end)] do
    match t with
    | .var v =>
      match bindVal E v (← decodeE x) row with
      | some row' => row := row'
      | none => return none
    | _ => pure ()
  if let some bv := p.bindPath then
    if let some pv := r.path then
      row := row.setAt (E.idx bv) (some (.str (← pathText pv)))
  if let some (gv, gval) := g then
    match bindVal E gv gval row with
    | some row' => row := row'
    | none => return none
  return some row

/-- The graphs with a visible membership in a view. -/
def graphsOfView (v : Store.View) : EvM (List Int64) := do
  match ← lookupE (.iri Engine.Vocab.sysInGraph) with
  | none => return []
  | some ig =>
    let ms ← liftR (rangeScan .pos v [ig])
    return (ms.map (·.o)).eraseDups.mergeSort fun a b => decide (a.toInt ≤ b.toInt)

/-- The pattern rows of a path pattern under an outer row. -/
def evalPath (opts : PathOpts) : PathE := fun E p a => do
  let s? ← endpoint E a p.start
  let e? ← endpoint E a p.end
  -- an endpoint value that is not stored has no statement: only the zero-hop match remains
  let unknown? : Option Value ← match s?, e? with
    | some s, _ => do pure (if (← lookupE s).isNone then some s else none)
    | none, some e => do pure (if (← lookupE e).isNone then some e else none)
    | none, none => pure none
  if let some val := unknown? then
    if !(toRE false p.path).norm.nullable then return []
    if let (some s, some e) := (s?, e?) then
      if s != e then return []
    let graphs ← match p.graph with
      | .var gv => do
        let gs ← graphsOfView (← resolveViewE p.view)
        gs.mapM fun g => do pure (some (gv, ← decodeE g))
      | _ => pure [none]
    return graphs.filterMap fun g => Id.run do
      let mut row := Row.empty E.n
      for t in [p.start, p.end] do
        if let .var v := t then
          match bindVal E v val row with
          | some r => row := r
          | none => return none
      if let some bv := p.bindPath then
        if p.mode.returnsPath then
          row := row.setAt (E.idx bv) (some (.str ("{\"nodes\":[" ++ jsonEscape val.lexical ++ "],\"edges\":[]}")))
      if let some (gv, gval) := g then
        match bindVal E gv gval row with
        | some r => row := r
        | none => return none
      return some row
  let maxHops := match p.maxHops with
    | some h => some h
    | none => if p.mode == .trail then some opts.maxHops else none
  let one (graphs : Option (List Int64)) : EvM (List PathRow) := do
    match s?, e? with
    | some s, _ => do
      match ← lookupE s with
      | none => return []
      | some sid =>
        let rows ← run opts { start := sid, expr := p.path, mode := p.mode, maxHops, view := p.view, graphs }
        match e? with
        | some e => do
          match ← lookupE e with
          | some eid => return rows.filter (·.end == eid)
          | none => return []
        | none => return rows
    | none, some e => do
      match ← lookupE e with
      | none => return []
      | some eid =>
        let rows ← run opts { start := eid, expr := .inv p.path, mode := p.mode, maxHops, view := p.view, graphs }
        return rows.map fun r => { r with start := r.end, «end» := r.start, path := r.path.map PathValue.reversed }
    | none, none => throw (.unsupported "path needs a bound endpoint")
  match p.graph with
  | .any => do
    let rows ← one none
    return (← rows.filterMapM fun r => patternRow E p r none)
  | .set gs => do
    let ids ← gs.filterMapM fun g => match g with
      | .const c => lookupE c.canonical
      | .id o => pure (some o.raw)
      | _ => pure none
    let rows ← one (some ids)
    return (← rows.filterMapM fun r => patternRow E p r none)
  | .var gv => do
    let v ← resolveViewE p.view
    let gs ← graphsOfView v
    let parts ← gs.mapM fun g => do
      let rows ← one (some [g])
      let gval ← decodeE g
      rows.filterMapM fun r => patternRow E p r (some (gv, gval))
    return parts.flatten

/-- The reference semantics of path patterns: the engine run on the model state. -/
def denotePath (opts : PathOpts) : PathSem := fun E p a =>
  match (evalPath opts E p a).run.onModel E.st with
  | .ok (.ok b) => .ok b
  | .ok (.error e) => .error (match e with
    | .unsupported m => .unsupported m
    | .parse d lo hi m => .parse d lo hi m
    | .pathLimitExceeded l => .pathLimitExceeded l
    | .invalidTerm m => .invalidTerm m
    | .store e => .store e
    | .invalidQuery m => .unsupported m)
  | .error e => .error (.store e)

end Tiramemsu.Path

namespace Tiramemsu

open Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Exec

/-- The reference semantics of a query, with the path engine. -/
def Query.denote (opts : Path.PathOpts) (st : Store.ModelState) (ps : Params) (q : Query) : Except QError Bag :=
  denoteWith (Path.denotePath opts) st ps q

/-- The evaluator of a query, with the path engine. -/
def Query.eval (opts : Path.PathOpts) (ps : Params) (q : Query) (counts : Codec.Value → Option Nat := fun _ => none) :
    EvM (Prepared × Bag) :=
  evalQueryWith (Path.evalPath opts) ps q counts

end Tiramemsu
