/-
Path hops and search.

- Hops: the neighbours of a node for one letter class, read through the sorted range scans of
  the path's view (stored hops forward and inverse, the wildcard over relationship statements,
  virtual hops between a statement and its parts), confined to a graph set when one is given.
- Search: breadth-first over `(node, DFA state)` layers. Every new search state is charged to
  the `pathMaxStates` budget; exceeding it fails with `PathLimitExceeded` and never truncates.
  Each loop runs on explicit fuel `pathMaxStates + 1`: a layer is non-empty only when the
  previous one charged a new state, so the fuel is never the reason a search stops.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Std.Data.HashSet
import Tiramemsu.Path.Automaton
import Tiramemsu.Exec.Eval

namespace Tiramemsu.Path

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Exec
open Tiramemsu.Engine (RProg ROp)

--# @lat: [[query#Paths#Search]]

/-- The predicate id of a virtual hop in a path value (a reserved IRI id outside the
dictionary, as Rust: `2^59 + kind`). -/
def virtualPredId (k : VKind) : Int64 := (ObjectId.ofPayload .iri (((1 : UInt64) <<< 59) + k.code.toUInt64)).raw

def virtualPredIri? (x : Int64) : Option String :=
  if x == virtualPredId .subject then some QVocab.sysSubject
  else if x == virtualPredId .object then some QVocab.sysObject
  else if x == virtualPredId .predicate then some QVocab.sysPredicate
  else none

/-- One hop of a path. `kind` 0 is stored, 1–3 the virtual hops. -/
structure Hop where
  eid : Int64
  pred : Int64
  dir : Dir
  kind : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A hop's identity: the eid and the kind (a stored hop is the same in both directions). -/
def Hop.identity (h : Hop) : Int64 × Nat := (h.eid, h.kind)

/-- The order of hops: eid, then stored before virtual, then forward before inverse. -/
def Hop.key (h : Hop) : Int × Nat × Nat := (h.eid.toInt, h.kind, h.dir.code)

def keyLt (a b : Int × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

def keyLe (a b : Int × Nat × Nat) : Bool := !keyLt b a

/-- A neighbour: the hop and the node it reaches, with the statement's valid interval. -/
structure Nb where
  hop : Hop
  to : Int64
  vFrom : Option Int64
  vTo : Option Int64
  deriving Repr, Inhabited

/-- The time after a hop (`none` time is −∞): a stored hop needs `v_to` unbounded or later than
`τ` and moves `τ` to `max(τ, v_from)`; a virtual hop keeps `τ`. `none` result: not allowed. -/
def stepTime (nb : Nb) (tau : Option Int) : Option (Option Int) :=
  if nb.hop.kind != 0 then some tau
  else
    match nb.vTo, tau with
    | some t, some τ => if t.toInt ≤ τ then none else some (some (max τ (nb.vFrom.map (·.toInt) |>.getD τ)))
    | _, _ => some (match nb.vFrom, tau with
      | some f, some τ => some (max τ f.toInt)
      | some f, none => some f.toInt
      | none, τ => τ)

/-- A path value: `hops + 1` nodes and the hops. -/
structure PathValue where
  nodes : List Int64
  hops : List Hop
  deriving Repr, DecidableEq, Inhabited

def PathValue.reversed (p : PathValue) : PathValue :=
  { nodes := p.nodes.reverse, hops := p.hops.reverse.map fun h => { h with dir := h.dir.flip } }

/-- One result row. -/
structure PathRow where
  start : Int64
  «end» : Int64
  hops : Nat
  path : Option PathValue := none
  /-- `none`: not time-respecting, or −∞. -/
  arrival : Option Int := none
  deriving Repr, DecidableEq, Inhabited

/-! ## The relationship view of the wildcard -/

/-- What the wildcard needs: the `sys:isEdge` flags of the view and `rdf:type`. -/
structure Rv where
  edgeTrue : List Int64 := []
  edgeFalse : List Int64 := []
  rdfType : Option Int64 := none
  deriving Inhabited

/-- The evaluation context of one search. -/
structure Ctx where
  view : Store.View
  dfa : Dfa
  /-- Dictionary ids of the mentioned IRIs (by IRI). -/
  ids : List (String × Int64)
  rv : Rv
  /-- The graph set as ids with the `sys:inGraph` id, if graph-scoped. -/
  graphs : Option (Option Int64 × List Int64)
  maxHops : Option Nat
  limit : Nat
  timed : Option (Option Int)

def Ctx.idOf (c : Ctx) (iri : String) : Option Int64 := (c.ids.find? (·.1 == iri)).map (·.2)

/-- Whether a predicate id is a `sys:` IRI. -/
def isSysPred (p : Int64) : EvM Bool := do
  match ← liftR (Term.decode (m := RProg) ⟨p⟩) with
  | .ok (.iri s) => return s.startsWith Engine.Vocab.sys
  | _ => return false

/-- Rust's relationship view: not `rdf:type`, not `sys:`, not flagged `sys:isEdge false`; flagged
`sys:isEdge true` or with a subject-capable object. -/
def Rv.passes (rv : Rv) (p o : Int64) : EvM Bool := do
  if some p == rv.rdfType || rv.edgeFalse.contains p then return false
  if ← isSysPred p then return false
  if rv.edgeTrue.contains p then return true
  match (ObjectId.mk o).tag with
  | .ok t => return t.isSubject
  | .error _ => return false

/-- Loads the `sys:isEdge` flags of a view (the latest flag statement in eid order wins). -/
def loadRv (v : Store.View) : EvM Rv := do
  let rdfType ← lookupE (.iri Engine.Vocab.rdfType)
  match ← lookupE (.iri Engine.Vocab.sysIsEdge) with
  | none => return { rdfType }
  | some ie =>
    let rows ← liftR (rangeScan .pos v [ie])
    let rows := rows.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt)
    let yes := (ObjectId.ofPayload .bool 1).raw
    let no := (ObjectId.ofPayload .bool 0).raw
    let (t, f) := rows.foldl (fun (acc : List Int64 × List Int64) r =>
      let t := acc.1.filter (· != r.s)
      let f := acc.2.filter (· != r.s)
      if r.o == yes then (r.s :: t, f) else if r.o == no then (t, r.s :: f) else (t, f)) ([], [])
    return { edgeTrue := t, edgeFalse := f, rdfType }

/-! ## Hops -/

/-- Whether a statement may be traversed under the graph scope. -/
def inScope (c : Ctx) (eid : Int64) : EvM Bool := do
  match c.graphs with
  | none => return true
  | some (none, _) => return false
  | some (some ig, gs) =>
    let ms ← liftR (rangeScan .spo c.view [eid, ig])
    return ms.any fun m => gs.contains m.o

/-- The mentioned predicate ids of a direction (the wildcard's other letter excludes them). -/
def mentioned (c : Ctx) (d : Dir) : List Int64 :=
  c.dfa.alpha.toList.filterMap fun l => match l with
    | .pred iri d' _ => if d' == d then c.idOf iri else none
    | _ => none

def storedNb (d : Dir) (x : Int64) (r : TripleRow) : Nb :=
  { hop := { eid := r.eid, pred := r.p, dir := d, kind := 0 }, to := if d == .out then r.o else r.s,
    vFrom := r.vFrom, vTo := r.vTo }

def VKind.part (k : VKind) (r : TripleRow) : Int64 :=
  match k with | .subject => r.s | .object => r.o | .predicate => r.p

/-- The neighbours of a node for one letter class. -/
def fetchClass (c : Ctx) (lc : LClass) (x : Int64) : EvM (List Nb) := do
  let nbs ← match lc with
    | .pred iri d rel =>
      match c.idOf iri with
      | none => pure []
      | some p => do
        let rows ← liftR (match d with
          | .out => rangeScan .spo c.view [x, p]
          | .inn => rangeScan .pos c.view [p, x])
        let rows ← match rel with
          | none => pure rows
          | some want => rows.filterM fun r => do
            return (← c.rv.passes r.p (if d == .out then r.o else x)) == want
        pure (rows.map (storedNb d x))
    | .other d => do
      let rows ← liftR (match d with
        | .out => rangeScan .spo c.view [x]
        | .inn => rangeScan .osp c.view [x])
      let excl := mentioned c d
      let rows ← rows.filterM fun r => do
        if excl.contains r.p then return false
        c.rv.passes r.p (if d == .out then r.o else x)
      pure (rows.map (storedNb d x))
    | .virt k .out => do
      if (ObjectId.mk x).tagBits != Tag.stmt.toUInt64 then pure []
      else
        match ← liftR (lookupEid c.view x) with
        | none => pure []
        | some r => pure [{ hop := { eid := x, pred := virtualPredId k, dir := .out, kind := k.code },
                            to := k.part r, vFrom := r.vFrom, vTo := r.vTo }]
    | .virt k .inn => do
      let rows ← liftR (match k with
        | .subject => rangeScan .spo c.view [x]
        | .object => rangeScan .osp c.view [x]
        | .predicate => rangeScan .pos c.view [x])
      pure (rows.map fun r => { hop := { eid := r.eid, pred := virtualPredId k, dir := .inn, kind := k.code },
                                to := r.eid, vFrom := r.vFrom, vTo := r.vTo })
  nbs.filterM fun nb => inScope c nb.hop.eid

/-- The sorted transitions of one search state: each neighbour with its target state. -/
def expandOne (c : Ctx) (node : Int64) (q : Nat) : EvM (List (Nb × Nat)) := do
  let parts ← (c.dfa.trans.getD q []).mapM fun (ci, t) => do
    let nbs ← fetchClass c (c.dfa.alpha.getD ci (.other .out)) node
    return nbs.map (·, t)
  return parts.flatten.mergeSort fun a b => keyLe a.1.hop.key b.1.hop.key

/-- Charges new search states to the budget. -/
def charge (c : Ctx) (used n : Nat) : EvM Nat :=
  if used + n > c.limit then throw (.pathLimitExceeded c.limit) else return used + n

def Ctx.depthOk (c : Ctx) (depth : Nat) : Bool := c.maxHops.all (depth < ·)

def arrivalOf (c : Ctx) (tau : Option Int) : Option Int := if c.timed.isSome then tau else none

/-! ## REACH -/

/-- One BFS layer of REACH: the new pairs and the newly reached accepting ends. -/
def reachLayer (c : Ctx) (frontier : List (Int64 × Nat)) (visited : Std.HashSet (Int64 × Nat))
    (emitted : Std.HashSet Int64) (used : Nat) :
    EvM (List (Int64 × Nat) × Std.HashSet (Int64 × Nat) × Std.HashSet Int64 × List Int64 × Nat) := do
  let exps ← frontier.mapM fun (n, q) => expandOne c n q
  exps.flatten.foldlM (fun (acc : List (Int64 × Nat) × Std.HashSet (Int64 × Nat) × Std.HashSet Int64 × List Int64 × Nat) (nb, t) => do
    let (next, visited, emitted, ends, used) := acc
    if visited.contains (nb.to, t) then return acc
    let used ← charge c used 1
    let visited := visited.insert (nb.to, t)
    let next := next ++ [(nb.to, t)]
    if c.dfa.accepts t && !emitted.contains nb.to then
      return (next, visited, emitted.insert nb.to, ends ++ [nb.to], used)
    else return (next, visited, emitted, ends, used)) ([], visited, emitted, [], used)

def reachLoop (c : Ctx) (start : Int64) :
    Nat → List (Int64 × Nat) → Std.HashSet (Int64 × Nat) → Std.HashSet Int64 → Nat → Nat → List PathRow →
      EvM (List PathRow)
  | 0, _, _, _, _, _, rows => return rows
  | fuel + 1, frontier, visited, emitted, depth, used, rows => do
    if frontier.isEmpty || !c.depthOk depth then return rows
    let (next, visited, emitted, ends, used) ← reachLayer c frontier visited emitted used
    let ends := ends.mergeSort fun a b => decide (a.toInt ≤ b.toInt)
    let rows := rows ++ ends.map fun e => { start, «end» := e, hops := depth + 1 }
    reachLoop c start fuel next visited emitted (depth + 1) used rows

def reach (c : Ctx) (start : Int64) : EvM (List PathRow) := do
  let used ← charge c 0 1
  let q0 := 0
  let zero := if c.dfa.accepts q0 then [{ start, «end» := start, hops := 0 : PathRow }] else []
  let emitted : Std.HashSet Int64 := if c.dfa.accepts q0 then (∅ : Std.HashSet Int64).insert start else ∅
  reachLoop c start (c.limit + 1) [(start, q0)] ((∅ : Std.HashSet (Int64 × Nat)).insert (start, q0))
    emitted 0 used zero

/-! ## Time-respecting REACH (label correcting, earliest arrival) -/

def better (a : Option Int) (b : Option Int) : Bool :=
  match a, b with
  | none, none => false
  | none, some _ => true
  | some _, none => false
  | some x, some y => x < y

def tmin (a b : Option Int) : Option Int := if better b a then b else a

def reachTimedLoop (c : Ctx) :
    Nat → List (Int64 × Nat × Option Int) → Std.HashMap (Int64 × Nat) (Option Int) →
      Std.HashMap Int64 (Nat × Option Int) → Nat → Nat → EvM (Std.HashMap Int64 (Nat × Option Int))
  | 0, _, _, ends, _, _ => return ends
  | fuel + 1, frontier, best, ends, depth, used => do
    if frontier.isEmpty || !c.depthOk depth then return ends
    let exps ← frontier.mapM fun (n, q, tau) => do return ((← expandOne c n q).map (·, tau))
    let (next, best, ends, used) ← exps.flatten.foldlM (fun
        (acc : List (Int64 × Nat × Option Int) × Std.HashMap (Int64 × Nat) (Option Int) × Std.HashMap Int64 (Nat × Option Int) × Nat)
        ((nb, t), tau) => do
      let (next, best, ends, used) := acc
      match stepTime nb tau with
      | none => return acc
      | some at_ =>
        if (best.get? (nb.to, t)).any (fun b => !better at_ b) then return acc
        let used ← charge c used 1
        let best := best.insert (nb.to, t) at_
        let next := match next.findIdx? (fun e => e.1 == nb.to && e.2.1 == t) with
          | some i => next.set i (nb.to, t, at_)
          | none => next ++ [(nb.to, t, at_)]
        let ends := if c.dfa.accepts t then
            match ends.get? nb.to with
            | some (h, a) => ends.insert nb.to (h, tmin a at_)
            | none => ends.insert nb.to (depth + 1, at_)
          else ends
        return (next, best, ends, used)) ([], best, ends, used)
    reachTimedLoop c fuel next best ends (depth + 1) used

def reachTimed (c : Ctx) (start : Int64) (tau0 : Option Int) : EvM (List PathRow) := do
  let used ← charge c 0 1
  let ends : Std.HashMap Int64 (Nat × Option Int) := if c.dfa.accepts 0 then (∅ : Std.HashMap _ _).insert start (0, tau0) else ∅
  let ends ← reachTimedLoop c (c.limit + 1) [(start, 0, tau0)] ((∅ : Std.HashMap _ _).insert (start, 0) tau0) ends 0 used
  let rows := ends.toList.map fun (e, h, a) => ({ start, «end» := e, hops := h, arrival := a } : PathRow)
  return rows.mergeSort fun a b => decide (a.hops < b.hops ∨ (a.hops = b.hops ∧ a.end.toInt ≤ b.end.toInt))

/-! ## TRAIL -/

/-- A node of the trail arena: its parent, the hop into it and its time. -/
structure TNode where
  node : Int64
  state : Nat
  parent : Option Nat
  hop : Option Hop
  tau : Option Int
  deriving Inhabited

/-- Whether a hop identity is on the chain from `at` to the root. -/
def onChain (arena : Array TNode) (ident : Int64 × Nat) : Nat → Option Nat → Bool
  | 0, _ => false
  | _, none => false
  | fuel + 1, some i =>
    let n := arena.getD i default
    (n.hop.any fun h => h.identity == ident) || onChain arena ident fuel n.parent

/-- The steps (hop, node reached) from the root to `at`. -/
def stepsOf (arena : Array TNode) : Nat → Option Nat → List (Hop × Int64) → List (Hop × Int64)
  | 0, _, acc => acc
  | _, none, acc => acc
  | fuel + 1, some i, acc =>
    let n := arena.getD i default
    stepsOf arena fuel n.parent (match n.hop with | some h => (h, n.node) :: acc | none => acc)

def rowOf (c : Ctx) (start : Int64) (steps : List (Hop × Int64)) (tau : Option Int) : PathRow :=
  { start, «end» := (steps.getLast?.map (·.2)).getD start, hops := steps.length,
    path := some { nodes := start :: steps.map (·.2), hops := steps.map (·.1) },
    arrival := arrivalOf c tau }

def trailLoop (c : Ctx) (start : Int64) :
    Nat → Array TNode → Nat → Nat → Nat → Nat → List PathRow → EvM (List PathRow)
  | 0, _, _, _, _, _, rows => return rows
  | fuel + 1, arena, lo, hi, depth, used, rows => do
    if lo ≥ hi || !c.depthOk depth then return rows
    let mut arena := arena
    let mut used := used
    for i in [lo:hi] do
      let n := arena.getD i default
      for (nb, t) in ← expandOne c n.node n.state do
        let tau? := match c.timed with
          | none => some n.tau
          | some _ => stepTime nb n.tau
        if let some tau := tau? then
          if !onChain arena nb.hop.identity (arena.size + 1) (some i) then
            used ← charge c used 1
            arena := arena.push { node := nb.to, state := t, parent := some i, hop := some nb.hop, tau }
    let newRows := (List.range (arena.size - hi)).filterMap fun k =>
      let n := arena.getD (hi + k) default
      if c.dfa.accepts n.state then some (rowOf c start (stepsOf arena (arena.size + 1) (some (hi + k)) []) n.tau)
      else none
    trailLoop c start fuel arena hi arena.size (depth + 1) used (rows ++ newRows)

def trail (c : Ctx) (start : Int64) : EvM (List PathRow) := do
  let tau0 := c.timed.getD none
  let used ← charge c 0 1
  let zero := if c.dfa.accepts 0 then [rowOf c start [] tau0] else []
  trailLoop c start (c.limit + 1) #[{ node := start, state := 0, parent := none, hop := none, tau := tau0 }] 0 1 0 used zero

/-! ## ANY_SHORTEST and ALL_SHORTEST -/

/-- A node of the shortest-path arena with its layered predecessors. -/
structure SNode where
  node : Int64
  state : Nat
  depth : Nat
  tau : Option Int
  preds : List (Nat × Hop)
  deriving Inhabited

/-- Every path into an arena node, along its predecessors (fuel: the node's depth + 1). -/
def pathsTo (arena : Array SNode) : Nat → Nat → List (List (Hop × Int64))
  | 0, _ => []
  | fuel + 1, i =>
    let n := arena.getD i default
    if n.preds.isEmpty then [[]]
    else n.preds.flatMap fun (p, h) => (pathsTo arena fuel p).map (· ++ [(h, n.node)])

def hopKeys (steps : List (Hop × Int64)) : List (Int × Nat × Nat) := steps.map (·.1.key)

def keysLe : List (Int × Nat × Nat) → List (Int × Nat × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if keyLt a b then true else if keyLt b a then false else keysLe as bs

def shortestLoop (c : Ctx) (start : Int64) (all : Bool) :
    Nat → Array SNode → Std.HashMap (Int64 × Nat) Nat → Std.HashMap (Int64 × Nat) (Option Int) →
      Std.HashSet Int64 → List Nat → Nat → Nat → List PathRow → EvM (List PathRow)
  | 0, _, _, _, _, _, _, _, rows => return rows
  | fuel + 1, arena, index, best, emitted, layer, depth, used, rows => do
    if layer.isEmpty || !c.depthOk depth then return rows
    let mut arena := arena
    let mut index := index
    let mut used := used
    let mut next : List Nat := []
    -- timed searches key the layer by (node, state, time); untimed by (node, state)
    let mut tindex : Std.HashMap (Int64 × Nat × Option Int) Nat := ∅
    for parent in layer do
      let pn := arena.getD parent default
      for (nb, t) in ← expandOne c pn.node pn.state do
        match c.timed with
        | none =>
          match index.get? (nb.to, t) with
          | none =>
            used ← charge c used 1
            index := index.insert (nb.to, t) arena.size
            next := next ++ [arena.size]
            arena := arena.push { node := nb.to, state := t, depth := depth + 1, tau := none, preds := [(parent, nb.hop)] }
          | some j =>
            if all && (arena.getD j default).depth == depth + 1 then
              used ← charge c used 1
              arena := arena.modify j fun n => { n with preds := n.preds ++ [(parent, nb.hop)] }
        | some _ =>
          match stepTime nb pn.tau with
          | none => pure ()
          | some at_ =>
            if !(best.get? (nb.to, t)).any (fun b => !better at_ b) then
              match tindex.get? (nb.to, t, at_) with
              | none =>
                used ← charge c used 1
                tindex := tindex.insert (nb.to, t, at_) arena.size
                next := next ++ [arena.size]
                arena := arena.push { node := nb.to, state := t, depth := depth + 1, tau := at_, preds := [(parent, nb.hop)] }
              | some j =>
                if all then
                  used ← charge c used 1
                  arena := arena.modify j fun n => { n with preds := n.preds ++ [(parent, nb.hop)] }
    let best := next.foldl (fun b i =>
      let n := arena.getD i default
      match b.get? (n.node, n.state) with
      | some x => b.insert (n.node, n.state) (tmin x n.tau)
      | none => b.insert (n.node, n.state) n.tau) best
    let targets := next.filter fun i =>
      let n := arena.getD i default
      c.dfa.accepts n.state && !emitted.contains n.node
    let mut found : List (List (Hop × Int64) × Option Int) := []
    if all then
      for i in targets do
        let n := arena.getD i default
        for p in pathsTo arena (depth + 2) i do
          used ← charge c used 1
          found := found ++ [(p, n.tau)]
      found := found.mergeSort fun a b => keysLe (hopKeys a.1) (hopKeys b.1)
    else
      let mut seen : Std.HashSet Int64 := ∅
      for i in targets do
        let n := arena.getD i default
        if !seen.contains n.node then
          seen := seen.insert n.node
          match pathsTo arena (depth + 2) i with
          | p :: _ => found := found ++ [(p, n.tau)]
          | [] => pure ()
    let emitted := targets.foldl (fun e i => e.insert (arena.getD i default).node) emitted
    let rows := rows ++ found.map fun (p, tau) => rowOf c start p tau
    shortestLoop c start all fuel arena index best emitted next (depth + 1) used rows

def shortest (c : Ctx) (start : Int64) (all : Bool) : EvM (List PathRow) := do
  let tau0 := c.timed.getD none
  let used ← charge c 0 1
  let zero := if c.dfa.accepts 0 then [rowOf c start [] tau0] else []
  let emitted : Std.HashSet Int64 := if c.dfa.accepts 0 then (∅ : Std.HashSet Int64).insert start else ∅
  shortestLoop c start all (c.limit + 1)
    #[{ node := start, state := 0, depth := 0, tau := tau0, preds := [] }]
    ((∅ : Std.HashMap (Int64 × Nat) Nat).insert (start, 0) 0)
    ((∅ : Std.HashMap (Int64 × Nat) (Option Int)).insert (start, 0) tau0)
    emitted [0] 0 used zero

/-- Runs one search mode from a start node. -/
def search (c : Ctx) (mode : PathMode) (start : Int64) : EvM (List PathRow) :=
  match mode, c.timed with
  | .reach, none => reach c start
  | .reach, some tau => reachTimed c start tau
  | .trail, _ => trail c start
  | .anyShortest, _ => shortest c start false
  | .allShortest, _ => shortest c start true

end Tiramemsu.Path
