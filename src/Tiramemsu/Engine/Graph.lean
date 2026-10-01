/-
Named-graph membership verbs (Rust's `engine/graph.rs`): a graph is an `IRI`, `NODE` or
`BNODE`; a membership is the engine-written statement `(e sys:inGraph g)`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Verbs

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Named Graphs]]

namespace EngM

/-- The rendered form of a graph id, for error messages. -/
def renderGraph (g : ObjectId) : EngM String := do
  match ← reads (decode g) with
  | .ok v => pure v.lexical
  | .error _ => pure s!"{g.raw}"

/-- Validates a graph name: an `IRI`, `NODE` or `BNODE` id. -/
def graphId (g : ObjectId) : EngM ObjectId := do
  let g ← idIn g
  match ← tagOf g with
  | .iri | .node | .bnode =>
    checkKnown g .object
    pure g
  | _ => fail (.invalidGraphName (← renderGraph g))

/-- The live memberships `(m, e, sys:inGraph, g)`, optionally of one statement, by eid. -/
def liveMemberships (e : Option ObjectId) (ig g : ObjectId) : EngM (List ObjectId) := do
  let rows ← rd (.scan { family := .livePos, pre := #[ig.raw, g.raw] })
  let rows := rows.filter fun r => e.all (·.raw == r.s)
  pure ((byEid rows).map (⟨·.eid⟩))

/-- Adds live statement `e` to `g` idempotently over `opts.valid`; returns the membership eid
and whether it is new. -/
def addToGraph (e g : ObjectId) (opts : AssertOpts) : EngM (ObjectId × Bool) := do
  originOk e
  let g ← graphId g
  let some row ← rd (.triple e.raw) | fail (.notLive e)
  if row.tRet.isSome then fail (.notLive e)
  let pIri := (← iriOf ⟨row.p⟩).getD ""
  if pIri.startsWith Vocab.sys || pIri.startsWith Vocab.tm then fail (.reservedNamespace pIri)
  let ig ← sys Vocab.sysInGraph
  let r ← write e ig g opts.valid true .engine
  if r.isNew then
    report fun x => { x with asserted := x.asserted.filter (· != r.eid),
                             memberships := x.memberships.push r.eid }
  pure (r.eid, r.isNew)

/-- Retracts the live memberships of `e` in `g`; `e` stays live. -/
def removeFromGraph (e g : ObjectId) : EngM Bool := do
  originOk e
  let g ← graphId g
  let some ig ← sysLookup Vocab.sysInGraph | return false
  let ms ← liveMemberships (some e) ig g
  for m in ms do
    let _ ← retractRoot m .explicit
  pure !ms.isEmpty

/-- Retracts every live membership in `g`; member statements stay live. -/
def clearGraph (g : ObjectId) : EngM (List ObjectId) := do
  let g ← graphId g
  let some ig ← sysLookup Vocab.sysInGraph | return []
  let ms ← liveMemberships none ig g
  for m in ms do
    let _ ← retractRoot m .explicit
  pure ms

/-- Declares `g`: asserts `(g rdf:type sys:Graph)` idempotently. -/
def createGraph (g : ObjectId) : EngM Asserted := do
  let g ← graphId g
  let ty ← sys Vocab.rdfType
  let cls ← sys Vocab.sysGraph
  let r ← write g ty cls Valid.always true .user
  if let .existing e := r then report fun x => { x with existing := x.existing.push e }
  pure r

/-- Clears `g` and retracts its declaration; returns the retracted roots, memberships first. -/
def dropGraph (g : ObjectId) : EngM (List ObjectId) := do
  let g ← graphId g
  let out ← clearGraph g
  match ← sysLookup Vocab.rdfType, ← sysLookup Vocab.sysGraph with
  | some ty, some cls => return out ++ (← retractMatching (some g) (some ty) (some cls))
  | _, _ => pure out

end EngM

end Tiramemsu.Engine
