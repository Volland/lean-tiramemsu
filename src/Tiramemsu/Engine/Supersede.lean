/-
Supersede: correct a live statement by cascade-and-replay (Rust's `engine/supersede.rs`).

The cascade set `C` of the root is computed once; fresh eids `σ` are allocated for `C` in
cascade order; every member of `C` is retracted with kind `supersede`; uniqueness and
cardinality one run for the new root content; every member that is not a graph membership is
replayed under `σ` (subject and object rewritten through `σ`, the patch applied to the root
only); finally the link `(σ root, sys:supersedes, root)` is inserted.

Listed deviation: a replay whose rewritten subject or object equals its own new eid (possible
only when a statement refers to an eid not issued yet) fails with `SelfReference`, where Rust
checks only the root's object.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Pipeline

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Supersede]]

/-- The substitution of a supersede: old eid to new eid, in cascade order. -/
abbrev Sigma := List (Int64 × Int64)

/-- A raw id through `σ` (identity outside the cascade set). -/
def Sigma.apply (σ : Sigma) (x : Int64) : Int64 :=
  match σ.find? (·.1 == x) with
  | some (_, y) => y
  | none => x

/-- The replay of one member of the cascade set: new eid, rewritten subject and object, the
patched object and interval for the root. -/
def replayRow (σ : Sigma) (root : Int64) (newO : Int64) (newValid : Valid) (r : TripleRow) : NewRow :=
  if r.eid == root then
    { eid := σ.apply r.eid, s := σ.apply r.s, p := r.p, o := newO,
      vFrom := newValid.vFrom, vTo := newValid.vTo }
  else
    { eid := σ.apply r.eid, s := σ.apply r.s, p := r.p, o := σ.apply r.o,
      vFrom := r.vFrom, vTo := r.vTo }

namespace EngM

/-- Supersedes live statement `root` with `patch` and returns the new root eid. -/
def supersede (root : ObjectId) (patch : Patch) : EngM ObjectId := do
  originOk root
  let row ← match ← rd (.triple root.raw) with
    | some r => if r.tRet.isNone then pure r else fail (.notLive root)
    | none => fail (.notLive root)
  let newO ← match patch.o with
    | some v => internValue v
    | none => pure ⟨row.o⟩
  let newValid : Valid := { vFrom := patch.vFrom.getD row.vFrom, vTo := patch.vTo.getD row.vTo }
  if !newValid.nonempty then fail (.invalidPatch "empty interval")
  if newO.raw == row.o && newValid == ⟨row.vFrom, row.vTo⟩ then fail (.invalidPatch "no change")
  let s : ObjectId := ⟨row.s⟩
  let p : ObjectId := ⟨row.p⟩
  -- the new root content is a user write
  checkPositions s p newO
  let pIri := (← iriOf p).getD ""
  ofExcept (checkReserved pIri (← tagOf s))
  let flag := Flag.ofIri pIri
  match flag with
  | some f =>
    validateFlag f p s newO
    validateSchemaChange f s newO (some root)
  | none => checkValueType p newO
  let set ← cascadeSet root
  let mut σ : Sigma := []
  for m in set do
    let e ← allocEid
    σ := σ ++ [(m.raw, e.raw)]
  let newRoot : ObjectId := ⟨σ.apply root.raw⟩
  if newO == newRoot then fail (.selfReference newRoot)
  let mut rows := []
  for m in set do
    match ← rd (.triple m.raw) with
    | some r => rows := rows ++ [r]
    | none => throw (.store (.misuse "cascade member vanished"))
  for m in set do
    let _ ← retractRow m .supersede
  uniqueAndCardinality s p newO newValid (flag.any Flag.singleValued)
  let inGraph ← sysLookup Vocab.sysInGraph
  for r in rows do
    if inGraph.any (·.raw == r.p) then continue
    let n := replayRow σ root.raw newO.raw newValid r
    if n.s == n.eid || n.o == n.eid then fail (.selfReference ⟨n.eid⟩)
    insertRow ⟨n.eid⟩ ⟨n.s⟩ ⟨n.p⟩ ⟨n.o⟩ ⟨n.vFrom, n.vTo⟩
    report fun x => { x with superseded := x.superseded.push (⟨r.eid⟩, ⟨n.eid⟩) }
  let linkP ← sys Vocab.sysSupersedes
  let link ← allocEid
  insertRow link newRoot linkP root Valid.always
  pure newRoot

end EngM

end Tiramemsu.Engine
