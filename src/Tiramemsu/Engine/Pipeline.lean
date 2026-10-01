/-
The write pipeline and the retraction cascade (Rust's `engine/ops.rs` `write`,
`unique_and_cardinality`, `find_overlapping` and `engine/cascade.rs`).

Order of the pipeline: positions, reserved namespace (user writes), interval, flag validation
and schema-change check (flag predicates) or value type then subject type, idempotency (assert
only), uniqueness, cardinality-one replacement, eid allocation, self-reference, insert.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Schema

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Write Pipeline]]

/-- Who is writing: user writes are checked against the reserved namespaces. -/
inductive Writer where
  | user
  | engine
  deriving Repr, DecidableEq, Inhabited

namespace EngM

/-- The cascade set of a live root: the root, then breadth-first every live statement whose
subject or object was reached; `CascadeLimitExceeded` past `max_cascade`. -/
def cascadeSet (root : ObjectId) : EngM (List ObjectId) := do
  let limit := (← get).opts.maxCascade
  let fuel ← reads walkFuel
  match ← reads (walk (neighbors {}) (some limit) root.raw fuel) with
  | .done order => pure (order.toList.map (⟨·⟩))
  | .exceeded => fail (.cascadeLimitExceeded root limit)
  | .outOfFuel => throw (.store (.misuse "cascade walk ran out of fuel"))

/-- Retracts a live root and its cascade set: the root gets `kind`, the rest `cascade` for an
explicit retraction and `kind` otherwise. `false` when the root is not live. -/
def retractRoot (root : ObjectId) (kind : RetKind) : EngM Bool := do
  originOk root
  if (← live root) != some true then return false
  validateFlagRetraction root
  let set ← cascadeSet root
  let mut first := true
  for e in set do
    let k := if first || kind != .explicit then kind else .cascade
    first := false
    let _ ← retractRow e k
  pure true

/-- Live rows of `(s, p)` other than object `o` whose interval overlaps `valid`, by eid. -/
def overlappingOthers (s p o : ObjectId) (valid : Valid) : EngM (List TripleRow) := do
  let rows ← liveOfSP s p
  pure (byEid (rows.filter fun r => r.o != o.raw && Valid.overlaps ⟨r.vFrom, r.vTo⟩ valid))

/-- The uniqueness check, then cardinality-one replacement, for a statement about to be
inserted. Single-valued flag predicates are implicitly `one`, valid time ignored. -/
def uniqueAndCardinality (s p o : ObjectId) (valid : Valid) (isFlag : Bool) : EngM Unit := do
  let sc ← if isFlag then pure ({ one := true } : PredicateSchema) else schema p
  if sc.unique then
    let rows ← rd (.scan { family := .livePos, pre := #[p.raw, o.raw] })
    if let some r := rows.find? (·.s != s.raw) then fail (.uniqueViolation p o ⟨r.s⟩)
  if sc.one then
    let v := if isFlag then Valid.always else valid
    for r in ← overlappingOthers s p o v do
      let _ ← retractRoot ⟨r.eid⟩ .cardinality

/-- The smallest live eid with the same triple and an overlapping interval. -/
def findOverlapping (s p o : ObjectId) (valid : Valid) : EngM (Option ObjectId) := do
  let rows ← rd (.scan { family := .liveSpo, pre := #[s.raw, p.raw, o.raw] })
  pure ((byEid (rows.filter fun r => Valid.overlaps ⟨r.vFrom, r.vTo⟩ valid)).head?.map (⟨·.eid⟩))

/-- The pre-insert pipeline shared by assert, create, confirm, metadata and memberships. -/
def write (s p o : ObjectId) (valid : Valid) (idempotent : Bool) (w : Writer) : EngM Asserted := do
  checkPositions s p o
  let pIri := (← iriOf p).getD ""
  if w == .user then ofExcept (checkReserved pIri (← tagOf s))
  ofExcept valid.check
  let flag := Flag.ofIri pIri
  match flag with
  | some f =>
    validateFlag f p s o
    validateSchemaChange f s o none
  | none =>
    checkValueType p o
    checkSubjectType p s
  if idempotent then
    if let some e ← findOverlapping s p o valid then return .existing e
  uniqueAndCardinality s p o valid (flag.any Flag.singleValued)
  let eid ← allocEid
  if s == eid || o == eid then fail (.selfReference eid)
  insertRow eid s p o valid
  pure (.new eid)

end EngM

end Tiramemsu.Engine
