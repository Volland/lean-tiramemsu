/-
The memory verbs (Rust's `engine/ops.rs`): assert (with `Return`/`Confirm`), create,
transaction metadata, confirm, upsert, retract, retract-matching, new node and new blank node;
and the volatile side table (`engine/volatile.rs`).
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Pipeline

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Memory Verbs]]

namespace EngM

/-- Records that this transaction corroborates live statement `e`: asserts
`(e sys:confirmedBy tx)` and returns its eid. -/
def confirm (e : ObjectId) : EngM ObjectId := do
  originOk e
  if (← live e) != some true then fail (.notLive e)
  let p ← sys Vocab.sysConfirmedBy
  let o ← txId
  return (← write e p o Valid.always true .engine).eid

/-- Asserts `(s, p, o)` idempotently; `Existing` returns the smallest live overlapping match. -/
def assertStmt (s p o : ObjectId) (opts : AssertOpts) : EngM Asserted := do
  let s ← idIn s
  let p ← idIn p
  let o ← idIn o
  let r ← write s p o opts.valid true .user
  if let .existing e := r then
    report fun x => { x with existing := x.existing.push e }
    if opts.onExisting == .confirm then
      let _ ← confirm e
  pure r

/-- Always inserts a new statement (parallel edges); schema checks still apply. -/
def create (s p o : ObjectId) (valid : Valid) : EngM ObjectId := do
  let s ← idIn s
  let p ← idIn p
  let o ← idIn o
  return (← write s p o valid false .user).eid

/-- Asserts a metadata statement about this transaction: `(tx p o)`. -/
def metadata (p o : ObjectId) : EngM ObjectId := do
  return (← assertStmt (← txId) p o {}).eid

/-- A fresh `NODE` id (no statement). -/
def newNode : EngM ObjectId := do codec .value (← op (.alloc .node))

/-- A fresh `BNODE` id (no statement). -/
def newBNode : EngM ObjectId := do codec .value (← op (.alloc .bnode))

/-- For a `sys:unique` predicate: the live subject holding `o` (smallest eid), or a new node
with `(node p o)` asserted. -/
def upsert (p o : ObjectId) : EngM ObjectId := do
  let p ← idIn p
  let o ← idIn o
  if (← tagOf p) != .iri then fail (.invalidTerm .predicate "predicate must be an IRI")
  checkKnown p .predicate
  if !(← schema p).unique then fail (.notUniquePredicate p)
  let rows ← rd (.scan { family := .livePos, pre := #[p.raw, o.raw] })
  match (byEid rows).head? with
  | some r => pure ⟨r.s⟩
  | none =>
    let node ← newNode
    let _ ← assertStmt node p o {}
    pure node

/-- Retracts a live statement with cascade; `false` for a retracted or unknown eid. -/
def retract (e : ObjectId) : EngM Bool := retractRoot e .explicit

/-- Retracts every statement live now that matches the bound positions (valid time ignored),
in ascending eid order, and returns the matched eids. -/
def retractMatching (s p o : Option ObjectId) : EngM (List ObjectId) := do
  for x in [s, p, o] do
    if let some v := x then
      let _ ← tagOf v
      originOk v
  let rows ← reads (View.triplesIn {} s p o)
  let matched := rows.map fun r => (⟨r.eid⟩ : ObjectId)
  for e in matched do
    let _ ← retractRoot e .explicit
  pure matched

/-! ## Volatile state -/

def volatileKey (s key : ObjectId) : EngM Unit := do
  if !(← tagOf s).isSubject then
    fail (.invalidTerm .subject "volatile subject must be subject-capable")
  if (← tagOf key) != .iri then fail (.invalidTerm .key "volatile key must be an IRI")
  checkKnown s .subject
  checkKnown key .key

/-- Upserts the volatile value of `(s, key)`, with `updated_at` this transaction's instant. -/
def setVolatile (s key value : ObjectId) : EngM Unit := do
  let s ← idIn s
  let key ← idIn key
  let value ← idIn value
  volatileKey s key
  checkKnown value .value
  op (.volPut { s := s.raw, key := key.raw, value := value.raw, updatedAt := (← get).instant })

/-- Removes the volatile value of `(s, key)`; succeeds when there is none. -/
def clearVolatile (s key : ObjectId) : EngM Unit := do
  let s ← idIn s
  let key ← idIn key
  volatileKey s key
  op (.volDel s.raw key.raw)

end EngM

end Tiramemsu.Engine
