/-
Engine helpers shared by the verbs, following Rust's `Tx` methods: interning and looking up
engine IRIs, the IRI of an id, position and term checks, liveness, the recorded insert (with
multi-eid bookkeeping) and the recorded retraction (statements and memberships apart).
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.View.Read

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Write Pipeline]]

namespace EngM

/-- Lookup-or-insert of a dictionary key. -/
def internKey (k : TermKey) (num : Option UInt64) (pos : Position := .value) : EngM Nat := do
  codec pos (← op (.intern k num))

/-- Encodes a value, interning it (its datatype IRI first) when it needs the dictionary. -/
def internValue (v : Value) (pos : Position := .value) : EngM ObjectId := do
  match encode v with
  | .error e => fail (Error.ofCodec pos e)
  | .ok (.inline x) => pure x
  | .ok (.term t) =>
    let dt ← match t.datatype with
      | none => pure none
      | some iri => do
        let j ← internKey ⟨.iri, iri, none, none⟩ none pos
        pure (some (termId .iri j).raw)
    let i ← internKey ⟨t.tag, t.lex, dt, t.lang⟩ t.num pos
    pure (termId t.tag i)

/-- The id of an engine IRI, interning it. -/
def sys (iri : String) : EngM ObjectId := do
  let i ← internKey ⟨.iri, iri, none, none⟩ none
  pure (termId .iri i)

/-- The id of an engine IRI, if it is interned. -/
def sysLookup (iri : String) : EngM (Option ObjectId) := reads (View.iriId iri)

/-- The text of an `IRI` id. -/
def iriOf (x : ObjectId) : EngM (Option String) := do
  if x.tagBits != Tag.iri.toUInt64 then return none
  match ← rd (.rowById x.upayload.toNat) with
  | some r => pure (if r.tag == .iri then some r.lex else none)
  | none => pure none

/-- The tag of an id. -/
def tagOf (x : ObjectId) (pos : Position := .value) : EngM Tag := codec pos x.tag

/-- Rejects an allocated id with a non-zero origin. -/
def originOk (x : ObjectId) : EngM Unit := codec .value (checkOrigin x)

/-- An id accepted in a statement position (Rust's `IntoObject for ObjectId`). -/
def idIn (x : ObjectId) : EngM ObjectId := do
  let _ ← tagOf x
  originOk x
  pure x

/-- Checks that a dictionary id names an existing term of its tag. -/
def checkKnown (x : ObjectId) (pos : Position) : EngM Unit := do
  let t ← tagOf x pos
  if t.isDictionary then
    let ok := match ← rd (.rowById x.upayload.toNat) with
      | some r => r.tag == t
      | none => false
    if !ok then fail (.invalidTerm pos s!"unknown term id {x.raw}")

/-- Validates the kinds of a statement's positions. -/
def checkPositions (s p o : ObjectId) : EngM Unit := do
  let st ← tagOf s .subject
  let pt ← tagOf p .predicate
  let _ ← tagOf o .object
  for x in [s, p, o] do originOk x
  if !st.isSubject then fail (.invalidTerm .subject s!"{st.name} cannot be a subject")
  if pt != .iri then fail (.invalidTerm .predicate s!"{pt.name} cannot be a predicate")
  checkKnown s .subject
  checkKnown p .predicate
  checkKnown o .object

/-- `some true` live, `some false` retracted, `none` unknown. -/
def live (e : ObjectId) : EngM (Option Bool) := do
  return (← rd (.triple e.raw)).map (·.tRet.isNone)

/-- Whether a statement is a graph membership (its predicate is `sys:inGraph`). -/
def isMembership (e : ObjectId) : EngM Bool := do
  match ← sysLookup Vocab.sysInGraph with
  | none => pure false
  | some ig => return (← rd (.triple e.raw)).any (·.p == ig.raw)

/-- Inserts one statement row (checked by the operation's guard) and records it: listed as
asserted, and its predicate marked multi-eid when another row has the same triple. -/
def insertRow (eid s p o : ObjectId) (valid : Valid) : EngM Unit := do
  op (.insert { eid := eid.raw, s := s.raw, p := p.raw, o := o.raw, vFrom := valid.vFrom, vTo := valid.vTo })
  report fun r => { r with asserted := r.asserted.push eid }
  let same ← rd (.scan { family := .histSpo, pre := #[s.raw, p.raw, o.raw], view := { tx := .history } })
  if same.any (·.eid != eid.raw) then op (.markMulti p.raw)

/-- Retracts a live row with a kind and records it; `false` when it was not live. -/
def retractRow (e : ObjectId) (k : RetKind) : EngM Bool := do
  let done ← op (.retract e.raw k)
  if done then
    if ← isMembership e then report fun r => { r with membershipsRetracted := r.membershipsRetracted.push (e, k) }
    else report fun r => { r with retracted := r.retracted.push (e, k) }
  pure done

/-- Allocates a fresh statement id. -/
def allocEid : EngM ObjectId := do codec .value (← op (.alloc .stmt))

/-- The `TX` id of this transaction. -/
def txId : EngM ObjectId := do return mkAlloc .tx 0 (← get).t.toUInt64

end EngM

end Tiramemsu.Engine
