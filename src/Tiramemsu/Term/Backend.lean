/-
The term dictionary on a store: the access a store gives the dictionary algorithms, and the
algorithms themselves (`internKey`, `intern`, `lookupValue`, `decode`), the same as those of
the pure `Dict`, over any backend.

- `TermReader`: the coalesced lookup and the by-id read (snapshot readers and the engine's
  read programs need only these).
- `TermBackend`: adds the insert and the `next_term` counter (the writer).

The model-store instances live here; the SQLite instances and the caches are in
`Tiramemsu.Term.Cache` (shell). Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Term.Dict
import Tiramemsu.Store.Model

namespace Tiramemsu.Term

open Tiramemsu.Codec Tiramemsu.Store

--# @lat: [[codec#Term Dictionary#Caches And SQLite]]

/-- Dictionary reads a store provides. -/
class TermReader (m : Type → Type) where
  lookupKey : TermKey → m (Option Nat)
  rowById : Nat → m (Option Row)

/-- Dictionary access of a writer. -/
class TermBackend (m : Type → Type) extends TermReader m where
  insertRow : Row → m Unit
  nextTerm : m Nat
  setNextTerm : Nat → m Unit

/-- A `term` table row as a dictionary row. -/
def Row.ofStore (r : TermRow) : Option Row := do
  let t ← Tag.ofNat? r.tag.toNatClampNeg
  pure ⟨r.id.toNatClampNeg, t, r.lex, r.dt, r.lang, r.num⟩

/-- The id of a key in a model state (coalesced comparison, as the `term_key` index). -/
def modelLookupKey (st : ModelState) (k : TermKey) : Option Nat :=
  (st.terms.find? fun r => (Row.ofStore r).any (·.key.equiv k)).map (·.id.toNatClampNeg)

/-- The row of an id in a model state. -/
def modelRowById (st : ModelState) (i : Nat) : Option Row :=
  (st.termById i.toInt64).bind Row.ofStore

/-! ## The model store -/

instance : TermBackend ModelM where
  lookupKey k := ModelM.read fun st => modelLookupKey st k
  rowById i := ModelM.read fun st => modelRowById st i
  insertRow r := WriteStore.insertTerm r.toStore
  nextTerm := do return ((← ReadStore.counter (m := ModelM) "next_term").getD 1).toNatClampNeg
  setNextTerm n := WriteStore.setCounter (m := ModelM) "next_term" n.toInt64

instance : TermReader SnapM where
  lookupKey k := fun st => .ok (modelLookupKey st k)
  rowById i := fun st => .ok (modelRowById st i)

/-! ## The algorithms, over any backend -/

section
variable {m : Type → Type} [Monad m]

/-- Lookup-or-insert of a key (`IdSpaceExhausted TERM` past `2^60 − 1`). -/
def internKey [TermBackend m] (k : TermKey) (num : Option UInt64) : m (Except CodecError Nat) := do
  match ← TermReader.lookupKey (m := m) k with
  | some i => pure (.ok i)
  | none =>
    let next ← TermBackend.nextTerm (m := m)
    if next ≤ termIdMax then
      TermBackend.insertRow ⟨next, k.tag, k.lex, k.dt, k.lang, num⟩
      TermBackend.setNextTerm (next + 1)
      pure (.ok next)
    else pure (.error (.idSpaceExhausted .term))

/-- Encodes a value on the write path, interning its datatype IRI first, then the term. -/
def intern [TermBackend m] (v : Value) : m (Except CodecError ObjectId) := do
  match encode v with
  | .error e => pure (.error e)
  | .ok (.inline x) => pure (.ok x)
  | .ok (.term t) =>
    let dt : Except CodecError (Option Int64) ← match t.datatype with
      | none => pure (Except.ok none)
      | some iri => do
        match ← internKey (m := m) ⟨.iri, iri, none, none⟩ none with
        | .ok j => pure (Except.ok (some (termId .iri j).raw))
        | .error e => pure (Except.error e)
    match dt with
    | .error e => pure (.error e)
    | .ok dt =>
      match ← internKey ⟨t.tag, t.lex, dt, t.lang⟩ t.num with
      | .ok i => pure (.ok (termId t.tag i))
      | .error e => pure (.error e)

/-- Encodes a value for a read: lookups only. -/
def lookupValue [TermReader m] (v : Value) : m (Except CodecError (Option ObjectId)) := do
  match encode v with
  | .error e => pure (.error e)
  | .ok (.inline x) => pure (.ok (some x))
  | .ok (.term t) =>
    let dt? ← match t.datatype with
      | none => pure (some none)
      | some iri => do
        pure ((← TermReader.lookupKey (m := m) ⟨.iri, iri, none, none⟩).map fun j => some (termId .iri j).raw)
    match dt? with
    | none => pure (.ok none)
    | some dt => pure (.ok ((← TermReader.lookupKey (m := m) ⟨t.tag, t.lex, dt, t.lang⟩).map (termId t.tag)))

/-- Decodes an id (dictionary ids from their row). -/
def decode [TermReader m] (x : ObjectId) : m (Except CodecError Value) := do
  match decodeInline x with
  | .error e => pure (.error e)
  | .ok (some v) => pure (.ok v)
  | .ok none =>
    match x.tag with
    | .error e => pure (.error e)
    | .ok t =>
      let bad : CodecError := .invalidTerm s!"unknown term id {x.raw.toInt}"
      match ← TermReader.rowById (m := m) x.upayload.toNat with
      | none => pure (.error bad)
      | some r =>
        if r.tag != t then pure (.error bad)
        else
          let dt ← match r.dt with
            | none => pure none
            | some raw =>
              let y : ObjectId := ⟨raw⟩
              if y.tagBits == Tag.iri.toUInt64 then do
                match ← TermReader.rowById (m := m) y.upayload.toNat with
                | some d => pure (if d.tag == .iri then some d.lex else none)
                | none => pure none
              else pure none
          pure (valueFromTerm r.tag r.lex dt r.lang)

end

end Tiramemsu.Term
