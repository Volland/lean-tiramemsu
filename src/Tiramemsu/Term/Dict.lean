/-
The term dictionary as a pure model: rows in insertion order and the next id. Interning is
lookup-or-append with `id = next`, bounded at `2^60 − 1`; values intern their datatype IRI
first; reads only look up; decoding rebuilds the value from the row. Every law of the
dictionary is proven on this model, and `SqliteStore` is refinement-tested against it.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Term.Key

namespace Tiramemsu.Term

open Tiramemsu.Codec

--# @lat: [[codec#Term Dictionary]]

/-- The largest term id: `2^60 − 1`. -/
def termIdMax : Nat := 2 ^ 60 - 1

/-- The dictionary model. -/
structure Dict where
  rows : List Row := []
  next : Nat := 1
  deriving Repr, Inhabited

namespace Dict

/-- A fresh dictionary (`next_term` 1). -/
def empty : Dict := {}

/-- The id of a key, compared as the `term_key` index compares. -/
def lookup (d : Dict) (k : TermKey) : Option Nat :=
  (d.rows.find? fun r => r.key.equiv k).map (·.id)

/-- The row of an id. -/
def byId (d : Dict) (i : Nat) : Option Row := d.rows.find? (·.id == i)

/-- Looks a key up, appending it with `id = next` when absent; `IdSpaceExhausted TERM` when no
id is left (the dictionary is then unchanged). -/
def intern (d : Dict) (k : TermKey) (num : Option UInt64) : Except CodecError (Nat × Dict) :=
  match d.lookup k with
  | some i => .ok (i, d)
  | none =>
    if d.next ≤ termIdMax then
      .ok (d.next, { rows := d.rows ++ [⟨d.next, k.tag, k.lex, k.dt, k.lang, num⟩], next := d.next + 1 })
    else .error (.idSpaceExhausted .term)

/-- Interns a term spec: its datatype IRI first, then the term. -/
def internSpec (d : Dict) (t : TermSpec) : Except CodecError (Nat × Dict) := do
  let (dt, d1) ← match t.datatype with
    | none => pure (none, d)
    | some iri => do
      let (j, d1) ← d.intern ⟨.iri, iri, none, none⟩ none
      pure (some (termId .iri j).raw, d1)
  d1.intern ⟨t.tag, t.lex, dt, t.lang⟩ t.num

/-- Encodes a value on the write path, interning dictionary terms. -/
def internValue (d : Dict) (v : Value) : Except CodecError (ObjectId × Dict) :=
  match encode v with
  | .error e => .error e
  | .ok (.inline x) => .ok (x, d)
  | .ok (.term t) => do
    let (i, d') ← d.internSpec t
    pure (termId t.tag i, d')

/-- Encodes a value for a read: lookups only; `none` when a needed term (or its datatype IRI)
is absent. -/
def lookupValue (d : Dict) (v : Value) : Except CodecError (Option ObjectId) :=
  match encode v with
  | .error e => .error e
  | .ok (.inline x) => .ok (some x)
  | .ok (.term t) =>
    let dt? : Option (Option Int64) := match t.datatype with
      | none => some none
      | some iri => (d.lookup ⟨.iri, iri, none, none⟩).map fun j => some (termId .iri j).raw
    match dt? with
    | none => .ok none
    | some dt => .ok ((d.lookup ⟨t.tag, t.lex, dt, t.lang⟩).map (termId t.tag))

/-- The text of an `IRI` id, when it names an `IRI` row. -/
def iriText (d : Dict) (raw : Int64) : Option String :=
  let x : ObjectId := ⟨raw⟩
  if x.tagBits == Tag.iri.toUInt64 then
    match d.byId x.upayload.toNat with
    | some r => if r.tag = .iri then some r.lex else none
    | none => none
  else none

/-- Decodes an id: inline ids by the codec, dictionary ids from their row (missing row or tag
mismatch: `InvalidTerm`). -/
def decode (d : Dict) (x : ObjectId) : Except CodecError Value :=
  match decodeInline x with
  | .error e => .error e
  | .ok (some v) => .ok v
  | .ok none =>
    match x.tag with
    | .error e => .error e
    | .ok t =>
      match d.byId x.upayload.toNat with
      | some r =>
        if r.tag = t then valueFromTerm r.tag r.lex (r.dt.bind d.iriText) r.lang
        else .error (.invalidTerm s!"unknown term id {x.raw.toInt}")
      | none => .error (.invalidTerm s!"unknown term id {x.raw.toInt}")

end Dict

end Tiramemsu.Term
