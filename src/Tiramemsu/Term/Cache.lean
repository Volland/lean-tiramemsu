/-
The term dictionary on a store, and its caches (shell, unverified; refinement-tested against
the pure `Dict` model):

- `TermBackend`: the coalesced lookup, the by-id read, the insert and the `next_term` counter,
  implemented for `ModelStore` and for `SqliteStore` with the SQL of Rust's `term.rs`.
- `intern`, `lookupValue`, `decode`: the dictionary algorithms of `Dict`, over any backend.
- `WriterCache`: a committed key/id map plus a per-transaction overlay, merged on commit and
  dropped on rollback; capacity unbounded, `n` (cleared past `2n`, as Rust), or 0 (off).
- `ReaderCache`: an id → row LRU filled only from committed rows (snapshot readers).
Terms are immutable, so no cache entry is ever invalidated, only evicted.
-/
import Std.Data.HashMap
import Tiramemsu.Term.Dict
import Tiramemsu.Sqlite.Store
import Tiramemsu.Store.Model

namespace Tiramemsu.Term

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Sqlite

--# @lat: [[codec#Term Dictionary#Caches And SQLite]]

instance : Hashable TermKey where
  hash k := hash (k.tag.toNat, k.lex, k.dt.getD 0, k.lang.getD "")

/-- Keys are cached by their coalesced form. -/
abbrev CKey := Nat × String × Int64 × String

def TermKey.ckey (k : TermKey) : CKey := (k.tag.toNat, k.lex, k.dt.getD 0, k.lang.getD "")

/-- Dictionary access a store provides. -/
class TermBackend (m : Type → Type) where
  lookupKey : TermKey → m (Option Nat)
  rowById : Nat → m (Option Row)
  insertRow : Row → m Unit
  nextTerm : m Nat
  setNextTerm : Nat → m Unit

/-- A `term` table row as a dictionary row. -/
def Row.ofStore (r : TermRow) : Option Row := do
  let t ← Tag.ofNat? r.tag.toNatClampNeg
  pure ⟨r.id.toNatClampNeg, t, r.lex, r.dt, r.lang, r.num⟩

/-! ## The model store -/

instance : TermBackend ModelM where
  lookupKey k := ModelM.read fun st =>
    (st.terms.find? fun r => (Row.ofStore r).any (·.key.equiv k)).map (·.id.toNatClampNeg)
  rowById i := ModelM.read fun st => (st.termById i.toInt64).bind Row.ofStore
  insertRow r := WriteStore.insertTerm r.toStore
  nextTerm := do return ((← ReadStore.counter (m := ModelM) "next_term").getD 1).toNatClampNeg
  setNextTerm n := WriteStore.setCounter (m := ModelM) "next_term" n.toInt64

/-! ## SQLite, with Rust's `term.rs` statements -/

/-- Rust's `LOOKUP_SQL` (text bound as bytes and cast, as everywhere in `SqliteStore`). -/
def sqlLookup : String :=
  "SELECT id FROM term WHERE tag = ?1 AND lex = CAST(?2 AS TEXT) " ++
  "AND ifnull(dt, 0) = ifnull(?3, 0) AND ifnull(lang, '') = ifnull(CAST(?4 AS TEXT), '')"

/-- Rust's `BY_ID_SQL`. -/
def sqlById : String :=
  "SELECT id, tag, CAST(lex AS BLOB), dt, CAST(lang AS BLOB), num FROM term WHERE id = ?1"

def lookupOn (c : Conn) (k : TermKey) : SqlM (Option Nat) := do
  let r ← c.queryOne sqlLookup #[.int k.tag.toInt64, .text k.lex, .ofOpt k.dt, .ofOptText k.lang]
    (colInt! · 0)
  pure (r.map (·.toNatClampNeg))

def byIdOn (c : Conn) (i : Nat) : SqlM (Option Row) := do
  let r ← c.queryOne sqlById #[.int i.toInt64] readTerm
  pure (r.bind Row.ofStore)

instance : TermBackend SqliteM where
  lookupKey k := fun st => do lookupOn (← st.conn) k
  rowById i := fun st => do byIdOn (← st.conn) i
  insertRow r := WriteStore.insertTerm r.toStore
  nextTerm := do return ((← ReadStore.counter (m := SqliteM) "next_term").getD 1).toNatClampNeg
  setNextTerm n := WriteStore.setCounter (m := SqliteM) "next_term" n.toInt64

/-! ## The writer cache -/

/-- Cache capacity: `none` unbounded, `some 0` off, `some n` cleared past `2n` on commit. -/
structure WriterCache where
  capacity : Option Nat
  committed : IO.Ref (Std.HashMap CKey Nat)
  committedRev : IO.Ref (Std.HashMap Nat Row)
  overlay : IO.Ref (Std.HashMap CKey Nat)
  overlayRev : IO.Ref (Std.HashMap Nat Row)

def WriterCache.new (capacity : Option Nat) : IO WriterCache := do
  pure { capacity, committed := ← IO.mkRef {}, committedRev := ← IO.mkRef {},
         overlay := ← IO.mkRef {}, overlayRev := ← IO.mkRef {} }

def WriterCache.enabled (c : WriterCache) : Bool := c.capacity != some 0

/-- Merges the overlay into the committed cache (after `COMMIT`). -/
def WriterCache.commit (c : WriterCache) : IO Unit := do
  if !c.enabled then return
  let ov ← c.overlay.get
  let ovr ← c.overlayRev.get
  if let some n := c.capacity then
    if (← c.committed.get).size + ov.size > 2 * n then
      c.committed.set {}; c.committedRev.set {}
  c.committed.modify fun m => ov.fold (fun m k v => m.insert k v) m
  c.committedRev.modify fun m => ovr.fold (fun m k v => m.insert k v) m
  c.overlay.set {}; c.overlayRev.set {}

/-- Drops the overlay (after `ROLLBACK`). -/
def WriterCache.rollback (c : WriterCache) : IO Unit := do
  c.overlay.set {}; c.overlayRev.set {}

/-- A backend behind a writer cache. -/
abbrev CachedM (m : Type → Type) := ReaderT WriterCache m

instance {m : Type → Type} [Monad m] [MonadLiftT IO m] [TermBackend m] : TermBackend (CachedM m) where
  lookupKey k := fun c => do
    if c.enabled then
      if let some i := (← (c.overlay.get : IO _))[k.ckey]? then return some i
      if let some i := (← (c.committed.get : IO _))[k.ckey]? then return some i
    let r ← TermBackend.lookupKey k
    -- not in the overlay, so the row was committed before this transaction
    if c.enabled then if let some i := r then (c.committed.modify (·.insert k.ckey i) : IO _)
    pure r
  rowById i := fun c => do
    if c.enabled then
      if let some r := (← (c.overlayRev.get : IO _))[i]? then return some r
      if let some r := (← (c.committedRev.get : IO _))[i]? then return some r
    let r ← TermBackend.rowById i
    if c.enabled then
      if let some row := r then
        (c.committed.modify (·.insert row.key.ckey i) : IO _)
        (c.committedRev.modify (·.insert i row) : IO _)
    pure r
  insertRow r := fun c => do
    TermBackend.insertRow r
    if c.enabled then
      (c.overlay.modify (·.insert r.key.ckey r.id) : IO _)
      (c.overlayRev.modify (·.insert r.id r) : IO _)
  nextTerm := fun _ => TermBackend.nextTerm
  setNextTerm n := fun _ => TermBackend.setNextTerm n

/-! ## The algorithms, over any backend -/

section
variable {m : Type → Type} [Monad m] [TermBackend m]

/-- Lookup-or-insert of a key (`IdSpaceExhausted TERM` past `2^60 − 1`). -/
def internKey (k : TermKey) (num : Option UInt64) : m (Except CodecError Nat) := do
  match ← TermBackend.lookupKey k with
  | some i => pure (.ok i)
  | none =>
    let next ← TermBackend.nextTerm
    if next ≤ termIdMax then
      TermBackend.insertRow ⟨next, k.tag, k.lex, k.dt, k.lang, num⟩
      TermBackend.setNextTerm (next + 1)
      pure (.ok next)
    else pure (.error (.idSpaceExhausted .term))

/-- Encodes a value on the write path, interning its datatype IRI first, then the term. -/
def intern (v : Value) : m (Except CodecError ObjectId) := do
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
def lookupValue (v : Value) : m (Except CodecError (Option ObjectId)) := do
  match encode v with
  | .error e => pure (.error e)
  | .ok (.inline x) => pure (.ok (some x))
  | .ok (.term t) =>
    let dt? ← match t.datatype with
      | none => pure (some none)
      | some iri => do
        pure ((← TermBackend.lookupKey ⟨.iri, iri, none, none⟩).map fun j => some (termId .iri j).raw)
    match dt? with
    | none => pure (.ok none)
    | some dt => pure (.ok ((← TermBackend.lookupKey ⟨t.tag, t.lex, dt, t.lang⟩).map (termId t.tag)))

/-- Decodes an id (dictionary ids from their row). -/
def decode (x : ObjectId) : m (Except CodecError Value) := do
  match decodeInline x with
  | .error e => pure (.error e)
  | .ok (some v) => pure (.ok v)
  | .ok none =>
    match x.tag with
    | .error e => pure (.error e)
    | .ok t =>
      let bad : CodecError := .invalidTerm s!"unknown term id {x.raw.toInt}"
      match ← TermBackend.rowById x.upayload.toNat with
      | none => pure (.error bad)
      | some r =>
        if r.tag != t then pure (.error bad)
        else
          let dt ← match r.dt with
            | none => pure none
            | some raw =>
              let y : ObjectId := ⟨raw⟩
              if y.tagBits == Tag.iri.toUInt64 then do
                match ← TermBackend.rowById y.upayload.toNat with
                | some d => pure (if d.tag == .iri then some d.lex else none)
                | none => pure none
              else pure none
          pure (valueFromTerm r.tag r.lex dt r.lang)

end

/-! ## The reader cache -/

/-- An id → row LRU for snapshot readers; only committed rows ever reach it. -/
structure ReaderCache where
  capacity : Nat
  entries : IO.Ref (Std.HashMap Nat (Row × Nat))
  tick : IO.Ref Nat

def ReaderCache.new (capacity : Nat) : IO ReaderCache := do
  pure { capacity := max capacity 1, entries := ← IO.mkRef {}, tick := ← IO.mkRef 0 }

def ReaderCache.get (c : ReaderCache) (i : Nat) : IO (Option Row) := do
  match (← c.entries.get)[i]? with
  | some (r, _) =>
    let t ← c.tick.modifyGet fun t => (t, t + 1)
    c.entries.modify (·.insert i (r, t))
    pure (some r)
  | none => pure none

def ReaderCache.put (c : ReaderCache) (r : Row) : IO Unit := do
  let t ← c.tick.modifyGet fun t => (t, t + 1)
  let es ← c.entries.get
  let es := if es.size ≥ c.capacity then
      match es.fold (fun (acc : Option (Nat × Nat)) k (_, u) =>
          match acc with
          | some (_, best) => if u < best then some (k, u) else acc
          | none => some (k, u)) none with
      | some (k, _) => es.erase k
      | none => es
    else es
  c.entries.set (es.insert r.id (r, t))

/-- A snapshot reader behind the LRU (committed rows only). -/
instance : TermBackend (ReaderT ReaderCache ReaderM) where
  lookupKey k := fun _ conn => lookupOn conn k
  rowById i := fun c conn => do
    if let some r ← (c.get i : IO _) then return some r
    let r ← byIdOn conn i
    if let some row := r then (c.put row : IO _)
    pure r
  insertRow _ := fun _ _ => throw (.misuse "a snapshot reader cannot insert terms")
  nextTerm := fun _ conn => do return ((← counterOn conn "next_term").getD 1).toNatClampNeg
  setNextTerm _ := fun _ _ => throw (.misuse "a snapshot reader cannot write counters")

end Tiramemsu.Term
