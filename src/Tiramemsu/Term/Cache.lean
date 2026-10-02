/-
The term dictionary on a store, and its caches (shell, unverified; refinement-tested against
the pure `Dict` model):

- `TermBackend` (see `Tiramemsu.Term.Backend`) for `SqliteStore`, with the SQL of Rust's
  `term.rs`; the algorithms `intern`, `lookupValue`, `decode` are generic over it.
- `WriterCache`: a committed key/id map plus a per-transaction overlay, merged on commit and
  dropped on rollback; capacity unbounded, `n` (cleared past `2n`, as Rust), or 0 (off).
- `ReaderCache`: an id → row LRU filled only from committed rows (snapshot readers).
Terms are immutable, so no cache entry is ever invalidated, only evicted.
-/
import Std.Data.HashMap
import Tiramemsu.Term.Backend
import Tiramemsu.Sqlite.Store

namespace Tiramemsu.Term

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Sqlite

--# @lat: [[codec#Term Dictionary#Caches And SQLite]]

instance : Hashable TermKey where
  hash k := hash (k.tag.toNat, k.lex, k.dt.getD 0, k.lang.getD "")

/-- Keys are cached by their coalesced form. -/
abbrev CKey := Nat × String × Int64 × String

def TermKey.ckey (k : TermKey) : CKey := (k.tag.toNat, k.lex, k.dt.getD 0, k.lang.getD "")

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
    let r ← TermReader.lookupKey (m := m) k
    -- not in the overlay, so the row was committed before this transaction
    if c.enabled then if let some i := r then (c.committed.modify (·.insert k.ckey i) : IO _)
    pure r
  rowById i := fun c => do
    if c.enabled then
      if let some r := (← (c.overlayRev.get : IO _))[i]? then return some r
      if let some r := (← (c.committedRev.get : IO _))[i]? then return some r
    let r ← TermReader.rowById (m := m) i
    if c.enabled then
      if let some row := r then
        (c.committed.modify (·.insert row.key.ckey i) : IO _)
        (c.committedRev.modify (·.insert i row) : IO _)
    pure r
  insertRow r := fun c => do
    TermBackend.insertRow (m := m) r
    if c.enabled then
      (c.overlay.modify (·.insert r.key.ckey r.id) : IO _)
      (c.overlayRev.modify (·.insert r.id r) : IO _)
  nextTerm := fun _ => TermBackend.nextTerm (m := m)
  setNextTerm n := fun _ => TermBackend.setNextTerm (m := m) n

/-! ## The reader cache -/

/-- An id → row LRU for snapshot readers; only committed rows ever reach it. -/
structure ReaderCache where
  capacity : Nat
  entries : IO.Ref (Std.HashMap Nat (Row × Nat))
  tick : IO.Ref Nat
  /-- Key → id of terms found (only hits: terms are immutable, so a hit stays valid). -/
  keys : IO.Ref (Std.HashMap CKey Nat)

def ReaderCache.new (capacity : Nat) : IO ReaderCache := do
  pure { capacity := max capacity 1, entries := ← IO.mkRef {}, tick := ← IO.mkRef 0, keys := ← IO.mkRef {} }

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

/-- A snapshot reader without a cache. -/
instance : TermReader ReaderM where
  lookupKey k := fun conn => lookupOn conn k
  rowById i := fun conn => byIdOn conn i

/-- A snapshot reader behind the LRU (committed rows only). -/
instance : TermBackend (ReaderT ReaderCache ReaderM) where
  lookupKey k := fun c conn => do
    if let some i := (← (c.keys.get : IO _))[k.ckey]? then return some i
    let r ← lookupOn conn k
    if let some i := r then
      if (← (c.keys.get : IO _)).size < c.capacity then (c.keys.modify (·.insert k.ckey i) : IO _)
    pure r
  rowById i := fun c conn => do
    if let some r ← (c.get i : IO _) then return some r
    let r ← byIdOn conn i
    if let some row := r then (c.put row : IO _)
    pure r
  insertRow _ := fun _ _ => throw (.misuse "a snapshot reader cannot insert terms")
  nextTerm := fun _ conn => do return ((← counterOn conn "next_term").getD 1).toNatClampNeg
  setNextTerm _ := fun _ _ => throw (.misuse "a snapshot reader cannot write counters")

end Tiramemsu.Term
