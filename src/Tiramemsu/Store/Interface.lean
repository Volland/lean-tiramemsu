/-
The abstract store interface. The engine reaches storage only through these classes, which
have exactly two implementations: `ModelStore` (pure, every theorem is stated over it) and
`SqliteStore` (leansqlite, linked to the model by refinement tests).
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Store.Types

namespace Tiramemsu.Store

--# @lat: [[architecture#Store Abstraction#Interface]]

/-- Reads: ordered range scans with early exit, and point reads. A missing row is `none`. -/
class ReadStore (m : Type → Type) where
  /-- Ordered fold over the rows a scan matches; `.done` stops the scan. -/
  scan {β : Type} : ScanSpec → β → (β → TripleRow → m (ForInStep β)) → m β
  /-- A triple row by statement id. -/
  triple : Int64 → m (Option TripleRow)
  /-- A term row by id. -/
  termById : Int64 → m (Option TermRow)
  /-- A term id by key; an absent datatype or language matches only an absent one. -/
  termByKey : (tag : Int64) → (lex : String) → Option Int64 → Option String → m (Option Int64)
  /-- A transaction row by number. -/
  txByT : Int64 → m (Option TxRow)
  /-- The transaction with the greatest instant at or before the given instant. -/
  txAtOrBefore : (instant : Int64) → m (Option TxRow)
  /-- A named counter of `meta`. -/
  counter : String → m (Option Int64)
  /-- A volatile row by `(s, key)`. -/
  volatileGet : (s key : Int64) → m (Option VolatileRow)
  /-- All volatile rows of a subject, ordered by key. -/
  volatileOf : (s : Int64) → m (Array VolatileRow)
  /-- Whether a predicate is in the multi-eid set. -/
  predMulti : Int64 → m Bool

/-- Writes, write transactions and savepoints. Every write needs an open transaction. -/
class WriteStore (m : Type → Type) extends ReadStore m where
  /-- Appends a triple row; a reused statement id is `idReused`. -/
  insertTriple : TripleRow → m Unit
  /-- The single retraction update: sets `t_ret` and `ret_kind` of a live row. -/
  retract : (eid t kind : Int64) → m Unit
  /-- Appends a term row (numeric value normalized as SQLite stores a REAL). -/
  insertTerm : TermRow → m Unit
  /-- Appends a transaction row. -/
  insertTx : TxRow → m Unit
  /-- Sets a named counter. -/
  setCounter : String → Int64 → m Unit
  /-- Inserts or replaces the volatile row for `(s, key)`. -/
  volatilePut : VolatileRow → m Unit
  /-- Deletes the volatile row for `(s, key)` if present. -/
  volatileDel : (s key : Int64) → m Unit
  /-- Adds a predicate to the multi-eid set; idempotent. -/
  addPredMulti : Int64 → m Unit
  /-- Begins a write transaction (`BEGIN IMMEDIATE` on SQLite). -/
  begin : m Unit
  /-- Commits the write transaction. -/
  commit : m Unit
  /-- Rolls the write transaction back. -/
  rollback : m Unit
  /-- Opens a savepoint. -/
  savepoint : String → m Unit
  /-- Restores the state at the newest open savepoint of that name and keeps it open. -/
  rollbackTo : String → m Unit
  /-- Closes the newest open savepoint of that name and every newer one, keeping writes. -/
  release : String → m Unit
  /-- A named counter of `meta` as it was when the write transaction began (outside a
  transaction: the committed value). The engine's write guards compare against it. -/
  baseCounter : String → m (Option Int64)

/-! ## Lifting through a reader (the writer's term cache is a `ReaderT` layer) -/

instance {ρ : Type} {m : Type → Type} [ReadStore m] : ReadStore (ReaderT ρ m) where
  scan sp init f := fun r => ReadStore.scan sp init (fun b row => f b row r)
  triple e := fun _ => ReadStore.triple e
  termById i := fun _ => ReadStore.termById i
  termByKey tag lex dt lang := fun _ => ReadStore.termByKey tag lex dt lang
  txByT t := fun _ => ReadStore.txByT t
  txAtOrBefore i := fun _ => ReadStore.txAtOrBefore i
  counter n := fun _ => ReadStore.counter n
  volatileGet s k := fun _ => ReadStore.volatileGet s k
  volatileOf s := fun _ => ReadStore.volatileOf s
  predMulti p := fun _ => ReadStore.predMulti p

instance {ρ : Type} {m : Type → Type} [WriteStore m] : WriteStore (ReaderT ρ m) where
  insertTriple r := fun _ => WriteStore.insertTriple r
  retract e t k := fun _ => WriteStore.retract e t k
  insertTerm r := fun _ => WriteStore.insertTerm r
  insertTx r := fun _ => WriteStore.insertTx r
  setCounter n v := fun _ => WriteStore.setCounter n v
  volatilePut r := fun _ => WriteStore.volatilePut r
  volatileDel s k := fun _ => WriteStore.volatileDel s k
  addPredMulti p := fun _ => WriteStore.addPredMulti p
  begin := fun _ => WriteStore.begin
  commit := fun _ => WriteStore.commit
  rollback := fun _ => WriteStore.rollback
  savepoint n := fun _ => WriteStore.savepoint n
  rollbackTo n := fun _ => WriteStore.rollbackTo n
  release n := fun _ => WriteStore.release n
  baseCounter n := fun _ => WriteStore.baseCounter n

/--
Snapshot readers: separate handles that observe the committed state as of `beginRead`.
`withSnapshot` runs reads (a `ReadStore r` program) on a snapshot.
-/
class SnapshotStore (m : Type → Type) (snap : outParam Type) (r : outParam (Type → Type)) where
  beginRead : m snap
  endRead : snap → m Unit
  withSnapshot {α : Type} : snap → r α → m α

end Tiramemsu.Store
