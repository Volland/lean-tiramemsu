/-
The database handle (Rust's `tiramemsu/src/db.rs`, D10): one writer connection behind a mutex,
a pool of reader connections, an injectable clock and the writer's term cache.

- Every transaction, dry run and speculation runs on the writer under the mutex, inside
  `BEGIN IMMEDIATE`; concurrent callers wait. Handles on one file are serialised by SQLite
  (busy timeout).
- The writer's term cache takes a transaction's terms only after it commits.
- `withView` takes a reader and one read transaction for the whole scope, so every read of the
  view sees one WAL snapshot, a committed prefix whose last transaction is the view's basis
  (listed deviation: Rust takes a snapshot per read). The reader returns to the pool when the
  scope ends, normally or with an error.
Shell module (unverified).
-/
import Std.Sync.Mutex
import Tiramemsu.Engine.Transact
import Tiramemsu.Storage.Open
import Tiramemsu.Term.Cache
import Tiramemsu.Shell.Clock
import Tiramemsu.Shell.Pool

namespace Tiramemsu.Shell

open Tiramemsu.Store Tiramemsu.Sqlite Tiramemsu.Engine Tiramemsu.Term

--# @lat: [[engine#Shell]]

/-- Options of a database handle. -/
structure DbOptions where
  readers : Nat := 4
  busyTimeoutMs : Nat := 5000
  /-- Writer term cache: `none` unbounded, `some 0` off. -/
  termCacheCapacity : Option Nat := some 16384

/-- An open database. -/
structure Db where
  path : System.FilePath
  store : Sqlite.Store
  cache : WriterCache
  clock : Clock
  writer : Std.BaseMutex
  pool : Pool

/-- A view pinned to one snapshot of a reader. -/
structure PinnedView where
  conn : Conn
  spec : Tiramemsu.View.ViewSpec
  /-- The last committed transaction of the snapshot. -/
  basis : Int64

def storeErr {α : Type} : Except StoreError (Except Error α) → Except Error α
  | .ok r => r
  | .error e => .error (.store e)

/-- Opens (creating or checking) the database at `path`. -/
def Db.open (path : System.FilePath) (opts : DbOptions := {}) (clock : Clock := systemClock) :
    IO (Except Storage.OpenError Db) := do
  let co : ConnOptions := { busyTimeoutMs := opts.busyTimeoutMs.toInt32 }
  match ← Storage.openFile path co with
  | .error e => pure (.error e)
  | .ok st =>
    match ← (Pool.open path co opts.readers).run with
    | .error e => st.close; pure (.error (.store e))
    | .ok pool =>
      pure (.ok { path, store := st, cache := ← WriterCache.new opts.termCacheCapacity, clock,
                  writer := ← (Std.BaseMutex.new : BaseIO _), pool })

/-- Closes the handle (uncommitted writes are rolled back by SQLite). -/
def Db.close (db : Db) : IO Unit := do
  db.store.close
  db.pool.close

/-- Runs `f` holding the writer. -/
def Db.withWriter {α : Type} (db : Db) (f : IO α) : IO α := do
  db.writer.lock
  try f finally db.writer.unlock

/-- Runs a core on the writer and settles the term cache. -/
def Db.runCore {α : Type} (db : Db) (keep : Bool) (core : CachedM SqliteM (Except Error α)) :
    IO (Except Error α) := db.withWriter do
  let r ← (core db.cache db.store).run
  match r with
  | .ok (.ok _) => if keep then db.cache.commit else db.cache.rollback
  | _ => db.cache.rollback
  pure (storeErr r)

/-- The clock as a store action (read after `BEGIN IMMEDIATE`). -/
def Db.now (db : Db) : CachedM SqliteM Int := fun _ _ => do return (← (db.clock.now : IO Int))

/-- A dry run: the report a commit would return; nothing is kept but burned ids. -/
def Db.dryRun {α : Type} (db : Db) (opts : TxOptions) (prog : TxProg α) :
    IO (Except Error (α × TxReport)) :=
  db.runCore false (dryRunCore db.now opts prog.run)

/-- One transaction (a dry run when `opts.dryRun`). -/
def Db.transact {α : Type} (db : Db) (opts : TxOptions) (prog : TxProg α) :
    IO (Except Error (α × TxReport)) :=
  if opts.dryRun then db.dryRun opts prog
  else db.runCore true (transactCore db.now opts prog.run)

/-- A speculation: `prog` hypothetically, then `query` on the uncommitted state. -/
def Db.speculate {α β : Type} (db : Db) (prog : TxProg α) (validAt : Option Int64)
    (query : ReadProg β) : IO (Except Error β) :=
  db.runCore false (speculateCore db.now prog.run validAt query)

/-- Runs a read program on a reader connection. -/
def runOn {α : Type} (c : Conn) (p : RProg α) : SqlM α :=
  (RProg.interp (m := ReaderM) ROp.run p) c

/-- Runs `f` on a view pinned to one read transaction of a pooled reader. -/
def Db.withView {α : Type} (db : Db) (spec : Tiramemsu.View.ViewSpec) (f : PinnedView → IO α) : IO α := do
  let c ← db.pool.acquire
  try
    match ← c.beginRead.run with
    | .error e => throw (IO.userError s!"cannot begin a read: {e}")
    | .ok () =>
      try
        let basis ← match ← (runOn c Tiramemsu.View.basisT).run with
          | .ok b => pure b
          | .error e => throw (IO.userError s!"cannot read the basis: {e}")
        f { conn := c, spec, basis }
      finally
        let _ ← c.endRead.run
  finally
    db.pool.release c

/-- A query on a pinned view. -/
def PinnedView.run {α : Type} (v : PinnedView) (q : ReadProg α) : IO (Except Error α) := do
  return storeErr (← (runOn v.conn (ReadProg.run v.spec q)).run)

end Tiramemsu.Shell
