/-
`SqliteStore`: the store interface over leansqlite. Linked to `ModelStore` by refinement
tests, never by an axiom. Shell module (unverified).

- One writer connection; every write needs an open write transaction, tracked here so that
  misuse is reported without sending SQL.
- Reads on the writer see its own uncommitted writes; snapshot readers are reader
  connections inside a read transaction.
- Constraint aborts of the format-1 triggers and unique indexes map to store violations;
  any other SQLite failure inside a write transaction rolls the transaction back.
-/
import Tiramemsu.Store.Interface
import Tiramemsu.Sqlite.Sql

namespace Tiramemsu.Sqlite

open Tiramemsu.Store

--# @lat: [[architecture#SQLite Boundary#SqliteStore]]

/-- Write-transaction state of the writer connection. -/
structure TxState where
  inTx : Bool := false
  /-- Open savepoints, newest first. -/
  sps : List String := []
  deriving Repr, Inhabited

/-- An open SQLite store: the writer connection and a pool of idle reader connections. -/
structure Store where
  path : System.FilePath
  opts : ConnOptions
  writer : IO.Ref (Option Conn)
  txState : IO.Ref TxState
  idle : IO.Ref (Array Conn)

/-- A snapshot reader: a reader connection inside a read transaction. -/
structure Reader where
  conn : Conn

/-- The writer monad of the SQLite store. -/
abbrev SqliteM := ReaderT Store SqlM

/-- The reader monad of a snapshot. -/
abbrev ReaderM := ReaderT Conn SqlM

/-- Opens a store on a file that already carries the format-1 schema. -/
def Store.open (path : System.FilePath) (opts : ConnOptions := {}) : SqlM Store := do
  let w ← openWriter path opts
  pure { path, opts, writer := ← IO.mkRef (some w), txState := ← IO.mkRef {},
         idle := ← IO.mkRef #[] }

/-- Closes the store: drops cached statements and every connection reference. Uncommitted
writes are rolled back by SQLite when the connection is closed. -/
def Store.close (st : Store) : IO Unit := do
  if let some c ← st.writer.get then c.clearCache
  st.writer.set none
  for c in ← st.idle.get do c.clearCache
  st.idle.set #[]
  st.txState.set {}

/-- The writer connection. -/
def Store.conn (st : Store) : SqlM Conn := do
  match ← st.writer.get with
  | some c => pure c
  | none => throw (.misuse "store is closed")

/-! ## Row readers -/

def readTriple (st : SQLite.Stmt) : SqlM TripleRow := do
  pure { eid := ← colInt! st 0, s := ← colInt! st 1, p := ← colInt! st 2, o := ← colInt! st 3,
         tAdd := ← colInt! st 4, tRet := ← colInt st 5, vFrom := ← colInt st 6,
         vTo := ← colInt st 7, retKind := ← colInt st 8 }

def readTerm (st : SQLite.Stmt) : SqlM TermRow := do
  let lex ← colText st 2
  pure { id := ← colInt! st 0, tag := ← colInt! st 1, lex := lex.getD "", dt := ← colInt st 3,
         lang := ← colText st 4, num := ← colReal st 5 }

def readTx (st : SQLite.Stmt) : SqlM TxRow := do
  pure { t := ← colInt! st 0, instant := ← colInt! st 1 }

def readVolatile (st : SQLite.Stmt) : SqlM VolatileRow := do
  pure { s := ← colInt! st 0, key := ← colInt! st 1, value := ← colInt! st 2,
         updatedAt := ← colInt! st 3 }

/-! ## Reads on a connection -/

/-- A statement for a scan: the cached one, or a fresh one when the cached one is still
stepping (a scan nested in the callback of a scan of the same shape). -/
def Conn.prepareFree (c : Conn) (sql : String) : SqlM SQLite.Stmt := do
  let st ← c.prepare sql
  if ← lift st.isBusy then lift (c.db.prepare sql) else pure st

partial def scanLoop {m : Type → Type} [Monad m] [MonadLiftT SqlM m] {β : Type}
    (st : SQLite.Stmt) (f : β → TripleRow → m (ForInStep β)) (b : β) : m β := do
  if ← (step st : SqlM Bool) then
    let r ← (readTriple st : SqlM TripleRow)
    match ← f b r with
    | .done b' => pure b'
    | .yield b' => scanLoop st f b'
  else pure b

/-- An ordered scan with early exit on a connection. -/
def scanOn {m : Type → Type} [Monad m] [MonadLiftT SqlM m] [MonadFinally m] {β : Type}
    (c : Conn) (sp : ScanSpec) (init : β) (f : β → TripleRow → m (ForInStep β)) : m β := do
  if !sp.valid then (throw .invalidScan : SqlM β) else
  let (sql, params) := scanSql sp
  let st ← (c.prepareFree sql : SqlM SQLite.Stmt)
  try
    for h : i in [0:params.size] do
      (bindVal st (i + 1).toInt32 params[i] : SqlM Unit)
    scanLoop st f init
  finally
    (resetQuiet st : SqlM Unit)

def tripleOn (c : Conn) (e : Int64) : SqlM (Option TripleRow) :=
  c.queryOne sqlTriple #[.int e] readTriple

def termByIdOn (c : Conn) (i : Int64) : SqlM (Option TermRow) :=
  c.queryOne sqlTermById #[.int i] readTerm

def termByKeyOn (c : Conn) (tag : Int64) (lex : String) (dt : Option Int64)
    (lang : Option String) : SqlM (Option Int64) :=
  c.queryOne sqlTermByKey #[.int tag, .text lex, .ofOpt dt, .ofOptText lang] (colInt! · 0)

def txByTOn (c : Conn) (t : Int64) : SqlM (Option TxRow) :=
  c.queryOne sqlTxByT #[.int t] readTx

def txAtOrBeforeOn (c : Conn) (i : Int64) : SqlM (Option TxRow) :=
  c.queryOne sqlTxAtOrBefore #[.int i] readTx

def counterOn (c : Conn) (n : String) : SqlM (Option Int64) :=
  c.queryOne sqlCounter #[.text n] (colInt! · 0)

def volatileGetOn (c : Conn) (s k : Int64) : SqlM (Option VolatileRow) :=
  c.queryOne sqlVolatileGet #[.int s, .int k] readVolatile

def volatileOfOn (c : Conn) (s : Int64) : SqlM (Array VolatileRow) :=
  c.queryAll sqlVolatileOf #[.int s] readVolatile

def predMultiOn (c : Conn) (p : Int64) : SqlM Bool := do
  return (← c.queryOne sqlPredMulti #[.int p] (fun _ => pure ())).isSome

/-! ## Writes -/

/-- Which unique index a write may hit. -/
inductive UniqueCtx where
  | none | termKey | txInstant

/-- Maps constraint aborts to store violations; other errors are left as they are. -/
def mapConstraint (ctx : UniqueCtx) : StoreError → StoreError
  | e@(.sqlite _ ext msg) =>
    let has (needle : String) := (msg.splitOn needle).length > 1
    if ext == SQLITE_CONSTRAINT_TRIGGER then
      if has "never reused" then .violation .idReused
      else if has "single retraction" then .violation .retractOnce
      else e
    else if ext == SQLITE_CONSTRAINT_PRIMARYKEY then .violation .idReused
    else if ext == SQLITE_CONSTRAINT_UNIQUE then
      match ctx with
      | .termKey => .violation .termKeyTaken
      | .txInstant => .violation .instantTaken
      | .none => e
    else e
  | e => e

/-- Rolls the write transaction back after a storage error. -/
def Store.abortTx (st : Store) (c : Conn) : IO Unit := do
  let _ ← (c.rollback.run : IO _)
  st.txState.set {}

/-- A data write: misuse outside a transaction; storage errors roll the transaction back. -/
def writeIn (act : Conn → SqlM Unit) : SqliteM Unit := fun st => do
  unless (← st.txState.get).inTx do throw (.misuse "write outside a transaction")
  let c ← st.conn
  try act c
  catch e =>
    if let .sqlite .. := e then st.abortTx c
    throw e

/-- Runs a write statement, mapping constraint aborts. -/
def runWrite (c : Conn) (ctx : UniqueCtx) (sql : String) (params : Array Val) : SqlM Unit :=
  tryCatch (c.run sql params) fun e => throw (mapConstraint ctx e)

def insertTripleOn (c : Conn) (r : TripleRow) : SqlM Unit :=
  runWrite c .none sqlInsertTriple
    #[.int r.eid, .int r.s, .int r.p, .int r.o, .int r.tAdd, .ofOpt r.tRet, .ofOpt r.vFrom,
      .ofOpt r.vTo, .ofOpt r.retKind]

/-- The guarded retraction update; with no changed row, a lookup tells not-found from
retract-once. -/
def retractOn (c : Conn) (e t k : Int64) : SqlM Unit := do
  runWrite c .none sqlRetract #[.int t, .int k, .int e]
  if (← c.changes) == 0 then
    match ← tripleOn c e with
    | none => throw .notFound
    | some _ => throw (.violation .retractOnce)

def insertTermOn (c : Conn) (r : TermRow) : SqlM Unit :=
  runWrite c .termKey sqlInsertTerm
    #[.int r.id, .int r.tag, .text r.lex, .ofOpt r.dt, .ofOptText r.lang, .ofOptReal r.num]

def insertTxOn (c : Conn) (r : TxRow) : SqlM Unit :=
  runWrite c .txInstant sqlInsertTx #[.int r.t, .int r.instant]

/-! ## Transactions -/

def Store.begin : SqliteM Unit := fun st => do
  if (← st.txState.get).inTx then throw (.misuse "begin inside a transaction")
  (← st.conn).beginImmediate
  st.txState.set { inTx := true }

def Store.commit : SqliteM Unit := fun st => do
  unless (← st.txState.get).inTx do throw (.misuse "commit without a transaction")
  let c ← st.conn
  try c.commit
  catch e => st.abortTx c; throw e
  st.txState.set {}

def Store.rollback : SqliteM Unit := fun st => do
  unless (← st.txState.get).inTx do throw (.misuse "rollback without a transaction")
  let c ← st.conn
  try c.rollback
  finally st.txState.set {}

/-- Savepoint control: misuse checks, then the SQL, then the tracked stack. -/
def Store.spOp (what : String) (n : String) (needOpen : Bool) (sql : Conn → String → SqlM Unit)
    (next : List String → List String) : SqliteM Unit := fun st => do
  let ts ← st.txState.get
  unless ts.inTx do throw (.misuse s!"{what} outside a transaction")
  if needOpen && !ts.sps.contains n then throw (.misuse s!"no open savepoint {n}")
  let c ← st.conn
  try sql c n
  catch e => st.abortTx c; throw e
  st.txState.set { ts with sps := next ts.sps }

def Store.savepoint (n : String) : SqliteM Unit :=
  Store.spOp "savepoint" n false Conn.savepoint (n :: ·)

def Store.rollbackTo (n : String) : SqliteM Unit :=
  Store.spOp "rollback to savepoint" n true Conn.rollbackTo (·.dropWhile (· != n))

def Store.release (n : String) : SqliteM Unit :=
  Store.spOp "release" n true Conn.release fun sps => (sps.dropWhile (· != n)).drop 1

/-! ## Interface instances -/

/-- A read on the writer connection. -/
def onWriter {α : Type} (f : Conn → SqlM α) : SqliteM α := fun st => do f (← st.conn)

instance : ReadStore SqliteM where
  scan sp init f := fun st => do scanOn (← st.conn) sp init (fun b r => f b r st)
  triple e := onWriter (tripleOn · e)
  termById i := onWriter (termByIdOn · i)
  termByKey tag lex dt lang := onWriter (termByKeyOn · tag lex dt lang)
  txByT t := onWriter (txByTOn · t)
  txAtOrBefore i := onWriter (txAtOrBeforeOn · i)
  counter n := onWriter (counterOn · n)
  volatileGet s k := onWriter (volatileGetOn · s k)
  volatileOf s := onWriter (volatileOfOn · s)
  predMulti p := onWriter (predMultiOn · p)

instance : WriteStore SqliteM where
  insertTriple r := writeIn (insertTripleOn · r)
  retract e t k := writeIn (retractOn · e t k)
  insertTerm r := writeIn (insertTermOn · r)
  insertTx r := writeIn (insertTxOn · r)
  setCounter n v := writeIn fun c => runWrite c .none sqlSetCounter #[.text n, .int v]
  volatilePut r := writeIn fun c =>
    runWrite c .none sqlVolatilePut #[.int r.s, .int r.key, .int r.value, .int r.updatedAt]
  volatileDel s k := writeIn fun c => runWrite c .none sqlVolatileDel #[.int s, .int k]
  addPredMulti p := writeIn fun c => runWrite c .none sqlAddPredMulti #[.int p]
  begin := Store.begin
  commit := Store.commit
  rollback := Store.rollback
  savepoint := Store.savepoint
  rollbackTo := Store.rollbackTo
  release := Store.release

instance : ReadStore ReaderM where
  scan sp init f := fun c => scanOn c sp init (fun b r => f b r c)
  triple e := fun c => tripleOn c e
  termById i := fun c => termByIdOn c i
  termByKey tag lex dt lang := fun c => termByKeyOn c tag lex dt lang
  txByT t := fun c => txByTOn c t
  txAtOrBefore i := fun c => txAtOrBeforeOn c i
  counter n := fun c => counterOn c n
  volatileGet s k := fun c => volatileGetOn c s k
  volatileOf s := fun c => volatileOfOn c s
  predMulti p := fun c => predMultiOn c p

/-- Snapshots are reader connections (pooled) inside a read transaction. -/
instance : SnapshotStore SqliteM Reader ReaderM where
  beginRead := fun st => do
    if (← st.writer.get).isNone then throw (.misuse "store is closed")
    let c ← match (← st.idle.get).back? with
      | some c => do st.idle.modify (·.pop); pure c
      | none => openReader st.path st.opts
    c.beginRead
    pure { conn := c }
  endRead r := fun st => do
    r.conn.endRead
    st.idle.modify (·.push r.conn)
  withSnapshot r act := fun _ => act r.conn

/-! ## Whole-table reads (raw dump) -/

def dumpMeta (c : Conn) : SqlM (Array (String × Int64)) :=
  c.queryAll "SELECT CAST(key AS BLOB), value FROM meta ORDER BY key" #[] fun st => do
    pure (((← colText st 0).getD ""), ← colInt! st 1)

def dumpTerms (c : Conn) : SqlM (Array TermRow) :=
  c.queryAll ("SELECT id, tag, CAST(lex AS BLOB), dt, CAST(lang AS BLOB), num FROM term " ++
    "ORDER BY id") #[] readTerm

def dumpTxs (c : Conn) : SqlM (Array TxRow) :=
  c.queryAll "SELECT t, instant FROM tx ORDER BY t" #[] readTx

def dumpTriples (c : Conn) : SqlM (Array TripleRow) :=
  c.queryAll s!"SELECT {tripleCols} FROM triple ORDER BY eid" #[] readTriple

def dumpVolatile (c : Conn) : SqlM (Array VolatileRow) :=
  c.queryAll "SELECT s, key, value, updated_at FROM volatile ORDER BY s, key" #[] readVolatile

def dumpPredMulti (c : Conn) : SqlM (Array Int64) :=
  c.queryAll "SELECT p FROM pred_multi ORDER BY p" #[] (colInt! · 0)

end Tiramemsu.Sqlite
