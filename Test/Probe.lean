/-
leansqlite gap-check probes: one executable probe per need of the sqlite-binding spec.
The recorded statuses (direct / via SQL / gap) live in `Test/gap-check.md`.
-/
import Test.Util

namespace Test.Probe

open Test Tiramemsu.Sqlite Tiramemsu.Store

--# @lat: [[verification#Trusted Base#leansqlite Gap Check]]

/-- Runs a probe body; a thrown store error fails the probe. -/
def probe (name : String) (body : SqlM Bool) : TestM Unit := do
  match ← body.run with
  | .ok ok => check name ok "probe returned false"
  | .error e => check name false (toString e)

def one {α : Type} (c : Conn) (sql : String) (params : Array Val) (row : SQLite.Stmt → SqlM α) :
    SqlM (Option α) := c.queryOne sql params row

def intOf (c : Conn) (sql : String) (params : Array Val := #[]) : SqlM (Option Int64) := do
  return (← one c sql params (colInt · 0)).bind id

def textOf (c : Conn) (sql : String) (params : Array Val := #[]) : SqlM (Option String) := do
  return (← one c sql params (colText · 0)).bind id

/-- The error of an action, if it fails. -/
def errorOf {α : Type} (x : SqlM α) : SqlM (Option StoreError) :=
  tryCatch (do let _ ← x; pure none) (fun e => pure (some e))

def table (c : Conn) : SqlM Unit := do
  c.exec "CREATE TABLE t(id INTEGER PRIMARY KEY, i INTEGER, x TEXT, b BLOB, r REAL) STRICT"
  -- read transactions pin their snapshot with a read of `meta`
  c.exec "CREATE TABLE IF NOT EXISTS meta(key TEXT PRIMARY KEY, value INTEGER NOT NULL) STRICT"

/-- Every probe except the large-file one. -/
def probes : TestM Unit := do
  -- open read-write-create, and read-only on an existing file
  let p ← freshPath "probe-open"
  probe "open-rwc" do
    let c ← openWriter p
    table c
    c.clearCache
    pure (← (p.pathExists : IO Bool))
  probe "open-readonly" do
    let r ← openReader p
    let ro := (← lift (r.db.dbReadonly)) == some .readOnly
    let missing ← errorOf (openReader ((← (scratchDir : IO _)) / "does-not-exist.db"))
    pure (ro && match missing with | some (.sqlite 14 _ _) => true | _ => false)
  -- WAL and synchronous = NORMAL through PRAGMA statements
  probe "wal-synchronous" do
    let c ← openWriter p
    let jm ← textOf c "SELECT CAST(journal_mode AS BLOB) FROM pragma_journal_mode"
    let sync ← intOf c "SELECT synchronous FROM pragma_synchronous"
    pure (jm == some "wal" && sync == some 1)
  -- busy timeout: a second writer waits about the timeout, then reports SQLITE_BUSY
  probe "busy-timeout" do
    let a ← openWriter p
    let b ← openWriter p { busyTimeoutMs := 200 }
    a.beginImmediate
    let t0 ← (IO.monoMsNow : IO Nat)
    let e ← errorOf b.beginImmediate
    let t1 ← (IO.monoMsNow : IO Nat)
    a.rollback
    pure ((match e with | some (.sqlite 5 _ _) => true | _ => false) && t1 - t0 ≥ 150)
  -- BEGIN IMMEDIATE / COMMIT / ROLLBACK through SQL
  probe "transactions" do
    let c ← openWriter p
    c.beginImmediate
    c.run "INSERT INTO t(id, i) VALUES (1, 10)"
    c.rollback
    let afterRollback ← intOf c "SELECT count(*) FROM t"
    c.beginImmediate
    c.run "INSERT INTO t(id, i) VALUES (1, 10)"
    c.commit
    let afterCommit ← intOf c "SELECT count(*) FROM t"
    pure (afterRollback == some 0 && afterCommit == some 1)
  -- a read transaction holds one snapshot until it ends
  probe "read-snapshot" do
    let w ← openWriter p
    let r ← openReader p
    r.beginRead
    let before ← intOf r "SELECT count(*) FROM t"
    w.beginImmediate; w.run "INSERT INTO t(id, i) VALUES (2, 20)"; w.commit
    let during ← intOf r "SELECT count(*) FROM t"
    r.endRead
    r.beginRead
    let after ← intOf r "SELECT count(*) FROM t"
    r.endRead
    pure (before == some 1 && during == some 1 && after == some 2)
  -- SAVEPOINT / ROLLBACK TO / RELEASE through SQL
  probe "savepoints" do
    let c ← openWriter p
    c.beginImmediate
    c.run "INSERT INTO t(id, i) VALUES (3, 30)"
    c.savepoint "s"
    c.run "INSERT INTO t(id, i) VALUES (4, 40)"
    c.rollbackTo "s"
    c.run "INSERT INTO t(id, i) VALUES (5, 50)"
    c.release "s"
    c.commit
    let ids ← c.queryAll "SELECT id FROM t ORDER BY id" #[] (colInt! · 0)
    pure (ids == #[1, 2, 3, 5])
  -- prepared statements reused with reset and rebinding
  probe "statement-reuse" do
    let c ← openWriter p
    let sql := "SELECT i FROM t WHERE id = ?"
    let a ← intOf c sql #[.int 1]
    let b ← intOf c sql #[.int 2]
    let n := (← c.stmts.get).size
    let st ← c.prepare sql
    lift (st.bindInt64 1 3); let _ ← step st; let v ← colInt st 0
    lift st.reset; lift st.clearBindings
    let _ ← step st; let cleared ← colInt st 0  -- NULL parameter matches no row
    lift st.reset
    pure (a == some 10 && b == some 20 && v == some 30 && cleared == none && n ≥ 1)
  -- binding and reading Int64, text, blob, NULL and double
  probe "bind-read-values" do
    let c ← openWriter p
    c.beginImmediate
    c.run "INSERT INTO t(id, i, x, b, r) VALUES (?, ?, CAST(? AS TEXT), ?, ?)"
      #[.int 6, .int (-7), .text "héllo", .text "blob", .real (2.5 : Float).toBits]
    let st ← c.prepare "INSERT INTO t(id, b) VALUES (7, ?)"
    lift (st.bindBlob 1 (ByteArray.mk #[0, 1, 255])); let _ ← step st; lift st.reset
    c.commit
    let row ← one c "SELECT i, CAST(x AS BLOB), r FROM t WHERE id = 6" #[] fun st => do
      pure (← colInt st 0, ← colText st 1, ← colReal st 2)
    let blob ← one c "SELECT b FROM t WHERE id = 7" #[] fun st => lift (st.columnBlob 0)
    pure (row == some (some (-7), some "héllo", some (2.5 : Float).toBits) &&
      blob.map (·.data) == some #[0, 1, 255])
  -- ordered stepping with an early stop
  probe "ordered-early-stop" do
    let c ← openWriter p
    c.withStmt "SELECT id FROM t ORDER BY id" #[] fun st => do
      let mut got := #[]
      for _ in [0:3] do
        if ← step st then got := got.push (← colInt! st 0)
      pure (got == #[1, 2, 3])
  -- the changed-row count
  probe "changes" do
    let c ← openWriter p
    c.beginImmediate
    c.run "UPDATE t SET i = i + 1 WHERE id <= 3"
    let n ← c.changes
    c.run "UPDATE t SET i = 0 WHERE id = 999"
    let m ← c.changes
    c.rollback
    pure (n == 3 && m == 0)
  -- primary and extended result codes with the message
  probe "result-codes" do
    let c ← openWriter p
    c.exec "CREATE TABLE IF NOT EXISTS u(k INTEGER UNIQUE)"
    c.beginImmediate
    c.run "INSERT INTO u(k) VALUES (1)"
    let e ← errorOf (c.run "INSERT INTO u(k) VALUES (1)")
    c.rollback
    pure (match e with
      | some (.sqlite 19 2067 msg) => (msg.splitOn "UNIQUE").length > 1
      | _ => false)
  -- a connection opened on one thread and used on another
  probe "cross-thread" do
    let c ← openWriter p
    let task ← (IO.asTask (prio := .dedicated) (do
      match ← (intOf c "SELECT count(*) FROM t").run with
      | .ok v => pure v
      | .error e => throw (IO.userError (toString e))) : IO _)
    match ← (IO.wait task : IO _) with
    | .ok v => pure (v == some 6)
    | .error _ => pure false
  -- version and compile options
  probe "version-compile-options" do
    let c ← openMemory
    let v ← c.sqliteVersion
    let opts ← c.compileOptions
    let parts := (v.splitOn ".").map String.toNat!
    let atLeast := match parts with
      | [a, b, _] => a > 3 || (a == 3 && b ≥ 37)
      | _ => false
    let threadsafe := opts.any fun o => o.startsWith "THREADSAFE=" && o != "THREADSAFE=0"
    -- STRICT tables, partial and expression indexes
    c.exec "CREATE TABLE s(a INTEGER, b TEXT) STRICT"
    c.exec "CREATE INDEX s_partial ON s(a) WHERE a IS NOT NULL"
    c.exec "CREATE INDEX s_expr ON s(ifnull(b, ''))"
    pure (atLeast && threadsafe)

/-- Value fidelity: Int64 extremes, text with NUL, REAL normalization, NULL vs 0 vs ''. -/
def fidelity : TestM Unit := do
  let p ← freshPath "probe-values"
  probe "int64-extremes" do
    let c ← openWriter p
    table c
    let vals : Array Int64 := #[-9223372036854775808, -1, 0, 9223372036854775807]
    c.beginImmediate
    for h : i in [0:vals.size] do
      c.run "INSERT INTO t(id, i) VALUES (?, ?)" #[.int (i + 1).toInt64, .int vals[i]]
    c.commit
    let got ← c.queryAll "SELECT i FROM t ORDER BY id" #[] (colInt! · 0)
    pure (got == vals)
  probe "text-embedded-nul" do
    let c ← openWriter p
    let s := "a\x00b"
    c.beginImmediate
    c.run "INSERT INTO t(id, x) VALUES (10, CAST(? AS TEXT))" #[.text s]
    -- the direct leansqlite text calls stop at the NUL; recorded as a gap closed through SQL
    let st ← c.prepare "INSERT INTO t(id, x) VALUES (11, ?)"
    lift (st.bindText 1 s); let _ ← step st; lift st.reset
    c.commit
    let viaSql ← textOf c "SELECT CAST(x AS BLOB) FROM t WHERE id = 10"
    let direct ← one c "SELECT x FROM t WHERE id = 10" #[] fun st => lift (st.columnText 0)
    let directBind ← textOf c "SELECT CAST(x AS BLOB) FROM t WHERE id = 11"
    let typ ← textOf c "SELECT CAST(typeof(x) AS BLOB) FROM t WHERE id = 10"
    pure (viaSql == some s && typ == some "text" && direct != some s && directBind != some s)
  probe "real-normalization" do
    let c ← openWriter p
    let negZero : UInt64 := 0x8000000000000000
    let nan : UInt64 := 0x7FF8000000000001
    c.beginImmediate
    c.run "INSERT INTO t(id, r) VALUES (20, ?)" #[.real negZero]
    c.run "INSERT INTO t(id, r) VALUES (21, ?)" #[.real nan]
    c.run "INSERT INTO t(id, r) VALUES (22, ?)" #[.real (1.0 : Float).toBits]
    c.commit
    let z ← one c "SELECT r FROM t WHERE id = 20" #[] (colReal · 0)
    let n ← one c "SELECT r FROM t WHERE id = 21" #[] (colReal · 0)
    let o ← one c "SELECT r FROM t WHERE id = 22" #[] (colReal · 0)
    pure (z == some (some 0) && n == some none && o == some (some (1.0 : Float).toBits) &&
      normalizeNum (some negZero) == some 0 && normalizeNum (some nan) == none)
  probe "null-vs-zero-vs-empty" do
    let c ← openWriter p
    c.beginImmediate
    c.run "INSERT INTO t(id, i, x) VALUES (30, NULL, NULL)"
    c.run "INSERT INTO t(id, i, x) VALUES (31, 0, CAST(? AS TEXT))" #[.text ""]
    c.commit
    let a ← one c "SELECT i, CAST(x AS BLOB) FROM t WHERE id = 30" #[] fun st => do
      pure (← colInt st 0, ← colText st 1)
    let b ← one c "SELECT i, CAST(x AS BLOB) FROM t WHERE id = 31" #[] fun st => do
      pure (← colInt st 0, ← colText st 1)
    pure (a == some (none, none) && b == some (some 0, some ""))

/-- The Lean build registers no SQL table functions or user functions. -/
def noFunctions : TestM Unit := do
  let p ← freshFormat1 "probe-functions"
  probe "tm-path-unavailable" do
    let st ← Store.open p
    let c ← st.conn
    let e ← errorOf (lift (c.db.prepare "SELECT * FROM tm_path(1, 'knows+', 'REACH')"))
    st.close
    pure (match e with | some (.sqlite 1 1 msg) => (msg.splitOn "tm_path").length > 1 | _ => false)
  probe "no-user-functions" do
    -- Functions that are not built in, as seen by a store connection and by a bare
    -- leansqlite connection; SQLite's compiled-in extensions (e.g. FTS's `match`) appear on
    -- both, so equality shows the Lean build registers nothing of its own.
    let names (c : Conn) : SqlM (Array String) := do
      let rows ← c.queryAll
        "SELECT DISTINCT CAST(name AS BLOB) FROM pragma_function_list WHERE builtin = 0 ORDER BY 1"
        #[] (colText · 0)
      pure (rows.filterMap id)
    let st ← Store.open p
    let ours ← names (← st.conn)
    let bare ← names (← openMemory)
    st.close
    -- the Rust build registers `tm_*` functions (UDFs and the `tm_path` table function) and
    -- `rarray`; leansqlite offers `sha3*` only on request
    let foreign (n : String) := n.startsWith "tm_" || n == "rarray" || n.startsWith "sha3"
    pure (ours == bare && !ours.any foreign)

/-- Files larger than 2 GiB on a 64-bit platform (nightly only: writes about 2.1 GiB). -/
def largeFile : TestM Unit := do
  let p ← freshPath "probe-large"
  probe "large-file-over-2GiB" do
    let c ← openWriter p
    c.exec "PRAGMA journal_mode = DELETE"
    c.exec "PRAGMA synchronous = OFF"
    c.exec "CREATE TABLE big(id INTEGER PRIMARY KEY, pad BLOB)"
    c.beginImmediate
    for i in [0:2150] do
      c.run "INSERT INTO big(id, pad) VALUES (?, randomblob(1048576))" #[.int i.toInt64]
    c.run "INSERT INTO big(id, pad) VALUES (100000, x'0102')"
    c.commit
    let size ← (do return (← p.metadata).byteSize.toNat : IO Nat)
    let tail ← c.queryAll "SELECT id FROM big WHERE id >= 2148 ORDER BY id" #[] (colInt! · 0)
    let last ← one c "SELECT hex(pad) FROM big WHERE id = 100000" #[] (fun st => lift (st.columnText 0))
    let n ← intOf c "SELECT count(*) FROM big"
    c.clearCache
    for suf in ["", "-journal"] do
      let f : System.FilePath := p.toString ++ suf
      if ← (f.pathExists : IO Bool) then (IO.FS.removeFile f : IO Unit)
    pure (size > 2147483648 && tail == #[2148, 2149, 100000] && last == some "0102" &&
      n == some 2151)

def main (args : List String) : IO UInt32 := do
  let run : TestM Unit := do
    probes
    fidelity
    noFunctions
    if args.contains "--large" then largeFile
  let ((), r) ← run.run {}
  finish "probes" r

end Test.Probe
