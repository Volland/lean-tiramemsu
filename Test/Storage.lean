/-
Storage-format tests: the schema of a Lean-created file, STRICT tables, every never-forget
trigger against raw SQLite, the open rules (absent, zero-length, empty-schema, foreign, newer,
older, missing counter, failed initialization), reserved names, WAL, counters after reopen.
-/
import Test.Util
import Test.Schema

namespace Test.Storage

open Test Tiramemsu.Sqlite Tiramemsu.Store Tiramemsu.Storage Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[codec#Tests]]

def openOk (p : System.FilePath) : TestM (Option Store) := do
  match ← openFile p with
  | .ok st => pure (some st)
  | .error e => check s!"open {p}" false (toString e); pure none

/-- A raw connection (no engine checks), as a plain SQLite tool would use. -/
def raw (p : System.FilePath) : SqlM Conn := openWriter p (wal := false)

def errMsg (x : SqlM Unit) : IO String := do
  match ← x.run with
  | .ok () => pure ""
  | .error e => pure (toString e)

def fileBytes (p : System.FilePath) : IO ByteArray := IO.FS.readBinFile p

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def count (c : Conn) (sql : String) : SqlM Int64 := do
  pure ((← c.queryOne sql #[] (colInt! · 0)).getD (-1))

def run : TestM Unit := do
  -- creating a database
  let p ← freshPath "storage-fresh"
  if let some st ← openOk p then
    let c ← st.conn |>.run
    match c with
    | .ok c =>
      let rows ← sql? "meta rows" (c.queryAll "SELECT CAST(key AS BLOB), value FROM meta ORDER BY rowid" #[]
        fun st => do pure ((← colText st 0).getD "", ← colInt! st 1))
      checkEq "fresh counters in Rust order" rows (some initialMeta)
      for t in ["term", "tx", "triple", "volatile", "pred_multi"] do
        checkEq s!"{t} is empty" (← sql? t (count c s!"SELECT count(*) FROM {t}")) (some 0)
      let jm ← sql? "journal mode" (c.queryOne "SELECT CAST(journal_mode AS BLOB) FROM pragma_journal_mode" #[] (colText · 0))
      checkEq "WAL after open (writer)" jm (some (some (some "wal")))
      let names ← sql? "names" (c.queryAll "SELECT CAST(name AS BLOB) FROM sqlite_schema" #[] (colText · 0))
      let names := (names.getD #[]).filterMap id
      check "reserved names are absent" (names.all fun n => !reservedNames.contains n && !n.startsWith reservedPrefix)
    | .error e => check "writer" false (toString e)
    st.close
    -- the schema text equals the fixture (equal to Rust's, checked by scripts/check-schema-fixture.sh)
    match ← (Test.Schema.dump p).run with
    | .ok d => checkEq "schema equals the Rust format-1 fixture" d (← IO.FS.readFile schemaFixture)
    | .error e => check "schema dump" false (toString e)
    match ← (do let r ← openReader p; let j ← r.queryOne "SELECT CAST(journal_mode AS BLOB) FROM pragma_journal_mode" #[] (colText · 0); r.clearCache; pure j : SqlM _).run with
    | .ok j => checkEq "WAL after open (reader)" j (some (some "wal"))
    | .error e => check "reader" false (toString e)
  -- STRICT and the triggers, against raw SQLite
  if let some st ← openOk (← freshPath "storage-triggers") then
    let p := st.path
    st.close
    let r ← (do
      let c ← raw p
      c.exec "INSERT INTO term(id, tag, lex) VALUES (1, 0, 'urn:x:a')"
      c.exec "INSERT INTO tx(t, instant) VALUES (1, 100)"
      c.exec "INSERT INTO triple(eid, s, p, o, t_add) VALUES (19, 1, 16, 21, 1)"
      c.exec "INSERT INTO triple(eid, s, p, o, t_add, t_ret, ret_kind) VALUES (35, 1, 16, 37, 1, 9, 0)"
      pure c : SqlM Conn).run
    match r with
    | .error e => check "seed rows" false (toString e)
    | .ok c =>
      let before ← (do pure (← dumpTerms c, ← dumpTxs c, ← dumpTriples c) : SqlM _).run
      let cases : List (String × String × String) := [
        ("STRICT rejects TEXT in triple.s", "INSERT INTO triple(eid, s, p, o, t_add) VALUES (51, 'x', 16, 21, 1)", "cannot store TEXT"),
        ("DELETE on triple", "DELETE FROM triple", "tiramemsu: triples are never deleted"),
        ("second retraction", "UPDATE triple SET t_ret = 12 WHERE eid = 35", "tiramemsu: only a single retraction is allowed"),
        ("other triple update", "UPDATE triple SET o = 5 WHERE eid = 19", "tiramemsu: only a single retraction is allowed"),
        ("reused eid", "INSERT OR REPLACE INTO triple(eid, s, p, o, t_add) VALUES (19, 1, 16, 21, 2)", "tiramemsu: eids are never reused"),
        ("reused term id", "REPLACE INTO term(id, tag, lex) VALUES (1, 0, 'urn:x:b')", "tiramemsu: term ids are never reused"),
        ("reused transaction number", "INSERT OR REPLACE INTO tx(t, instant) VALUES (1, 5)", "tiramemsu: transaction numbers are never reused"),
        ("DELETE on term", "DELETE FROM term", "tiramemsu: terms are never deleted"),
        ("UPDATE on term", "UPDATE term SET lex = 'y'", "tiramemsu: terms are immutable"),
        ("DELETE on tx", "DELETE FROM tx", "tiramemsu: transactions are never deleted"),
        ("UPDATE on tx", "UPDATE tx SET instant = 0", "tiramemsu: transactions are immutable")]
      for (name, sql, msg) in cases do
        let e ← errMsg (c.exec sql)
        check name (has e msg) e
      let after ← (do pure (← dumpTerms c, ← dumpTxs c, ← dumpTriples c) : SqlM _).run
      check "rows unchanged by the rejected writes" (match before, after with
        | .ok a, .ok b => reprStr a == reprStr b
        | _, _ => false)
      checkEq "legal retraction" (← errMsg (c.exec "UPDATE triple SET t_ret = 9, ret_kind = 0 WHERE eid = 19")) ""
      checkEq "meta is not protected" (← errMsg (c.exec "UPDATE meta SET value = value WHERE key = 'last_t'")) ""
      c.clearCache
  -- open rules
  let zero ← freshPath "storage-zero"
  IO.FS.writeFile zero ""
  if let some st ← openOk zero then
    check "zero-length file initialized" ((← (ReadStore.counter (m := SqliteM) "next_term" st).run) == .ok (some 1))
    st.close
  let empty ← freshPath "storage-empty"
  let _ ← (do let c ← raw empty; c.exec "CREATE TABLE t(x)"; c.exec "DROP TABLE t"; c.clearCache : SqlM Unit).run
  if let some st ← openOk empty then
    check "empty-schema file initialized" ((← (ReadStore.counter (m := SqliteM) "format_version" st).run) == .ok (some 1))
    st.close
  let foreign ← freshPath "storage-foreign"
  let _ ← (do let c ← raw foreign; c.exec "CREATE TABLE customers(id INTEGER)"; c.clearCache : SqlM Unit).run
  match ← openFile foreign with
  | .error (.foreignFile _) => pure ()
  | _ => check "unrelated SQLite database is ForeignFile" false
  let objs ← (do let r ← openReader foreign; let n ← r.queryAll "SELECT CAST(name AS BLOB) FROM sqlite_schema" #[] (colText · 0); r.clearCache; pure n : SqlM _).run
  check "foreign file still holds only customers" (match objs with
    | .ok n => n.toList.filterMap id == ["customers"]
    | _ => false)
  for (name, v) in [("newer", 2), ("older", 0)] do
    let f ← freshPath s!"storage-{name}"
    if let some st ← openOk f then st.close
    let _ ← (do let c ← raw f; c.exec s!"UPDATE meta SET value = {v} WHERE key = 'format_version'"; c.exec "PRAGMA wal_checkpoint(TRUNCATE)"; c.clearCache : SqlM Unit).run
    let b ← fileBytes f
    match ← openFile f with
    | .error (.formatVersion found sup) =>
      check s!"file from a {name} build: FormatVersion" (found == v && sup == 1)
    | _ => check s!"file from a {name} build: FormatVersion" false
    check s!"{name} file's bytes are unchanged" ((← fileBytes f) == b)
  let mc ← freshPath "storage-missing"
  if let some st ← openOk mc then st.close
  let _ ← (do let c ← raw mc; c.exec "DELETE FROM meta WHERE key = 'next_stmt'"; c.exec "PRAGMA wal_checkpoint(TRUNCATE)"; c.clearCache : SqlM Unit).run
  let b ← fileBytes mc
  match ← openFile mc with
  | .error (.missingCounter "next_stmt") => pure ()
  | _ => check "missing counter fails the open" false
  check "missing-counter file is unchanged" ((← fileBytes mc) == b)
  let fi ← freshPath "storage-failed-init"
  match ← openFile fi (ddl := Tiramemsu.Storage.ddlV1.push "CREATE TABLE broken(") with
  | .error _ => pure ()
  | .ok st => st.close; check "failed initialization fails the open" false
  let objs ← (do let r ← openReader fi; let n ← count r "SELECT count(*) FROM sqlite_schema"; r.clearCache; pure n : SqlM _).run
  checkEq "failed initialization leaves no object" objs (.ok 0)
  if let some st ← openOk fi then
    check "a later open initializes from scratch" ((← (ReadStore.counter (m := SqliteM) "next_stmt" st).run) == .ok (some 1))
    st.close
  -- counters resume after reopen
  let cr ← freshPath "storage-resume"
  if let some st ← openOk cr then
    let _ ← (do Store.begin st; WriteStore.setCounter (m := SqliteM) "next_term" 57 st; Store.commit st : SqlM Unit).run
    st.close
  if let some st ← openOk cr then
    let cache ← WriterCache.new none
    let r ← (do Store.begin st; let x ← (intern (Value.iri "urn:x:resumed") : CachedM SqliteM _) cache st; Store.commit st; pure x : SqlM _).run
    checkEq "counters resume after reopen" (match r with | .ok (.ok x) => some x.upayload.toNat | _ => none) (some 57)
    st.close
  -- reopen is read-only on data
  let snap ← (Test.Schema.dump cr).run
  if let some st ← openOk cr then st.close
  check "reopen leaves the file's schema and meta unchanged" ((← (Test.Schema.dump cr).run) == snap)

def main : IO UInt32 := do
  let ((), r) ← run.run {}
  finish "storage" r

end Test.Storage
