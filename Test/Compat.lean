/-
The compatibility test: opening and closing a file written by the pinned Rust build with the
Lean build, without writes, leaves its schema, rows, statistics tables and journal mode
unchanged. Runs on a copy of the given Rust-written file.
-/
import Test.Util

namespace Test.Compat

open Test Tiramemsu.Sqlite Tiramemsu.Store

/-- Everything the test compares, read through a plain reader connection. -/
def snapshot (path : System.FilePath) : SqlM String := do
  let c ← openReader path
  let text (st : SQLite.Stmt) (i : Int32) : SqlM String := do return (← colText st i).getD "NULL"
  let schema ← c.queryAll
    "SELECT CAST(type AS BLOB), CAST(name AS BLOB), CAST(tbl_name AS BLOB), CAST(ifnull(sql, '') AS BLOB) FROM sqlite_master ORDER BY rowid"
    #[] fun st => do pure s!"{← text st 0}|{← text st 1}|{← text st 2}|{← text st 3}"
  let hasStat (t : String) : SqlM Bool := do
    return (← c.queryOne "SELECT 1 FROM sqlite_master WHERE name = ?" #[.text t] (fun _ => pure ())).isSome
  let stat1 ← if ← hasStat "sqlite_stat1" then
      c.queryAll "SELECT CAST(tbl AS BLOB), CAST(ifnull(idx, '') AS BLOB), CAST(stat AS BLOB) FROM sqlite_stat1 ORDER BY 1, 2"
        #[] fun st => do pure s!"{← text st 0}|{← text st 1}|{← text st 2}"
    else pure #[]
  let stat4 ← if ← hasStat "sqlite_stat4" then
      c.queryAll "SELECT CAST(tbl || '|' || ifnull(idx, '') || '|' || neq || '|' || nlt || '|' || ndlt || '|' || hex(sample) AS BLOB) FROM sqlite_stat4 ORDER BY 1"
        #[] fun st => text st 0
    else pure #[]
  let jm ← c.queryOne "SELECT CAST(journal_mode AS BLOB) FROM pragma_journal_mode" #[] (text · 0)
  let rows := s!"{reprStr (← dumpMeta c)}\n{reprStr (← dumpTerms c)}\n{reprStr (← dumpTxs c)}\n" ++
    s!"{reprStr (← dumpTriples c)}\n{reprStr (← dumpVolatile c)}\n{reprStr (← dumpPredMulti c)}"
  c.clearCache
  pure s!"schema {schema}\nstat1 {stat1}\nstat4 {stat4.size} {hash stat4.toList}\njournal {jm}\n{rows}"

def main (args : List String) : IO UInt32 := do
  let some src := args.head? | IO.eprintln "usage: tiramemsu-tests compat <rust-written.db>"; return 2
  let copy ← freshPath "compat"
  copyDb src copy
  let res ← (do
    let before ← snapshot copy
    let st ← Store.open copy
    let _ ← (ReadStore.counter "format_version" : SqliteM _) st   -- a read, no write
    st.close
    let after ← snapshot copy
    let stats := (before.splitOn "\n").take 3
    pure (before == after, stats) : SqlM _).run
  match res with
  | .ok (true, stats) =>
    IO.println s!"compat: Rust-written file unchanged by open and close ({String.intercalate "; " (stats.map (·.take 60 |>.toString))})"
    pure 0
  | .ok (false, _) => IO.eprintln "FAIL compat: the file changed"; pure 1
  | .error e => IO.eprintln s!"FAIL compat: {e}"; pure 1

end Test.Compat
