/-
The format-1 schema fixture: extraction from a database file (`sqlite_master.sql` in rowid
order, without SQLite's internal `sqlite_%` objects such as the planner statistics tables,
plus the `meta` rows in insertion order).
-/
import Test.Util

namespace Test.Schema

open Tiramemsu.Sqlite

def header : String :=
  "-- Format-1 schema fixture, extracted by `tiramemsu-tests schema-dump` from an empty\n" ++
  "-- database created by the pinned Rust build: sqlite_master.sql in rowid order (SQLite's\n" ++
  "-- internal sqlite_% objects excluded), then the initial meta rows.\n"

/-- The SQL text of a string literal. -/
def sqlString (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

/-- The fixture text for a database file. -/
def dump (path : System.FilePath) : SqlM String := do
  let c ← openReader path
  let objs ← c.queryAll
    ("SELECT CAST(sql AS BLOB) FROM sqlite_master WHERE sql IS NOT NULL " ++
     "AND name NOT LIKE 'sqlite\\_%' ESCAPE '\\' ORDER BY rowid") #[] (colText · 0)
  let metaRows ← c.queryAll "SELECT CAST(key AS BLOB), value FROM meta ORDER BY rowid" #[]
    fun st => do pure ((← colText st 0).getD "", ← colInt! st 1)
  c.clearCache
  let stmts := objs.filterMap id |>.map (· ++ ";\n")
  let inserts := renderMeta metaRows
  pure (header ++ String.join stmts.toList ++ String.join inserts.toList)
where
  renderMeta (rows : Array (String × Int64)) : Array String :=
    rows.map fun (k, v) => s!"INSERT INTO meta(key, value) VALUES ({sqlString k}, {v});\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    match ← (dump path).run with
    | .ok s => IO.print s; pure 0
    | .error e => IO.eprintln s!"schema-dump: {e}"; pure 1
  | _ => IO.eprintln "usage: tiramemsu-tests schema-dump <db>"; pure 2

end Test.Schema
