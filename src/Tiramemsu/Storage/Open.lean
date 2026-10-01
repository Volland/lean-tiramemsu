/-
Opening a format-1 file, in Rust's order: a writer connection with `synchronous = NORMAL` and
`recursive_triggers = ON`; `BEGIN IMMEDIATE`; create (no objects other than `sqlite_*`) or
check (`meta`, `format_version`, every counter); `COMMIT`, or `ROLLBACK` on any failure, so a
failed open leaves the file as it was; then `journal_mode = WAL`. No `PRAGMA optimize`: the
Lean build never asks SQLite to plan a query (listed deviation). Shell module.
-/
import Tiramemsu.Sqlite.Store
import Tiramemsu.Storage.Ddl
import Tiramemsu.Storage.Meta

namespace Tiramemsu.Storage

open Tiramemsu.Sqlite Tiramemsu.Store

--# @lat: [[codec#Storage Format 1#Meta And Open]]

abbrev OpenM := ExceptT OpenError IO

def liftSql {α : Type} (x : SqlM α) : OpenM α := do
  match ← x.run with
  | .ok a => pure a
  | .error e => throw (.store e)

/-- Creates every format-1 object and the initial `meta` rows (inside the open transaction). -/
def createFormat1 (c : Conn) (ddl : Array String := ddlV1) : SqlM Unit := do
  for stmt in ddl do c.exec stmt
  for (k, v) in initialMeta do
    c.run "INSERT INTO meta(key, value) VALUES (CAST(? AS TEXT), ?)" #[.text k, .int v]

/-- Checks an existing file: `meta` with a supported `format_version` and every counter. -/
def check (c : Conn) (path : System.FilePath) : OpenM Unit := do
  let hasMeta ← liftSql <| c.queryOne
    "SELECT count(*) FROM sqlite_schema WHERE type = 'table' AND name = 'meta'" #[] (colInt! · 0)
  if hasMeta.getD 0 == 0 then throw (.foreignFile path.toString)
  let found ← liftSql <| c.queryOne "SELECT value FROM meta WHERE key = 'format_version'" #[] (colInt! · 0)
  match found with
  | none => throw (.foreignFile path.toString)
  | some v =>
    -- format 1 has no migrations: older and newer versions are both rejected
    if v != formatVersion then throw (.formatVersion v formatVersion)
  for k in metaKeys do
    let row ← liftSql <| c.queryOne "SELECT value FROM meta WHERE key = CAST(? AS TEXT)" #[.text k] (colInt! · 0)
    if row.isNone then throw (.missingCounter k)

/-- Opens (creating or checking) the database at `path`. `ddl` replaces the format-1 statements
in tests only (to make initialization fail part-way). -/
def openFile (path : System.FilePath) (opts : ConnOptions := {}) (ddl : Array String := ddlV1) :
    IO (Except OpenError Sqlite.Store) := do
  let r : OpenM Sqlite.Store := do
    let c ← liftSql (openWriter path opts (wal := false))
    liftSql c.beginImmediate
    let body : OpenM Unit := do
      let objects ← liftSql <| c.queryOne
        "SELECT count(*) FROM sqlite_schema WHERE name NOT LIKE 'sqlite_%'" #[] (colInt! · 0)
      if objects.getD 0 == 0 then liftSql (createFormat1 c ddl) else check c path
    let res ← (liftM (ExceptT.run body) : OpenM (Except OpenError Unit))
    match res with
    | .ok () => liftSql c.commit
    | .error e =>
      let _ ← (c.rollback.run : IO _)
      c.clearCache
      throw e
    liftSql (c.exec "PRAGMA journal_mode = WAL")
    pure { path, opts, writer := ← IO.mkRef (some c), txState := ← IO.mkRef {}, idle := ← IO.mkRef #[] }
  r.run

end Tiramemsu.Storage
