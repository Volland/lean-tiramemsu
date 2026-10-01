/-
Test utilities: checks with reporting, scratch files, format-1 database fixtures.
-/
import Tiramemsu

namespace Test

open Tiramemsu.Sqlite Tiramemsu.Store

/-- Accumulated test results. -/
structure Report where
  passed : Nat := 0
  failed : Array String := #[]
  notes : Array String := #[]

abbrev TestM := StateT Report IO

def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit := do
  if ok then modify fun r => { r with passed := r.passed + 1 }
  else
    let msg := if detail.isEmpty then name else s!"{name}: {detail}"
    IO.eprintln s!"FAIL {msg}"
    modify fun r => { r with failed := r.failed.push msg }

def note (msg : String) : TestM Unit := do
  IO.println s!"  note: {msg}"
  modify fun r => { r with notes := r.notes.push msg }

def checkEq {α : Type} [BEq α] [Repr α] (name : String) (got want : α) : TestM Unit :=
  check name (got == want) s!"got {reprStr got}, want {reprStr want}"

/-- Runs a SQL action; a failure becomes a test failure and `none`. -/
def sql? {α : Type} (name : String) (x : SqlM α) : TestM (Option α) := do
  match ← x.run with
  | .ok a => pure (some a)
  | .error e => check name false (toString e); pure none

/-- Prints the summary and returns the exit code. -/
def finish (title : String) (r : Report) : IO UInt32 := do
  IO.println s!"{title}: {r.passed} passed, {r.failed.size} failed"
  pure (if r.failed.isEmpty then 0 else 1)

/-- The scratch directory for test databases (ignored by git). -/
def scratchDir : IO System.FilePath := do
  let d : System.FilePath := "testdata" / "tmp"
  IO.FS.createDirAll d
  pure d

/-- A fresh database path (any old file and its WAL/SHM are removed). -/
def freshPath (name : String) : IO System.FilePath := do
  let p := (← scratchDir) / s!"{name}.db"
  for suf in ["", "-wal", "-shm", "-journal"] do
    let f : System.FilePath := p.toString ++ suf
    if ← f.pathExists then IO.FS.removeFile f
  pure p

/-- The format-1 DDL fixture (extracted from an empty database made by the pinned Rust build). -/
def schemaFixture : System.FilePath := "testdata" / "format1-schema.sql"

/-- Creates a format-1 database at `path` from the schema fixture. -/
def createFormat1 (path : System.FilePath) : SqlM Unit := do
  let ddl ← (IO.FS.readFile schemaFixture : IO String)
  let c ← openWriter path
  c.exec "BEGIN IMMEDIATE"
  c.exec ddl
  c.exec "COMMIT"
  c.clearCache

/-- A fresh format-1 database. -/
def freshFormat1 (name : String) : IO System.FilePath := do
  let p ← freshPath name
  match ← (createFormat1 p).run with
  | .ok () => pure p
  | .error e => throw (IO.userError s!"cannot create {p}: {e}")

/-- Copies a database file with its WAL (for runs on copies of the same file). -/
def copyDb (src dst : System.FilePath) : IO Unit := do
  for suf in ["", "-wal", "-shm"] do
    let d : System.FilePath := dst.toString ++ suf
    if ← d.pathExists then IO.FS.removeFile d
  for suf in ["", "-wal"] do
    let s : System.FilePath := src.toString ++ suf
    if ← s.pathExists then IO.FS.writeBinFile (dst.toString ++ suf) (← IO.FS.readBinFile s)

/-- Loads the committed contents of a database into a model state (test-only, plain SQL). -/
def loadModelState (path : System.FilePath) : SqlM ModelState := do
  let c ← openReader path
  let st : ModelState := {
    triples := (← dumpTriples c).toList, terms := (← dumpTerms c).toList,
    txs := (← dumpTxs c).toList, counters := (← dumpMeta c).toList,
    volatile := (← dumpVolatile c).toList, predMulti := (← dumpPredMulti c).toList }
  c.clearCache
  pure st

end Test
