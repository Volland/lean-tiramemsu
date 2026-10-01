/-
Versions reported by the CLI: the program, the linked SQLite and the storage format.
Shell module (unverified).
-/
import Tiramemsu.Sqlite.Conn

namespace Tiramemsu.Shell

open Tiramemsu.Sqlite

/-- The program version. -/
def programVersion : String := "0.1.0"

/-- The highest storage format version this build supports. -/
def formatVersion : Nat := 1

/-- The version report: program, linked SQLite version, SQLite thread-safety, format. -/
def versionReport (verbose : Bool := false) : SqlM (List String) := do
  let c ← openMemory
  let v ← c.sqliteVersion
  let opts ← c.compileOptions
  let threadsafe := (opts.find? (·.startsWith "THREADSAFE=")).getD "THREADSAFE=?"
  let base := [s!"tiramemsu {programVersion}", s!"sqlite {v}", s!"sqlite-{threadsafe.toLower}",
    s!"format {formatVersion}"]
  pure (if verbose then base ++ opts.toList.map ("sqlite-option " ++ ·) else base)

end Tiramemsu.Shell
