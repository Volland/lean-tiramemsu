/-
The `meta` table of format 1: the format version and the engine counters, with the rows of a
fresh database in Rust's insertion order, and the errors of opening a file.
Shell module.
-/
import Tiramemsu.Store.Types

namespace Tiramemsu.Storage

--# @lat: [[codec#Storage Format 1#Meta And Open]]

/-- The format version this build writes and reads. -/
def formatVersion : Int64 := 1

/-- The `meta` rows of a fresh database, in insertion order. -/
def initialMeta : Array (String × Int64) := #[
  ("format_version", 1), ("next_term", 1), ("next_node", 1), ("next_bnode", 1),
  ("next_stmt", 1), ("last_t", 0), ("last_instant", 0), ("multi_version", 0)]

/-- Every key `meta` must hold. -/
def metaKeys : Array String := initialMeta.map (·.1)

/-- Names reserved for later formats (never created by format 1), and a reserved prefix. -/
def reservedNames : Array String := #["seal_key", "term_fts"]
def reservedPrefix : String := "vec_"

/-- Why a file could not be opened. -/
inductive OpenError where
  /-- A SQLite file with objects but no `meta` table or no `format_version` row. -/
  | foreignFile (path : String)
  /-- A format version other than the supported one. -/
  | formatVersion (found supported : Int64)
  /-- A `meta` table without one of the required keys. -/
  | missingCounter (key : String)
  /-- A storage failure. -/
  | store (e : Tiramemsu.Store.StoreError)
  deriving Repr, Inhabited

def OpenError.code : OpenError → String
  | .foreignFile _ => "ForeignFile"
  | .formatVersion .. => "FormatVersion"
  | .missingCounter _ => "InvalidTerm"
  | .store _ => "Sqlite"

instance : ToString OpenError where
  toString
    | .foreignFile p => s!"not a tiramemsu database: {p}"
    | .formatVersion f s => s!"format version {f} is not supported (this build supports {s})"
    | .missingCounter k => s!"meta table is missing counter {k}"
    | .store e => toString e

end Tiramemsu.Storage
