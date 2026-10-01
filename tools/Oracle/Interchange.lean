/-
File interchange with the pinned Rust build (storage-format and term-dictionary specs):

- the `sqlite_schema` rows of fresh files created by each build are identical;
- the same values interned in the same order give equal `term` tables, `num` bits included;
- a Rust fixture (every tag, the literal edge cases, retracted statements) decodes to the same
  values in both builds, with or without SQLite's planner statistics;
- a Lean-created file opens in Rust without error or migration and decodes alike;
- opening and closing a Rust file with the Lean build leaves every table unchanged.
Tooling only.
-/
import Oracle.Codec
import Oracle.Fixture
import Tiramemsu.Sqlite.Conn

namespace Oracle.Interchange

open Tiramemsu.Json Tiramemsu.Codec Oracle.Codec

--# @lat: [[codec#Differential Codec Oracle]]

def fresh (name : String) : IO System.FilePath := do
  let d : System.FilePath := ".oracle" / "work" / "interchange"
  IO.FS.createDirAll d
  let p := d / s!"{name}.db"
  for suf in ["", "-wal", "-shm"] do
    let f : System.FilePath := p.toString ++ suf
    if ← f.pathExists then IO.FS.removeFile f
  pure p

def pathJ (p : System.FilePath) : Json := .obj #[("path", .str p.toString)]

/-- The schema rows (`type, name, tbl_name, sql`) other than SQLite's own `sqlite_*` objects. -/
def schemaRows (p : System.FilePath) : IO (Array String) := do
  let r ← (do
    let c ← Tiramemsu.Sqlite.openReader p
    let rows ← c.queryAll
      ("SELECT CAST(type || '|' || name || '|' || tbl_name || '|' || ifnull(sql, '') AS BLOB) " ++
       "FROM sqlite_schema WHERE name NOT LIKE 'sqlite\\_%' ESCAPE '\\' ORDER BY rowid") #[]
      (Tiramemsu.Sqlite.colText · 0)
    c.clearCache
    pure (rows.filterMap id) : Tiramemsu.Sqlite.SqlM _).run
  match r with
  | .ok rs => pure rs
  | .error e => throw (IO.userError s!"schema of {p}: {e}")

def hasStats (p : System.FilePath) : IO Bool := do
  let r ← (do
    let c ← Tiramemsu.Sqlite.openReader p
    let n ← c.queryOne "SELECT count(*) FROM sqlite_schema WHERE name = 'sqlite_stat1'" #[] (Tiramemsu.Sqlite.colInt! · 0)
    c.clearCache
    pure n : Tiramemsu.Sqlite.SqlM _).run
  pure (match r with | .ok (some n) => n > 0 | _ => false)

/-- The values every interchange step interns: the spec edge cases and seeded random values. -/
def corpus (seed n : Nat) : Array Value := Id.run do
  let fixed : Array Value := #[.iri "https://example.org/alice", .iri "urn:x:abcdefghij",
    .str "urn:x:abcdefghij", .str "a twenty-byte string!", .str "NUL\x00inside a long one",
    .str "𝄞 musical symbol G clef", .langStr "colour" "en-GB", .langStr "hi" "en",
    .typed "POINT(1 2)" "http://www.opengis.net/ont/geosparql#wktLiteral",
    .typed "5" "http://www.w3.org/2001/XMLSchema#int", .int (2 ^ 59), .int (-(2 ^ 59) - 1),
    .double ⟨0x3FF0000000000000⟩, .double ⟨0x8000000000000000⟩, .double ⟨0⟩, .double ⟨1⟩,
    .double ⟨0x7FF8000000000000⟩, .double ⟨0x7FF0000000000001⟩, .double ⟨0x7FF0000000000000⟩,
    .double ⟨0x000FFFFFFFFFFFFF⟩, .decimal "0.10", .decimal "-0.0", .decimal "123456789.000000001",
    .typed "abc" xsdInteger, .typed "2026-02-30" xsdDate, .typed "12000-01-01T00:00:00Z" xsdDateTime,
    .typed "1e3" xsdDecimal, .typed "-NaN" xsdDouble, .iri "urn:tiramemsu:node:007"]
  let (rand, _) := (do
    let mut xs := #[]
    for _ in [0:n] do xs := xs.push (← randValue)
    return xs : RngM (Array Value)).run ⟨seed.toUInt64 + 11⟩
  return fixed ++ rand

structure Result where
  checks : Nat := 0
  failures : Array String := #[]

def Result.check (r : Result) (name : String) (ok : Bool) (detail : String := "") : Result :=
  { checks := r.checks + 1,
    failures := if ok then r.failures else r.failures.push (if detail.isEmpty then name else s!"{name}: {detail.take 400}") }

def run (rust lean : Driver) (seed n : Nat) : IO UInt32 := do
  let mut r : Result := {}
  -- 1. fresh files: identical schema rows
  let rs ← fresh "rust-schema"
  let ls ← fresh "lean-schema"
  let _ ← rust.call! "open" (pathJ rs); let _ ← rust.call! "close"
  let _ ← lean.call! "open" (pathJ ls); let _ ← lean.call! "close"
  let a ← schemaRows rs
  let b ← schemaRows ls
  r := r.check "schema dump matches Rust (sqlite_schema, creation order)" (a == b && a.size == 28)
    s!"rust {a.size} rows, lean {b.size} rows"
  -- 2. the same values interned in the same order: equal term tables
  let vals := corpus seed n
  let vj := Json.arr (vals.map Tiramemsu.Shell.valueJ)
  let rt ← fresh "rust-terms"
  let lt ← fresh "lean-terms"
  let ridsJ ← rust.call! "termIntern" (.obj #[("path", .str rt.toString), ("values", vj)])
  let lidsJ ← lean.call! "termIntern" (.obj #[("path", .str lt.toString), ("values", vj)])
  r := r.check "interned ids match Rust" ((norm ridsJ).compress == (norm lidsJ).compress)
    s!"rust {ridsJ.compress.take 300} lean {lidsJ.compress.take 300}"
  let rdump ← rust.call! "open" (pathJ rt) *> rust.call! "rawDump"
  let _ ← rust.call! "close"
  let ldump ← rust.call! "open" (pathJ lt) *> rust.call! "rawDump"
  let _ ← rust.call! "close"
  let rterm := (rdump.get? "term").getD .null
  let lterm := (ldump.get? "term").getD .null
  r := r.check "term tables equal row by row, num bits included" (rterm.compress == lterm.compress)
    s!"rust {rterm.compress.take 300} lean {lterm.compress.take 300}"
  r := r.check "meta equal" ((rdump.get? "meta").map (·.compress) == (ldump.get? "meta").map (·.compress))
  -- 3. a Rust fixture with statements and the edge values decodes alike in both builds
  let rf ← fresh "rust-fixture"
  let _ ← writeFixture rust rf seed 40
  let _ ← rust.call! "termIntern" (.obj #[("path", .str rf.toString), ("values", vj)])
  let _ ← rust.call! "open" (pathJ rf); let _ ← rust.call! "close"
  let stats ← hasStats rf
  let before ← rust.call! "open" (pathJ rf) *> rust.call! "rawDump"
  let _ ← rust.call! "close"
  let rdec ← rust.call! "decodeFile" (pathJ rf)
  let ldec ← lean.call! "decodeFile" (pathJ rf)
  r := r.check s!"Rust fixture decodes alike (sqlite_stat1 present: {stats})" ((norm rdec).compress == (norm ldec).compress)
    s!"rust {(norm rdec).compress.take 300} lean {(norm ldec).compress.take 300}"
  let after ← rust.call! "open" (pathJ rf) *> rust.call! "rawDump"
  let _ ← rust.call! "close"
  r := r.check "Lean open and close leave a Rust file's tables unchanged" (before.compress == after.compress)
  -- 4. a Lean-created file opens in Rust without error or migration and decodes alike
  let lt2 ← fresh "lean-only"
  let _ ← lean.call! "termIntern" (.obj #[("path", .str lt2.toString), ("values", vj)])
  let lstats ← hasStats lt2
  r := r.check "the Lean build writes no planner statistics" (!lstats)
  let ldec2 ← lean.call! "decodeFile" (pathJ lt2)
  let rdec2 ← rust.call "decodeFile" (pathJ lt2)
  match rdec2 with
  | .ok j =>
    r := r.check s!"Lean file decodes alike in Rust (sqlite_stat1 present: {lstats})" ((norm j).compress == (norm ldec2).compress)
      s!"rust {(norm j).compress.take 300} lean {(norm ldec2).compress.take 300}"
  | .err c m => r := r.check "Rust opens a Lean-created file" false s!"{c}: {m}"
  let fv ← rust.call! "open" (pathJ lt2) *> rust.call! "rawDump"
  let _ ← rust.call! "close"
  r := r.check "no migration: format_version stays 1" ((fv.get? "meta").any fun m => (m.compress.splitOn "[\"format_version\",1]").length > 1)
  for f in r.failures do IO.eprintln s!"FAIL interchange: {f}"
  IO.println s!"interchange: {r.checks} check(s), {r.failures.size} failure(s); {vals.size} values, {(match ldec.get? "triples" with | some (.arr t) => t.size | _ => 0)} fixture statements"
  return if r.failures.isEmpty then 0 else 1

end Oracle.Interchange
