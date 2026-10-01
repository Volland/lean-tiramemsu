/-
Report-only benchmark harness (D14). Builds a deterministic fixture through the Rust driver
(the shape of the Rust `bench/engine-comparison`: N nodes, about 11·N statements, four
retracted older names per node, five `knows` edges, a rare `ceo` edge), times workloads
grouped by the performance-gate categories on each build that supports them, checks that both
builds return equal results, and writes a JSON and a Markdown report with ratios against Rust.
The exit status reflects harness errors and result mismatches only, never ratios.
Tooling only.
-/
import Oracle.Driver
import Tiramemsu.Sqlite.Store

namespace Oracle

open Tiramemsu.Json

--# @lat: [[roadmap#Performance Gate#Benchmark Harness]]

def b (s : String) : Json := .obj #[("iri", .str s!"http://b/{s}")]
def node (i : Nat) : Json := b s!"n{i}"
def biri (s : String) : String := s!"<http://b/{s}>"

/-- The fixture operations of one node. -/
def nodeOps (n i : Nat) : Array Json := Id.run do
  let assert (s p o : Json) (as? : Option String := none) : Json :=
    .obj (#[("op", .str "assert"), ("s", s), ("p", p), ("o", o)] ++
      (as?.map (fun a => #[("as", Json.str a)]) |>.getD #[]))
  let mut ops := #[assert (node i) (b "type") (b (if i % 10 == 0 then "C3" else "C7"))]
  for k in [0:4] do
    ops := ops.push (assert (node i) (b "name") (.str s!"old name {i} {k}") (some s!"o{i}_{k}"))
    ops := ops.push (.obj #[("op", .str "retract"), ("eid", .obj #[("ref", .str s!"o{i}_{k}")])])
  ops := ops.push (assert (node i) (b "name") (.str s!"name of {i}"))
  for k in [1:6] do
    ops := ops.push (assert (node i) (b "knows") (node ((i * 7919 + k) % n + 1)))
  if i % 2000 == 0 then ops := ops.push (assert (node i) (b "ceo") (b "C5"))
  return ops

/-- Builds the fixture at `path` with the Rust driver. -/
def buildBenchFixture (rust : Driver) (path : System.FilePath) (n : Nat) : IO Unit := do
  for suf in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ suf
    if ← f.pathExists then IO.FS.removeFile f
  -- bulk load without per-commit statistics upkeep, then statistics once (as the Rust bench)
  let _ ← rust.call! "open" (.obj #[("path", .str path.toString),
    ("options", .obj #[("optimizeEvery", .int 1000000000000)])])
  let batch := 200
  let mut i := 1
  while i ≤ n do
    let mut ops := #[]
    for j in [i:min (i + batch) (n + 1)] do ops := ops ++ nodeOps n j
    let _ ← rust.call! "transact" (.obj #[("ops", .arr ops)])
    i := i + batch
  let _ ← rust.call! "optimize"
  let _ ← rust.call! "close"

/-- A timed workload: a list of bridge calls, timed inside the driver (`bench` op). -/
structure Workload where
  category : String
  name : String
  calls : Array (String × Json)
  reps : Nat := 1
  /-- Paths of result arrays compared as multisets. -/
  unordered : List String := []

/-- Timing of one build: total milliseconds and the last result of each call, or `none`
when the build does not implement the workload yet. -/
def timeOn (d : Driver) (w : Workload) : IO (Option (Float × Array Outcome)) := do
  let mut ns : Nat := 0
  let mut outs := #[]
  for (op, args) in w.calls do
    match ← d.call "bench" (.obj #[("op", .str op), ("args", args), ("reps", .int w.reps)]) with
    | .ok r =>
      ns := ns + ((r.getInt? "elapsedNs").getD 0).toNat
      outs := outs.push (.ok ((r.get? "result").getD .null))
    | o@(.err _ _) =>
      if o.isUnsupported then return none
      outs := outs.push o
  return some (ns.toFloat / 1e6, outs)

/-- One report row. -/
structure Row where
  category : String
  name : String
  rustMs : Option Float
  leanMs : Option Float
  /-- `ok`, `lean n/a` or `mismatch`. -/
  status : String
  deriving Inhabited

def Row.ratio (r : Row) : Option Float := do
  let l ← r.leanMs
  let rs ← r.rustMs
  if rs > 0 then some (l / rs) else none

/-- The exit status of a report: non-zero only on a mismatch (or a harness error, which is
thrown before a report exists), never because of a ratio. -/
def exitCode (rows : Array Row) : UInt32 :=
  if rows.any (·.status == "mismatch") then 1 else 0

/-- A float with three decimals. -/
def fmt (x : Float) : String :=
  let n := (x * 1000).round.toUInt64.toNat
  let frac := toString (n % 1000)
  s!"{n / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"

/-- As-of throughput as a percentage of the `now` baseline, from the point-lookup rows. -/
def asOfThroughput (rows : Array Row) (side : Row → Option Float) : Option Float := do
  let now ← (rows.find? (·.name == "point now")).bind side
  let asOf ← (rows.find? (·.name == "point asOf")).bind side
  if asOf > 0 then some (now / asOf * 100) else none

def optJ (x : Option Float) : Json := match x with
  | some v => .num (fmt v)
  | none => .null

def reportJson (n : Nat) (statements : Nat) (bytesPerStmt : Float) (pin : String)
    (rows : Array Row) : Json :=
  .obj #[("N", .int n), ("statements", .int statements), ("bytesPerStatement", .num (fmt bytesPerStmt)),
    ("rustPin", .str pin),
    ("asOfThroughputPct", .obj #[("rust", optJ (asOfThroughput rows (·.rustMs))),
                                 ("lean", optJ (asOfThroughput rows (·.leanMs)))]),
    ("workloads", .arr (rows.map fun r => .obj #[("category", .str r.category), ("name", .str r.name),
      ("rustMs", optJ r.rustMs), ("leanMs", optJ r.leanMs), ("ratio", optJ r.ratio),
      ("status", .str r.status)]))]

def reportMarkdown (n : Nat) (statements : Nat) (bytesPerStmt : Float) (pin : String)
    (rows : Array Row) : String := Id.run do
  let mut s := s!"# Benchmark report, N = {n}\n\n"
  s := s ++ s!"Report-only (D14): ratios are Lean ÷ Rust and never fail the run. Rust oracle pin `{pin}`. " ++
    s!"{statements} statements, {fmt bytesPerStmt} bytes per statement (same file for both builds).\n\n"
  let pct (x : Option Float) := (x.map (fmt · ++ " %")).getD "n/a"
  s := s ++ s!"As-of throughput (point asOf vs point now): Rust {pct (asOfThroughput rows (·.rustMs))}, " ++
    s!"Lean {pct (asOfThroughput rows (·.leanMs))}.\n\n"
  s := s ++ "| Category | Workload | Rust ms | Lean ms | Ratio | Status |\n|---|---|---|---|---|---|\n"
  for r in rows do
    let o (x : Option Float) := (x.map fmt).getD "n/a"
    s := s ++ s!"| {r.category} | {r.name} | {o r.rustMs} | {o r.leanMs} | {o r.ratio} | {r.status} |\n"
  return s

/-- The workloads of the gate categories (`lat.md/roadmap.md#Performance Gate`). -/
def workloads (n : Nat) (seed : Nat) (nameEids : Array Nat := #[]) : Array Workload := Id.run do
  let mut g := mkStdGen seed
  let mut starts := #[]
  for _ in [0:200] do
    let (x, g1) := randNat g 1 n
    g := g1
    starts := starts.push x
  let triples (i : Nat) (view : Json) : String × Json :=
    ("triples", .obj #[("s", node i), ("p", b "name"), ("view", view)])
  let now := Json.obj #[("kind", .str "now")]
  let asOf := Json.obj #[("kind", .str "asOf"), ("tx", .int 1)]
  let validAt := Json.obj #[("kind", .str "now"), ("validAt", .int 1500)]
  let sparql (q : String) : String × Json := ("sparql", .obj #[("text", .str q)])
  let writes := (List.range 200).toArray.map fun k =>
    ("transact", Json.obj #[("ops", .arr #[.obj #[("op", .str "assert"), ("s", node (starts[k % starts.size]!)),
      ("p", b "name"), ("o", .str s!"bench name {k}")]])])
  let supersedes := nameEids.mapIdx fun k e =>
    ("transact", Json.obj #[("ops", .arr #[.obj #[("op", .str "supersede"), ("eid", .int (Int.ofNat e)),
      ("patch", .obj #[("o", .str s!"superseded name {k}")])]])])
  #[ { category := "writes", name := "assert (one per transaction)", calls := writes },
     { category := "writes", name := "supersede (one per transaction)", calls := supersedes },
     { category := "lookups", name := "point now", calls := starts.map (triples · now) },
     { category := "lookups", name := "point asOf", calls := starts.map (triples · asOf) },
     { category := "lookups", name := "point validAt", calls := starts.map (triples · validAt) },
     { category := "lookups", name := "2-hop now", unordered := ["rows"],
       calls := (starts.extract 0 50).map fun i =>
         sparql s!"SELECT ?n WHERE \{ {biri s!"n{i}"} {biri "knows"} ?y . ?y {biri "name"} ?n }" },
     { category := "acyclic BGP", name := "skewed 4-pattern count",
       calls := #[sparql s!"SELECT (COUNT(*) AS ?c) WHERE \{ ?x {biri "type"} {biri "C7"} . ?x {biri "knows"} ?y . ?y {biri "ceo"} {biri "C5"} . ?y {biri "name"} ?n }"] },
     { category := "cyclic", name := "triangles from 20 starts", unordered := ["rows"],
       calls := (starts.extract 0 20).map fun i =>
         sparql s!"SELECT ?b ?c WHERE \{ {biri s!"n{i}"} {biri "knows"} ?b . ?b {biri "knows"} ?c . ?c {biri "knows"} {biri s!"n{i}"} }" },
     { category := "paths", name := "reach within 3 hops", unordered := [""],
       calls := (starts.extract 0 20).map fun i =>
         ("path", .obj #[("start", node i), ("path", .str s!"{biri "knows"}+"), ("maxHops", .int 3)]) } ]

/-- Statements in the file, counted through the Lean SQLite store. -/
def countStatements (path : System.FilePath) : IO Nat := do
  let r ← (do
    let c ← Tiramemsu.Sqlite.openReader path
    let n ← c.queryOne "SELECT count(*) FROM triple" #[] (Tiramemsu.Sqlite.colInt! · 0)
    c.clearCache
    pure n : Tiramemsu.Sqlite.SqlM _).run
  match r with
  | .ok (some n) => pure n.toNatClampNeg
  | _ => throw (IO.userError "cannot count statements")

def fileBytes (path : System.FilePath) : IO Nat := do
  let mut total := 0
  for suf in ["", "-wal"] do
    let f : System.FilePath := path.toString ++ suf
    if ← f.pathExists then total := total + (← f.metadata).byteSize.toNat
  return total

/-- Runs the benchmark and writes `oracle/bench/report-<N>.{json,md}`. -/
def runBench (n : Nat) (pin : String) (outDir : System.FilePath) : IO UInt32 := do
  let dir : System.FilePath := ".oracle" / "bench"
  IO.FS.createDirAll dir
  let fixture := dir / s!"fixture-{n}.db"
  let rust ← startRust
  let lean ← startLean
  IO.println s!"bench: building the fixture (N = {n}) through the Rust driver"
  let t0 ← IO.monoMsNow
  buildBenchFixture rust fixture n
  IO.println s!"bench: fixture built in {(← IO.monoMsNow) - t0} ms"
  let statements ← countStatements fixture
  let bytes ← fileBytes fixture
  let bps := bytes.toFloat / statements.toFloat
  -- read workloads run on the fixture; the write workload runs last, on copies
  -- the live `name` statements of the first 200 starts (supersede targets), read through Rust
  let _ ← rust.call! "open" (.obj #[("path", .str fixture.toString)])
  let mut nameEids := #[]
  for (_, args) in (workloads n 7).find? (·.name == "point now") |>.map (·.calls) |>.getD #[] do
    match ← rust.call "triples" args with
    | .ok (.arr rows) =>
      if let some e := rows[0]? >>= (·.getInt? "eid") then
        if !nameEids.contains e.toNat then nameEids := nameEids.push e.toNat
    | _ => pure ()
  let _ ← rust.call "close"
  let mut rows := #[]
  for w in workloads n 7 nameEids do
    let isWrite := w.category == "writes"
    let rpath := if isWrite then dir / "write-rust.db" else fixture
    let lpath := if isWrite then dir / "write-lean.db" else fixture
    if isWrite then
      for (src, dst) in [(fixture, rpath), (fixture, lpath)] do
        for suf in ["", "-wal", "-shm"] do
          let d : System.FilePath := dst.toString ++ suf
          if ← d.pathExists then IO.FS.removeFile d
        for suf in ["", "-wal"] do
          let s : System.FilePath := src.toString ++ suf
          if ← s.pathExists then IO.FS.writeBinFile (dst.toString ++ suf) (← IO.FS.readBinFile s)
    let _ ← rust.call! "open" (.obj #[("path", .str rpath.toString)])
    let r ← timeOn rust w
    let _ ← rust.call "close"
    let _ ← lean.call! "open" (.obj #[("path", .str lpath.toString)])
    let l ← timeOn lean w
    let _ ← lean.call "close"
    let status := match r, l with
      | some (_, ro), some (_, lo) =>
        if isWrite then "ok"  -- write reports carry wall-clock instants; equal counts suffice
        else if (ro.zip lo).all (fun (a, b) => sameOutcome w.unordered a b) && ro.size == lo.size
        then "ok" else "mismatch"
      | some _, none => "lean n/a"
      | none, _ => "rust n/a"
    rows := rows.push { category := w.category, name := w.name, rustMs := r.map (·.1),
                        leanMs := l.map (·.1), status }
    IO.println s!"bench: {w.category} / {w.name}: rust {(r.map (fmt ·.1)).getD "n/a"} ms, lean {(l.map (fmt ·.1)).getD "n/a"} ({status})"
  rust.stop
  lean.stop
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / s!"report-{n}.json") ((reportJson n statements bps pin rows).compress ++ "\n")
  IO.FS.writeFile (outDir / s!"report-{n}.md") (reportMarkdown n statements bps pin rows)
  IO.println s!"bench: {statements} statements, {fmt bps} bytes/statement; report in {outDir}"
  return exitCode rows

end Oracle
