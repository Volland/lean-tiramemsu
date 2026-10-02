/-
`oracle`: the differential harness and the report-only benchmark.

  oracle test                          harness unit tests (canonicalization, deviations, bench exit)
  oracle store [--seeds N] [--ops M]   M2 store differential (random scripts, cross-open)
  oracle scenario <file.json>...       runs comparison scenarios over shared files
  oracle fixture <db> [--seed S] [--txs K]   writes a deterministic Rust fixture file
  oracle bench --n N [--out DIR]       benchmark; report in DIR (default oracle/bench)
  oracle interchange [--seed S] [--values N]   file interchange with the Rust build
  oracle codec bench [--n N] [--out FILE]   report-only parse/print throughput against Rust
  oracle codec smoke                   codec mode on the Rust unit-test values
  oracle codec fuzz [--seed S] [--doubles N] [--parse N] [--values N] [--dates N]
                    [--decode N] [--numbers N]   differential codec fuzzing
-/
import Oracle.Tests
import Oracle.Fixture
import Oracle.Codec
import Oracle.Interchange
import Oracle.Store
import Oracle.Query
import Oracle.QueryBench

open Oracle

def pinCommit : IO String := do
  let lines := (← IO.FS.readFile ("oracle" / "RUST_PIN")).splitOn "\n"
  match lines.find? (·.startsWith "commit") with
  | some l => pure ((l.splitOn "=").getLast!.trimAscii.toString)
  | none => pure "unknown"

def flag (args : List String) (name : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def runScenarios (files : List String) : IO UInt32 := do
  let reg ← loadDeviations ("oracle" / "deviations.toml")
  let rust ← startRust
  let lean ← startLean
  let mut failures := 0
  for f in files do
    let sc ← Scenario.load f
    let r ← runScenario rust lean reg sc
    for a in r.accepted do IO.println s!"  {a}"
    for s in r.skipped do IO.println s!"  skipped: {s}"
    for x in r.failures do IO.eprintln s!"FAIL {x}"
    IO.println s!"scenario {sc.name}: {r.compared} compared step(s), {r.accepted.size} accepted deviation(s), {r.skipped.size} skipped, {r.failures.size} failure(s)"
    failures := failures + r.failures.size
  rust.stop
  lean.stop
  return if failures == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["test"] => Oracle.Tests.main
  | "store" :: rest => Oracle.Store.main rest
  | "query" :: rest => Oracle.Query.main rest
  | "bench-query" :: rest =>
    let out := match rest.dropWhile (· != "--out") with
      | _ :: d :: _ => d
      | _ => "oracle/bench/query.md"
    Oracle.QueryBench.main (flag rest "--n" 1000) (flag rest "--reps" 20) (flag rest "--rounds" 5) out
  | "scenario" :: files => if files.isEmpty then pure 2 else runScenarios files
  | "fixture" :: path :: rest =>
    let rust ← startRust
    let n ← writeFixture rust path (flag rest "--seed" 1) (flag rest "--txs" 50)
    rust.stop
    IO.println s!"fixture {path}: {n} committed transaction(s)"
    pure 0
  | ["codec", "smoke"] =>
    let rust ← startRust
    let r ← Oracle.Codec.smoke rust
    rust.stop
    pure r
  | "codec" :: "fuzz" :: rest =>
    let rust ← startRust
    let r ← Oracle.Codec.fuzz rust (flag rest "--seed" 1) (flag rest "--doubles" 100000)
      (flag rest "--parse" 20000) (flag rest "--values" 20000) (flag rest "--dates" 20000)
      (flag rest "--decode" 100000) (flag rest "--numbers" 20000)
    rust.stop
    pure r
  | "codec" :: "bench" :: rest =>
    let rust ← startRust
    let n := flag rest "--n" 100000
    let out := match rest.dropWhile (· != "--out") with
      | _ :: d :: _ => d
      | _ => s!"oracle/bench/codec-{n}.md"
    let r ← Oracle.Codec.bench rust n (flag rest "--seed" 1) out
    rust.stop
    pure r
  | "interchange" :: rest =>
    let rust ← startRust
    let lean ← startLean
    let r ← Oracle.Interchange.run rust lean (flag rest "--seed" 1) (flag rest "--values" 300)
    rust.stop
    lean.stop
    pure r
  | "bench" :: rest =>
    let out := match rest.dropWhile (· != "--out") with
      | _ :: d :: _ => d
      | _ => "oracle/bench"
    runBench (flag rest "--n" 100000) (← pinCommit) out
  | _ =>
    IO.eprintln "usage: oracle test | scenario <file>... | fixture <db> [--seed S] [--txs K] | bench --n N [--out DIR] | codec smoke | codec fuzz [--seed S] [--doubles N] [--parse N] [--values N] [--dates N] [--decode N] [--numbers N]"
    pure 2
