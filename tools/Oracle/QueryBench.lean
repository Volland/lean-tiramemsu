/-
Report-only query benchmarks against the pinned Rust build (D14): point lookups, 2-hop
lookups, an acyclic basic graph pattern and paths on the benchmark fixture, each timed through
both drivers' `m3.*` operations (wall clock, median of several rounds, driver protocol
included), with equal results checked. Ratios never fail the run. Tooling only.
-/
import Oracle.Bench
import Oracle.Canon
import Tiramemsu.Shell.IrJson

namespace Oracle.QueryBench

open Tiramemsu Tiramemsu.Json Tiramemsu.IR Tiramemsu.Codec Tiramemsu.Shell Oracle

--# @lat: [[query#Differential Query Oracle]]

def bv (s : String) : Value := .iri s!"http://b/{s}"
def tpq (s p o : TermOrVar) : Op := .triple { s, p, o }
def var (n : String) : TermOrVar := .var n
def cst (s : String) : TermOrVar := .const (bv s)

def workloads : List (String × String × Json) :=
  let q (o : Op) : Json := .obj #[("query", irQueryJ { root := o })]
  [("point lookup", "m3.execute", q (tpq (cst "n42") (cst "name") (var "x"))),
   ("2-hop lookup", "m3.execute", q (.join [tpq (cst "n42") (cst "knows") (var "y"), tpq (var "y") (cst "name") (var "z")])),
   ("acyclic BGP", "m3.execute", q (.join [tpq (var "a") (cst "type") (cst "C3"), tpq (var "a") (cst "knows") (var "b"),
      tpq (var "b") (cst "name") (var "n")])),
   ("rare join", "m3.execute", q (.join [tpq (var "a") (cst "ceo") (var "c"), tpq (var "a") (cst "knows") (var "b")])),
   ("path REACH knows{1,3}", "m3.path", .obj #[("start", valueJ (bv "n42")), ("text", .str "<http://b/knows>{1,3}"), ("mode", .str "REACH")]),
   ("path TRAIL knows+ (2 hops)", "m3.path", .obj #[("start", valueJ (bv "n42")), ("text", .str "<http://b/knows>+"),
      ("mode", .str "TRAIL"), ("maxHops", .int 2)])]

def timeCalls (d : Driver) (op : String) (args : Json) (reps : Nat) : IO (Nat × Outcome) := do
  let t0 ← IO.monoNanosNow
  let mut last := Outcome.err "none" ""
  for _ in [0:reps] do
    last ← d.call op args
  let t1 ← IO.monoNanosNow
  return ((t1 - t0) / reps, last)

def median (xs : List Nat) : Nat := (xs.mergeSort (· ≤ ·)).getD (xs.length / 2) 0

def main (n reps rounds : Nat) (out : String) : IO UInt32 := do
  let dir : System.FilePath := ".oracle" / "work"
  IO.FS.createDirAll dir
  let path := dir / s!"bench-query-{n}.db"
  let rust ← startRust
  let lean ← startLean
  buildBenchFixture rust path n
  let openArgs := Json.obj #[("path", .str path.toString)]
  let _ ← rust.call! "m3.open" openArgs
  let _ ← lean.call! "m3.open" openArgs
  let mut lines : Array String := #[s!"# Query benchmarks (report-only, D14)", "",
    s!"Fixture: {n} nodes (about {11 * n} statements); {reps} calls per round, median of {rounds} rounds; " ++
      "times per call in microseconds, driver protocol included.", "",
    "| Workload | Rust µs | Lean µs | Lean/Rust | Equal |", "|---|---|---|---|---|"]
  let mut mismatches := 0
  for (name, op, args) in workloads do
    let mut rs := []
    let mut ls := []
    let mut ro := Outcome.err "none" ""
    let mut lo := Outcome.err "none" ""
    for _ in [0:rounds] do
      let (r, o1) ← timeCalls rust op args reps
      let (l, o2) ← timeCalls lean op args reps
      rs := r :: rs
      ls := l :: ls
      ro := o1
      lo := o2
    let unordered := if op == "m3.execute" then ["rows"] else []
    let eq := sameOutcome unordered lo ro
    if !eq then mismatches := mismatches + 1
    let (r, l) := (median rs, median ls)
    let ratio := if r == 0 then "-" else s!"{(l * 100 / r : Nat).toFloat / 100}"
    lines := lines.push s!"| {name} | {r / 1000} | {l / 1000} | {ratio} | {if eq then "yes" else "NO"} |"
  rust.stop
  lean.stop
  let text := "\n".intercalate lines.toList ++ "\n"
  IO.FS.createDirAll (System.FilePath.mk out |>.parent |>.getD ".")
  IO.FS.writeFile out text
  IO.println text
  pure (if mismatches == 0 then 0 else 1)

end Oracle.QueryBench
