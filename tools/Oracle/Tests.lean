/-
Unit tests of the harness itself: one per canonicalization rule, the deviation matcher,
and the report-only exit status of the benchmark. Tooling only.
-/
import Oracle.Scenario
import Oracle.Bench

namespace Oracle.Tests

open Oracle Tiramemsu.Json

def parse! (s : String) : Json := match Json.parse s with
  | .ok j => j
  | .error e => panic! s!"bad test JSON {s}: {e}"

def eqC (unordered : List String) (a b : String) : Bool :=
  sameOutcome unordered (.ok (parse! a)) (.ok (parse! b))

def main : IO UInt32 := do
  let mut failed := 0
  let mut passed := 0
  let checks : List (String × Bool) := [
    ("keys are sorted", eqC [] "{\"b\":1,\"a\":2}" "{\"a\":2,\"b\":1}"),
    ("2^63-1 equals itself", eqC [] "9223372036854775807" "9223372036854775807"),
    ("2^63-1 differs from 2^63-2", !eqC [] "9223372036854775807" "9223372036854775806"),
    ("integers beyond 2^53 stay exact", !eqC [] "9007199254740993" "9007199254740992"),
    ("unordered rows compare as multisets",
      eqC [""] "[{\"x\":1},{\"x\":2},{\"x\":2}]" "[{\"x\":2},{\"x\":1},{\"x\":2}]"),
    ("multisets keep multiplicity", !eqC [""] "[1,2,2]" "[1,1,2]"),
    ("nested unordered path", eqC ["rows"] "{\"rows\":[1,2],\"vars\":[\"a\",\"b\"]}"
      "{\"vars\":[\"a\",\"b\"],\"rows\":[2,1]}"),
    ("ordered results compare in order", !eqC [] "[1,2]" "[2,1]"),
    ("ordered elsewhere under an unordered path", !eqC ["rows"] "{\"vars\":[\"a\",\"b\"]}" "{\"vars\":[\"b\",\"a\"]}"),
    ("doubles compare by lexical form", eqC [] "1.5e0" "1.5e0" && !eqC [] "1.5" "1.50"),
    ("errors compare by code only",
      sameOutcome [] (.err "Parse" "line 1") (.err "Parse" "at column 3")),
    ("different error codes differ", !sameOutcome [] (.err "Parse" "") (.err "Eval" "")),
    ("result differs from error", !sameOutcome [] (.ok .null) (.err "Parse" ""))]
  for (name, ok) in checks do
    if ok then passed := passed + 1 else failed := failed + 1; IO.eprintln s!"FAIL {name}"
  -- deviation matching against the committed registry
  let reg ← loadDeviations ("oracle" / "deviations.toml")
  let tmPath := Json.obj #[("sql", .str "SELECT * FROM tm_path(1, 'knows+', 'REACH')")]
  let rarray := Json.obj #[("sql", .str "SELECT * FROM rarray(1)")]
  let other := Json.obj #[("sql", .str "SELECT 1")]
  let leanErr : Outcome := .err "Sqlite" "no such table"
  let rustOk : Outcome := .ok (.bool true)
  let devChecks : List (String × Bool) := [
    ("registry has the tm_path entry", (reg.find? (·.id == "lean-no-tm-path")).isSome),
    ("registry has the SQL functions entry", (reg.find? (·.id == "lean-no-sql-functions")).isSome),
    ("every entry names its spec", reg.all (!·.spec.isEmpty)),
    ("listed difference passes", (findDeviation reg "sqlPrepare" tmPath leanErr rustOk).map (·.id) == some "lean-no-tm-path"),
    ("rarray difference passes", (findDeviation reg "sqlPrepare" rarray leanErr rustOk).isSome),
    ("unlisted difference fails", (findDeviation reg "sqlPrepare" other leanErr rustOk).isNone),
    ("listed op, other outcome fails", (findDeviation reg "sqlPrepare" tmPath rustOk leanErr).isNone),
    ("other op fails", (findDeviation reg "sparql" tmPath leanErr rustOk).isNone)]
  for (name, ok) in devChecks do
    if ok then passed := passed + 1 else failed := failed + 1; IO.eprintln s!"FAIL {name}"
  -- the benchmark never fails on a ratio, only on a mismatch
  let slow : Array Row := #[{ category := "lookups", name := "slow", rustMs := some 1.0,
                              leanMs := some 10.0, status := "ok" },
                            { category := "paths", name := "n/a", rustMs := some 1.0,
                              leanMs := none, status := "lean n/a" }]
  let bad := slow.push { category := "lookups", name := "different", rustMs := some 1.0,
                         leanMs := some 1.0, status := "mismatch" }
  let benchChecks : List (String × Bool) := [
    ("ten times slower still exits successfully", exitCode slow == 0),
    ("ratio is reported", (slow[0]!.ratio.map (fun x => decide (x > 9.9))) == some true),
    ("unsupported workload has no Lean column", slow[1]!.ratio.isNone),
    ("a result mismatch fails", exitCode bad == 1)]
  for (name, ok) in benchChecks do
    if ok then passed := passed + 1 else failed := failed + 1; IO.eprintln s!"FAIL {name}"
  IO.println s!"oracle tests: {passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1

end Oracle.Tests
