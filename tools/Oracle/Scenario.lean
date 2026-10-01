/-
Comparison scenarios over one shared database file. Each step names the build that runs it
(`rust`, `lean`, or `both`); a build opens the file the previous step left and closes it
(handoff after close). A step marked `compare` runs on both builds on copies of the shared
file, and the canonical results are compared; a mismatch passes only through the deviation
registry, and otherwise is reported with the scenario, step, seed and both results.
Tooling only.
-/
import Oracle.Driver
import Oracle.Deviation

namespace Oracle

open Tiramemsu.Json

--# @lat: [[verification#Differential Oracle#Scenarios]]

structure Step where
  build : String
  op : String
  args : Json := .null
  compare : Bool := false
  unordered : List String := []
  /-- The milestone that owns the operation on the Lean side: an `Unsupported` answer from
  the Lean build skips the step instead of failing it. -/
  owner : Option String := none
  /-- `err` when a single-build step is expected to fail. -/
  expect : Option String := none
  deriving Inhabited

structure Scenario where
  name : String
  seed : Option Int := none
  steps : Array Step
  deriving Inhabited

def Step.ofJson (j : Json) : Except String Step := do
  let some build := j.getStr? "build" | throw "a step needs `build`"
  let some op := j.getStr? "op" | throw "a step needs `op`"
  pure { build, op, args := (j.get? "args").getD .null, compare := (j.getBool? "compare").getD false,
         unordered := ((j.getArr? "unordered").getD #[]).toList.filterMap fun | .str s => some s | _ => none,
         owner := j.getStr? "owner", expect := j.getStr? "expect" }

def Scenario.ofJson (j : Json) : Except String Scenario := do
  let some name := j.getStr? "name" | throw "a scenario needs `name`"
  let some steps := j.getArr? "steps" | throw "a scenario needs `steps`"
  pure { name, seed := j.getInt? "seed", steps := ← steps.mapM Step.ofJson }

def Scenario.load (path : System.FilePath) : IO Scenario := do
  match Json.parse (← IO.FS.readFile path) >>= Scenario.ofJson with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- Copies a database file and its WAL. -/
def copyDb (src dst : System.FilePath) : IO Unit := do
  for suf in ["", "-wal", "-shm"] do
    let d : System.FilePath := dst.toString ++ suf
    if ← d.pathExists then IO.FS.removeFile d
  for suf in ["", "-wal"] do
    let s : System.FilePath := src.toString ++ suf
    if ← s.pathExists then IO.FS.writeBinFile (dst.toString ++ suf) (← IO.FS.readBinFile s)

/-- The result of a scenario run. -/
structure ScenarioResult where
  failures : Array String := #[]
  accepted : Array String := #[]
  skipped : Array String := #[]
  compared : Nat := 0

/-- Runs a scenario on a fresh shared file. -/
def runScenario (rust lean : Driver) (reg : Array Deviation) (sc : Scenario) : IO ScenarioResult := do
  let dir : System.FilePath := ".oracle" / "work" / sc.name
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let shared := dir / "shared.db"
  let mut res : ScenarioResult := {}
  let seedTxt := match sc.seed with | some s => s!", seed {s}" | none => ""
  for h : i in [0:sc.steps.size] do
    let st := sc.steps[i]
    let where_ := s!"scenario {sc.name}, step {i + 1} ({st.build} {st.op}{seedTxt})"
    if st.compare then
      let rc := dir / "copy-rust.db"
      let lc := dir / "copy-lean.db"
      copyDb shared rc
      copyDb shared lc
      let r ← rust.session rc st.op st.args
      let l ← lean.session lc st.op st.args
      res := { res with compared := res.compared + 1 }
      if sameOutcome st.unordered l r then continue
      if l.isUnsupported && st.owner.isSome then
        res := { res with skipped := res.skipped.push s!"{where_}: owned by {st.owner.getD ""}" }
        continue
      match findDeviation reg st.op st.args l r with
      | some d => res := { res with accepted := res.accepted.push s!"{where_}: accepted deviation {d.id}" }
      | none =>
        let msg := s!"{where_}: mismatch\n  rust: {(r.canon st.unordered).compress}\n  lean: {(l.canon st.unordered).compress}"
        res := { res with failures := res.failures.push msg }
    else
      let d := if st.build == "rust" then rust else lean
      let o ← d.session shared st.op st.args
      match o, st.expect with
      | .err c m, none => res := { res with failures := res.failures.push s!"{where_}: {c}: {m}" }
      | .ok _, some "err" => res := { res with failures := res.failures.push s!"{where_}: expected an error" }
      | _, _ => pure ()
  return res

end Oracle
