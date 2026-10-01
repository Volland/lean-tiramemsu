/-
The M2 differential suite (D6): random store scripts (`Test.Store.Gen`) run through the pinned
Rust driver and the Lean driver on separate files with the same manual clock. Every step's
result (reports, op results, error codes, view reads) and the canonical dumps of `triple`,
`term`, `tx`, `meta`, `volatile` and `pred_multi` must be equal; afterwards each build opens
the other's file, both dump it and continue with the same steps. Tooling only.
-/
import Oracle.Driver
import Oracle.Deviation
import Oracle.Scenario
import Test.Store.Gen

namespace Oracle.Store

open Tiramemsu.Json Oracle Test.Store.Gen

--# @lat: [[engine#Differential Store Oracle]]

structure Totals where
  steps : Nat := 0
  compared : Nat := 0
  accepted : Array String := #[]
  failures : Array String := #[]

def stepJ (s : Step) : String := s!"{s.op} {s.args.compress}"

/-- Compares one request on both drivers. -/
def compare (rust lean : Driver) (reg : Array Deviation) (where_ : String) (op : String) (args : Json)
    (t : Totals) : IO Totals := do
  let r ← rust.call op args
  let l ← lean.call op args
  let t := { t with compared := t.compared + 1 }
  if sameOutcome [] l r then return t
  -- lean-graphs-dedup: Rust lists a graph once per visible declaration when `sys:inGraph` was
  -- never interned (no UNION, no DISTINCT); accepted only when that is the whole difference
  if op == "m2.read" && args.getStr? "op" == some "graphs" then
    match r, l with
    | .ok (.arr rs), .ok (.arr ls) =>
      let dedup := rs.foldl (init := #[]) fun acc x => if acc.any (· == x) then acc else acc.push x
      if dedup.map (·.compress) == ls.map (·.compress) then
        return { t with accepted := t.accepted.push s!"{where_}: accepted deviation lean-graphs-dedup" }
    | _, _ => pure ()
  match findDeviation reg op args l r with
  | some d => return { t with accepted := t.accepted.push s!"{where_}: accepted deviation {d.id}" }
  | none =>
    let msg := s!"{where_}: {op} {args.compress}\n  rust: {(r.canon []).compress}\n  lean: {(l.canon []).compress}"
    return { t with failures := t.failures.push msg }

/-- The reads compared after a script: triples at every `t`, history, events, graphs and the
dependents of every statement on now and history. -/
def finalReads (lastT eids : Nat) : Array Json := Id.run do
  let mut out := #[]
  for t in [0:lastT + 2] do
    out := out.push (.obj #[("op", .str "triples"), ("view", .obj #[("kind", .str "asOf"), ("tx", .int t)])])
  out := out.push (.obj #[("op", .str "triples"), ("view", .obj #[("kind", .str "history")])])
  out := out.push (.obj #[("op", .str "events"), ("since", .int 0)])
  out := out.push (.obj #[("op", .str "graphs")])
  for e in [1:eids + 1] do
    out := out.push (.obj #[("op", .str "dependents"), ("eid", .int e)])
    out := out.push (.obj #[("op", .str "dependents"), ("eid", .int e), ("view", .obj #[("kind", .str "history")])])
  out

def lastTOf (dump : Outcome) : Nat × Nat :=
  match dump with
  | .ok j => ((j.getArr? "tx").map (·.size) |>.getD 0, (j.getArr? "triple").map (·.size) |>.getD 0)
  | _ => (0, 0)

/-- Runs one seed. -/
def runSeed (rust lean : Driver) (reg : Array Deviation) (seed ops : Nat) (t : Totals) : IO Totals := do
  let dir : System.FilePath := ".oracle" / "work" / "m2-store"
  IO.FS.createDirAll dir
  let rf := dir / s!"rust-{seed}.db"
  let lf := dir / s!"lean-{seed}.db"
  for f in [rf, lf] do
    for suf in ["", "-wal", "-shm"] do
      let p : System.FilePath := f.toString ++ suf
      if ← p.pathExists then IO.FS.removeFile p
  let _ ← rust.call! "m2.open" (.obj #[("path", .str rf.toString), ("clock", .int 1000)])
  let _ ← lean.call! "m2.open" (.obj #[("path", .str lf.toString), ("clock", .int 1000)])
  let script := Test.Store.Gen.script seed ops
  let mut t := t
  for h : i in [0:script.size] do
    let s := script[i]
    t ← compare rust lean reg s!"seed {seed} step {i}" s.op s.args { t with steps := t.steps + 1 }
  t ← compare rust lean reg s!"seed {seed} dump" "rawDump" .null t
  let (lastT, rows) := lastTOf (← rust.call "rawDump")
  for q in finalReads lastT (rows + 2) do
    let args := match q with
      | .obj kvs => if kvs.any (·.1 == "view") then q else .obj (kvs.push ("view", .obj #[("kind", .str "now")]))
      | j => j
    t ← compare rust lean reg s!"seed {seed} final read" "m2.read" args t
  let _ ← rust.call "m2.close"
  let _ ← lean.call "m2.close"
  -- cross-open: each build opens the other's file, dumps it, and continues the same steps
  let _ ← rust.call! "m2.open" (.obj #[("path", .str lf.toString), ("clock", .int 5000)])
  let _ ← lean.call! "m2.open" (.obj #[("path", .str rf.toString), ("clock", .int 5000)])
  t ← compare rust lean reg s!"seed {seed} cross dump" "rawDump" .null t
  for i in [0:(min 30 script.size)] do
    let s := script[i]!
    t ← compare rust lean reg s!"seed {seed} cross step {i}" s.op s.args t
  t ← compare rust lean reg s!"seed {seed} cross final dump" "rawDump" .null t
  let _ ← rust.call "m2.close"
  let _ ← lean.call "m2.close"
  pure t

def flagNat (args : List String) (name : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def main (args : List String) : IO UInt32 := do
  let seeds := flagNat args "--seeds" 20
  let ops := flagNat args "--ops" 100
  let first := flagNat args "--first" 1
  let reg ← loadDeviations ("oracle" / "deviations.toml")
  let rust ← startRust
  let lean ← startLean
  let mut t : Totals := {}
  for seed in [first:first + seeds] do
    t ← runSeed rust lean reg seed ops t
    if t.failures.size ≥ 5 then break
  rust.stop
  lean.stop
  for f in t.failures do IO.eprintln s!"FAIL {f}"
  for a in t.accepted do IO.println s!"  {a}"
  IO.println s!"store differential: {seeds} seeds x {ops} steps, {t.compared} compared, {t.accepted.size} accepted deviations, {t.failures.size} failures"
  pure (if t.failures.isEmpty then 0 else 1)

end Oracle.Store
