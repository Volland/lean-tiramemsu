/-
Engine refinement: random scripts (`Test.Store.Gen`) run as transaction bodies on the model
store and on SQLite through the same engine; every result, report, error kind, every view read
at every `t` and the final tables must be equal. On SQLite (with the format-1 triggers) every
step must also keep every earlier statement with its content and retraction ("Random
operations under the triggers"), and the as-of view at every `t` must equal the replay of the
event log ("As-of equals replay of the log", random sequences).
-/
import Test.Store.Run
import Test.Store.Gen

namespace Test.Store.Refine

open Tiramemsu Tiramemsu.Json Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Shell Test.Store Test.Store.Gen

def outJ {α : Type} (f : α → Json) : Except Error α → Json
  | .ok a => .obj #[("ok", f a)]
  | .error e => .obj #[("err", .str e.code)]

def withResults (r : Array Json × TxReport) : Json :=
  match reportJ r.2 with
  | .obj kvs => .obj (kvs.push ("results", .arr r.1))
  | j => j

/-- Runs one step on a harness; the clock is the script's manual clock. -/
def runStep (h : Harness) (clock : IO.Ref Int) (s : Step) : IO Json := do
  match s.op with
  | "m2.setClock" => clock.set ((s.args.getInt? "ms").getD 0); pure .null
  | "m2.transact" =>
    let ops := (s.args.getArr? "ops").getD #[]
    match txOptionsOf ((s.args.get? "options").getD .null) with
    | .error m => pure (.obj #[("err", .str "InvalidArgument"), ("m", .str m)])
    | .ok opts =>
      let r ← if opts.dryRun then h.dry (← clock.get) opts (opsProg ops) else h.tx (← clock.get) opts (opsProg ops)
      pure (outJ withResults r)
  | "m2.with" =>
    let ops := (s.args.getArr? "ops").getD #[]
    let qs := (s.args.getArr? "queries").getD #[]
    let d := match s.args.get? "validAt" with
      | some j => (timeOfJ j).toOption.join
      | none => none
    pure (outJ id (← h.spec (← clock.get) (opsProg ops) d (queriesProg qs)))
  | "m2.read" =>
    match viewOfJ ((s.args.get? "view").getD .null) with
    | .error m => pure (.obj #[("err", .str "InvalidArgument"), ("m", .str m)])
    | .ok v => pure (outJ id (← h.query v (readProg ((s.args.getStr? "op").getD "") s.args)))
  | other => pure (.str s!"unknown step {other}")

/-- Every view read the suites compare after a script: the triples as of every `t`, now,
history, the event log, the dependents of every statement and the graphs. -/
def viewReads (h : Harness) (lastT : Nat) (eids : Nat) : IO (Array Json) := do
  let mut out := #[]
  let rd (v : View.ViewSpec) (op : String) (args : Json) : IO Json := do
    pure (outJ id (← h.query v (readProg op args)))
  for t in [0:lastT + 2] do
    out := out.push (← rd (asOf t.toInt64) "triples" .null)
  out := out.push (← rd nowV "triples" .null)
  out := out.push (← rd hist "triples" .null)
  out := out.push (← rd nowV "events" .null)
  out := out.push (← rd nowV "graphs" .null)
  out := out.push (← rd hist "graphs" .null)
  for e in [1:eids + 1] do
    out := out.push (← rd nowV "dependents" (.obj #[("eid", .int e)]))
    out := out.push (← rd hist "dependents" (.obj #[("eid", .int e)]))
  pure out

/-- Never forget: every row of `a` is in `b` with the same content, and its retraction is
unchanged or newly set. -/
def keeps (a b : ModelState) : Bool :=
  a.triples.all fun r => b.triples.any fun r' =>
    r'.eid == r.eid && r'.s == r.s && r'.p == r.p && r'.o == r.o && r'.tAdd == r.tAdd &&
    r'.vFrom == r.vFrom && r'.vTo == r.vTo &&
    ((r'.tRet == r.tRet && r'.retKind == r.retKind) || (r.tRet.isNone && r'.tRet.isSome && r'.retKind.isSome)) &&
  a.terms.all (b.terms.contains ·) && a.txs.all (b.txs.contains ·)

/-- The replay of the event log up to `t` (asserts add, retracts remove), as eids. -/
def replay (st : ModelState) (t : Int) : List Int64 :=
  let evs := View.eventsOf st.triples
  let evs := (evs.filter (·.t.toInt ≤ t)).mergeSort View.eventLe
  let set := evs.foldl (init := ([] : List Int64)) fun acc e =>
    match e.op with
    | .assert => acc ++ [e.eid.raw]
    | .retract => acc.filter (· != e.eid.raw)
  set.mergeSort fun a b => decide (a.toInt ≤ b.toInt)

def norm (st : ModelState) : ModelState :=
  { st with counters := st.counters.mergeSort (fun a b => decide (a.1 ≤ b.1)),
            volatile := st.volatile.mergeSort (fun a b => decide (a.s.toInt < b.s.toInt ∨ (a.s == b.s ∧ a.key.toInt ≤ b.key.toInt))),
            predMulti := st.predMulti.mergeSort (fun a b => decide (a.toInt ≤ b.toInt)),
            triples := st.triples.mergeSort (fun a b => decide (a.eid.toInt ≤ b.eid.toInt)),
            terms := st.terms.mergeSort (fun a b => decide (a.id.toInt ≤ b.id.toInt)) }

/-- Runs one seed; `none` when both stores agree everywhere. -/
def runSeed (seed ops : Nat) : IO (Option String) := do
  let script := Gen.script seed ops
  let m := modelHarness (← IO.mkRef freshModelState)
  let path ← freshPath s!"refine-m2-{seed}"
  let s := sqliteHarness path (← openStore path) (← Tiramemsu.Term.WriterCache.new none)
  let cm ← IO.mkRef (1000 : Int)
  let cs ← IO.mkRef (1000 : Int)
  let mut prev ← s.tables
  let mut failure : Option String := none
  for h : i in [0:script.size] do
    let st := script[i]
    let a ← runStep m cm st
    let b ← runStep s cs st
    if a.compress != b.compress then
      failure := some s!"seed {seed} step {i} {st.op} {st.args.compress}\n  model:  {a.compress}\n  sqlite: {b.compress}"
      break
    let cur ← s.tables
    if !keeps prev cur then
      failure := some s!"seed {seed} step {i}: a statement, term or tx row was lost or changed on SQLite"
      break
    prev := cur
  if failure.isNone then
    let tm ← m.tables
    let ts ← s.tables
    if norm tm != norm ts then failure := some s!"seed {seed}: final tables differ"
    else
      let lastT := ts.txs.length
      let eids := ts.triples.length + 2
      let vm ← viewReads m lastT eids
      let vs ← viewReads s lastT eids
      for (x, y) in vm.zip vs do
        if failure.isNone && x.compress != y.compress then
          failure := some s!"seed {seed}: view read differs\n  model:  {x.compress}\n  sqlite: {y.compress}"
      -- as-of equals the replay of the event log, at every t
      for t in [0:lastT + 1] do
        let asof ← ok! "as-of" (← s.query (asOf t.toInt64) (do return (← triplesQ).toList.map (·.eid)))
        if failure.isNone && asof != replay ts t then
          failure := some s!"seed {seed}: as-of {t} differs from the replayed log"
  s.close
  pure failure

def flagNat (args : List String) (name : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def main (args : List String) : IO UInt32 := do
  let seeds := flagNat args "--seeds" 50
  let ops := flagNat args "--ops" 100
  let first := flagNat args "--first" 1
  let mut failed := 0
  for seed in [first:first + seeds] do
    if let some f ← runSeed seed ops then
      IO.eprintln s!"FAIL {f}"
      failed := failed + 1
      if failed ≥ 5 then break
  IO.println s!"store refinement: {seeds} seeds x {ops} steps, {failed} failed"
  pure (if failed == 0 then 0 else 1)

end Test.Store.Refine
