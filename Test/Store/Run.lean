/-
Running store scenarios: every scenario runs on the model store and on a fresh SQLite file;
each run must pass, and both runs must end with equal tables.
-/
import Test.Store.Harness

namespace Test.Store

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Term

/-- A scenario: `none` passes, `some detail` fails. -/
abbrev Scenario := Harness → IO (Option String)

/-- Fails unless `got = want`. -/
def expect {α : Type} [BEq α] [Repr α] (what : String) (got want : α) : Option String :=
  if got == want then none else some s!"{what}: got {reprStr got}, want {reprStr want}"

def allOk (xs : List (Option String)) : Option String := xs.findSome? id

/-- The result of an `Except`, or a failure message. -/
def ok! {α : Type} (what : String) : Except Error α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: unexpected {e.code}: {e}")

/-- Runs one scenario on both stores. -/
def runScenario (name : String) (sc : Scenario) : TestM Unit := do
  let m := modelHarness (← IO.mkRef freshModelState)
  let path ← freshPath s!"m2-{name.replace " " "-"}"
  let s := sqliteHarness path (← openStore path) (← WriterCache.new none)
  let rm ← try sc m catch e => pure (some s!"exception: {e}")
  let rs ← try sc s catch e => pure (some s!"exception: {e}")
  check s!"{name} [model]" rm.isNone (rm.getD "")
  check s!"{name} [sqlite]" rs.isNone (rs.getD "")
  let tm ← m.tables
  let ts ← s.tables
  let norm (st : ModelState) : ModelState :=
    { st with counters := st.counters.mergeSort (fun a b => decide (a.1 ≤ b.1)),
              volatile := st.volatile.mergeSort (fun a b => decide (a.s.toInt < b.s.toInt ∨ (a.s == b.s ∧ a.key.toInt ≤ b.key.toInt))),
              predMulti := st.predMulti.mergeSort (fun a b => decide (a.toInt ≤ b.toInt)),
              triples := st.triples.mergeSort (fun a b => decide (a.eid.toInt ≤ b.eid.toInt)),
              terms := st.terms.mergeSort (fun a b => decide (a.id.toInt ≤ b.id.toInt)) }
  let same := norm tm == norm ts
  check s!"{name} [same tables]" same
    (if same then "" else s!"model {reprStr (norm tm)}\nsqlite {reprStr (norm ts)}")
  s.close

/-- Runs a scenario on SQLite only (sizes the list-based model store is too slow for). -/
def runSqliteOnly (name : String) (sc : Scenario) : TestM Unit := do
  let path ← freshPath s!"m2-{name.replace " " "-"}"
  let s := sqliteHarness path (← openStore path) (← WriterCache.new none)
  let rs ← try sc s catch e => pure (some s!"exception: {e}")
  check s!"{name} [sqlite]" rs.isNone (rs.getD "")
  s.close

end Test.Store
