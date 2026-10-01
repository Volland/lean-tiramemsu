/-
`tiramemsu-tests store`: every M2 store scenario on the model store and on SQLite.
-/
import Test.Store.TxLog
import Test.Store.Verbs
import Test.Store.Cascade
import Test.Store.Supersede
import Test.Store.Schema
import Test.Store.Graphs
import Test.Store.Views

namespace Test.Store

def scenarios : List (String × Scenario) :=
  TxLog.all ++ Verbs.all ++ Cascade.all ++ Supersede.all ++ Schema.all ++ Graphs.all ++ Views.all

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  let (_, r) ← (do
    for (name, sc) in scenarios do
      if only.all (name.startsWith ·) then runScenario name sc
    for (name, sc) in Cascade.large do
      if only.all (name.startsWith ·) then runSqliteOnly name sc : TestM Unit).run {}
  finish "store" r

end Test.Store
