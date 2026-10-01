/-
`tiramemsu-tests`: binding probes, store-contract tests, refinement tests and fixtures.
-/
import Test.Probe
import Test.Schema
import Test.Contract
import Test.Plan
import Test.Compat
import Test.Refine
import Test.Codec
import Test.Storage
import Test.Terms
import Test.Store.Main
import Test.Store.Refine
import Test.Store.Concurrency
import Test.Store.Merge

def usage : String := "usage: tiramemsu-tests <probe [--large] | contract | plan [db] | compat <rust-db> | refine [--seeds N] [--ops M] [--start db] [--self-test] | schema-dump <db> | codec | storage | terms [--seeds N] [--ops M] | store [prefix] | merge [--seeds N] | store-refine [--seeds N] [--ops M] | concurrency [--seeds N]>"

def main (args : List String) : IO UInt32 := do
  match args with
  | "probe" :: rest => Test.Probe.main rest
  | "schema-dump" :: rest => Test.Schema.main rest
  | "contract" :: rest => Test.Contract.main rest
  | "plan" :: rest => Test.Plan.main rest
  | "compat" :: rest => Test.Compat.main rest
  | "refine" :: rest => Test.Refine.main rest
  | ["codec"] => Test.Codec.main
  | ["storage"] => Test.Storage.main
  | "terms" :: rest => Test.Terms.main rest
  | "store" :: rest => Test.Store.main rest
  | "store-refine" :: rest => Test.Store.Refine.main rest
  | "merge" :: rest => Test.Store.MergeTest.main rest
  | "concurrency" :: rest => Test.Store.Concurrency.main rest
  | _ => IO.eprintln usage; pure 2
