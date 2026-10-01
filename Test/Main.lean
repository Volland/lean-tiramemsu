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

def usage : String := "usage: tiramemsu-tests <probe [--large] | contract | plan [db] | compat <rust-db> | refine [--seeds N] [--ops M] [--start db] [--self-test] | schema-dump <db> | codec | storage | terms [--seeds N] [--ops M]>"

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
  | _ => IO.eprintln usage; pure 2
