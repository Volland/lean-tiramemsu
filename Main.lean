/-
The `tiramemsu` executable: `version` and the oracle `driver`.
-/
import Tiramemsu

open Tiramemsu.Shell

def usage : String :=
  "usage: tiramemsu version [--verbose]\n       tiramemsu driver"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] | ["version", "--verbose"] | ["--version"] =>
    match ← (versionReport (args.contains "--verbose")).run with
    | .ok lines => lines.forM IO.println; pure 0
    | .error e => IO.eprintln s!"tiramemsu: {e}"; pure 1
  | ["driver"] => driverMain
  | _ => IO.eprintln usage; pure 2
