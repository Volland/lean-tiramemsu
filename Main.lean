/-
The `tiramemsu` executable: the command-line tool (`tiramemsu <db> <command> …`), `version` and
the oracle `driver`.
-/
import Tiramemsu

open Tiramemsu.Shell

def usage : String := Tiramemsu.Cli.usage

def main (args : List String) : IO UInt32 := do
  match args with
  | ["version"] | ["version", "--verbose"] | ["--version"] =>
    match ← (versionReport (args.contains "--verbose")).run with
    | .ok lines => lines.forM IO.println; pure 0
    | .error e => IO.eprintln s!"tiramemsu: {e}"; pure 1
  | ["driver"] => driverMain
  | [] => IO.eprintln usage; pure 2
  | _ => Tiramemsu.Cli.main args
