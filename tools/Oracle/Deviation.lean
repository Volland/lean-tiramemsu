/-
The deviation registry (`oracle/deviations.toml`): every accepted difference between the
builds, with an identifier, a summary, the spec that states it and a matcher. A mismatch
passes only if an entry's matcher covers it. Tooling only.
-/
import Policy.Toml
import Oracle.Canon

namespace Oracle

open Tiramemsu.Json

--# @lat: [[verification#Differential Oracle#Deviation Registry]]

/-- A registry entry. Matcher fields: `match.op` (operation name), `match.argsContainAny`
(substrings, any of which the compact request arguments contain), `match.lean` and
`match.rust` (outcome patterns: `ok`, `err`, `err:<code>` or `*`). -/
structure Deviation where
  id : String
  summary : String
  spec : String
  op : Option String
  argsContainAny : Array String
  lean : String
  rust : String
  deriving Repr, Inhabited

def loadDeviations (path : System.FilePath) : IO (Array Deviation) := do
  let doc ← match Policy.Toml.parse (← IO.FS.readFile path) with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"{path}: {e}")
  return (doc.all "deviation").map fun t =>
    { id := (t.str? "id").getD "", summary := (t.str? "summary").getD "",
      spec := (t.str? "spec").getD "", op := t.str? "match.op",
      argsContainAny := t.strs "match.argsContainAny",
      lean := (t.str? "match.lean").getD "*", rust := (t.str? "match.rust").getD "*" }

def outcomeMatches (pat : String) : Outcome → Bool
  | .ok _ => pat == "*" || pat == "ok"
  | .err code _ => pat == "*" || pat == "err" || pat == "err:" ++ code

/-- Whether the entry covers a mismatch of `op` with these arguments and outcomes. -/
def Deviation.covers (d : Deviation) (op : String) (args : Json) (lean rust : Outcome) : Bool :=
  let a := args.compress
  d.op.all (· == op) &&
  (d.argsContainAny.isEmpty || d.argsContainAny.any fun s => (a.splitOn s).length > 1) &&
  outcomeMatches d.lean lean && outcomeMatches d.rust rust

/-- The first registry entry covering a mismatch. -/
def findDeviation (reg : Array Deviation) (op : String) (args : Json) (lean rust : Outcome) :
    Option Deviation :=
  reg.find? (·.covers op args lean rust)

end Oracle
