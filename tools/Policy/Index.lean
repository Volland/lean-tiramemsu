/-
Spec parsing for the theorem index: requirements and scenarios of OpenSpec `spec.md` files.
A requirement is proven exactly when it has a scenario whose name begins with
`Machine-checked`. Tooling only.
-/
import Policy.Toml

namespace Policy

/-- A requirement of a capability spec. -/
structure Requirement where
  capability : String
  name : String
  proven : Bool
  /-- `project` for `openspec/specs`, otherwise the name of the active change. -/
  source : String
  deriving Repr, Inhabited

/-- Requirements of one spec file. Requirements under `## REMOVED Requirements` are skipped. -/
def parseSpec (capability source text : String) : Array Requirement := Id.run do
  let mut out : Array Requirement := #[]
  let mut cur : Option Requirement := none
  let mut removed := false
  for line in text.splitOn "\n" do
    let l := line.trimAsciiEnd.toString
    if l.startsWith "## " && !l.startsWith "### " then
      if let some r := cur then out := out.push r
      cur := none
      removed := (l.splitOn "REMOVED").length > 1
    else if l.startsWith "### Requirement:" then
      if let some r := cur then out := out.push r
      let name := (l.drop "### Requirement:".length).trimAscii.toString
      cur := if removed then none else some { capability, name, proven := false, source }
    else if l.startsWith "#### Scenario:" then
      let sc := (l.drop "#### Scenario:".length).trimAscii.toString
      if sc.startsWith "Machine-checked" then
        cur := cur.map ({ · with proven := true })
  if let some r := cur then out := out.push r
  return out

/-- The `spec.md` files of a specs directory, as (capability, path). -/
def specFiles (dir : System.FilePath) : IO (Array (String × System.FilePath)) := do
  if !(← dir.isDir) then return #[]
  let mut out := #[]
  for e in ← dir.readDir do
    let f := e.path / "spec.md"
    if ← f.pathExists then out := out.push (e.fileName, f)
  return out.qsort (·.1 < ·.1)

/-- Requirements of the project specs and of every active change. -/
def loadRequirements (root : System.FilePath) : IO (Array Requirement) := do
  let mut out := #[]
  for (cap, f) in ← specFiles (root / "openspec" / "specs") do
    out := out ++ parseSpec cap "project" (← IO.FS.readFile f)
  let changes := root / "openspec" / "changes"
  if ← changes.isDir then
    let entries := (← changes.readDir).qsort (·.fileName < ·.fileName)
    for e in entries do
      if e.fileName == "archive" || !(← e.path.isDir) then continue
      for (cap, f) in ← specFiles (e.path / "specs") do
        out := out ++ parseSpec cap e.fileName (← IO.FS.readFile f)
  return out

/-- An entry of the theorem index. -/
structure IndexEntry where
  spec : String
  requirement : String
  theorems : Array String
  deriving Repr, Inhabited

/-- Reads `[[requirement]]` tables with `spec`, `name` and `theorems`. -/
def loadIndex (path : System.FilePath) : IO (Array IndexEntry) := do
  let doc ← match Toml.parse (← IO.FS.readFile path) with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"{path}: {e}")
  return (doc.all "requirement").map fun t =>
    { spec := (t.str? "spec").getD "", requirement := (t.str? "name").getD "",
      theorems := t.strs "theorems" }

end Policy
