/-
Driver processes: the pinned Rust build's `tm-oracle-driver` and the Lean `tiramemsu driver`,
spoken to with the JSON-lines protocol. Tooling only.
-/
import Oracle.Canon

namespace Oracle

open Tiramemsu.Json

abbrev pipes : IO.Process.StdioConfig := { stdin := .piped, stdout := .piped, stderr := .inherit }

/-- A running driver. -/
structure Driver where
  name : String
  child : IO.Process.Child pipes
  next : IO.Ref Nat

def rustDriverPath : System.FilePath := ".oracle" / "target" / "release" / "tm-oracle-driver"
def leanDriverPath : System.FilePath := ".lake" / "build" / "bin" / "tiramemsu"

def Driver.start (name : String) (cmd : System.FilePath) (args : Array String := #[]) : IO Driver := do
  unless ← cmd.pathExists do
    throw (IO.userError s!"{name} driver not found at {cmd} (build it first)")
  let child ← IO.Process.spawn { cmd := cmd.toString, args, stdin := .piped, stdout := .piped,
                                 stderr := .inherit }
  pure { name, child, next := ← IO.mkRef 1 }

def startRust : IO Driver := Driver.start "rust" rustDriverPath
def startLean : IO Driver := Driver.start "lean" leanDriverPath #["driver"]

/-- One request and its response. -/
def Driver.call (d : Driver) (op : String) (args : Json := .null) : IO Outcome := do
  let id ← d.next.modifyGet fun n => (n, n + 1)
  let req := Json.obj #[("id", .int id), ("op", .str op), ("args", args)]
  d.child.stdin.putStrLn req.compress
  d.child.stdin.flush
  let line ← d.child.stdout.getLine
  if line.isEmpty then throw (IO.userError s!"{d.name} driver exited")
  match Json.parse line.trimAsciiEnd.toString with
  | .ok resp => pure (Outcome.ofResponse resp)
  | .error e => throw (IO.userError s!"{d.name} driver: bad response {line}: {e}")

/-- A call that must succeed. -/
def Driver.call! (d : Driver) (op : String) (args : Json := .null) : IO Json := do
  match ← d.call op args with
  | .ok r => pure r
  | .err c m => throw (IO.userError s!"{d.name} {op}: {c}: {m}")

def Driver.stop (d : Driver) : IO Unit := do
  let (_, child) ← d.child.takeStdin
  let _ ← child.wait

/-- Runs one operation on a file in its own session: open, operation, close. -/
def Driver.session (d : Driver) (path : System.FilePath) (op : String) (args : Json) : IO Outcome := do
  match ← d.call "open" (.obj #[("path", .str path.toString)]) with
  | .err c m => pure (.err c m)
  | .ok _ =>
    let r ← d.call op args
    let _ ← d.call "close"
    pure r

end Oracle
