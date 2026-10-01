/-
The pool of reader connections (Rust's `pool.rs`): read-only connections on the same WAL file;
taking one blocks while every reader is in use. Shell module (unverified).
-/
import Std.Sync.Mutex
import Tiramemsu.Sqlite.Conn

namespace Tiramemsu.Shell

open Tiramemsu.Sqlite

--# @lat: [[engine#Shell]]

/-- Idle reader connections behind a mutex and a condition variable. -/
structure Pool where
  lock : Std.BaseMutex
  available : Std.Condvar
  idle : IO.Ref (Array Conn)
  size : Nat

/-- Opens `n` reader connections. -/
def Pool.open (path : System.FilePath) (opts : ConnOptions) (n : Nat) : SqlM Pool := do
  let mut cs := #[]
  for _ in [0:n] do cs := cs.push (← openReader path opts)
  pure { lock := ← (Std.BaseMutex.new : BaseIO _), available := ← (Std.Condvar.new : BaseIO _),
         idle := ← IO.mkRef cs, size := n }

/-- Takes an idle reader, waiting while every reader is busy. -/
def Pool.acquire (p : Pool) : IO Conn := do
  p.lock.lock
  try
    let mut c? := none
    while c?.isNone do
      let cs ← p.idle.get
      match cs.back? with
      | some c =>
        p.idle.set cs.pop
        c? := some c
      | none => p.available.wait p.lock
    match c? with
    | some c => pure c
    | none => throw (IO.userError "unreachable")
  finally
    p.lock.unlock

/-- Returns a reader to the pool. -/
def Pool.release (p : Pool) (c : Conn) : IO Unit := do
  p.lock.lock
  p.idle.modify (·.push c)
  p.available.notifyOne
  p.lock.unlock

/-- Drops every reader. -/
def Pool.close (p : Pool) : IO Unit := do
  for c in ← p.idle.get do c.clearCache
  p.idle.set #[]

end Tiramemsu.Shell
