/-
Clocks for transaction instants (Rust's `clock.rs`): the system clock in epoch milliseconds,
and a manual clock that moves only when set or advanced (tests and differential runs).
Shell module (unverified).
-/
import Std.Time

namespace Tiramemsu.Shell

--# @lat: [[engine#Shell]]

/-- A source of wall-clock time in epoch milliseconds. -/
structure Clock where
  now : IO Int

/-- The system clock. -/
def systemClock : Clock :=
  ⟨do return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val⟩

/-- A clock that only moves when told to. -/
structure ManualClock where
  ref : IO.Ref Int

def ManualClock.new (ms : Int) : IO ManualClock := do return ⟨← IO.mkRef ms⟩
def ManualClock.set (c : ManualClock) (ms : Int) : IO Unit := c.ref.set ms
def ManualClock.advance (c : ManualClock) (delta : Int) : IO Unit := c.ref.modify (· + delta)
def ManualClock.clock (c : ManualClock) : Clock := ⟨c.ref.get⟩

end Tiramemsu.Shell
