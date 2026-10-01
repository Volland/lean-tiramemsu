/-
Valid-time intervals: the emptiness check, the overlap test of assert and cardinality one,
and membership of an instant (half-open, absent bounds unbounded).
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Engine.Types

namespace Tiramemsu.Engine

--# @lat: [[engine#Intervals]]

namespace Valid

/-- Valid for all time. -/
def always : Valid := {}

/-- An interval is nonempty unless both bounds are present and `vFrom ≥ vTo`. -/
def nonempty (v : Valid) : Bool :=
  match v.vFrom, v.vTo with
  | some a, some b => decide (a.toInt < b.toInt)
  | _, _ => true

/-- Fails with `InvalidInterval` on an empty interval. -/
def check (v : Valid) : Except Error Unit :=
  match v.vFrom, v.vTo with
  | some a, some b => if a.toInt < b.toInt then .ok () else .error (.invalidInterval a b)
  | _, _ => .ok ()

/-- The instant `d` (any integer) lies in `[vFrom, vTo)`. -/
def containsInt (v : Valid) (d : Int) : Bool :=
  (match v.vFrom with
   | none => true
   | some a => decide (a.toInt ≤ d)) &&
  (match v.vTo with
   | none => true
   | some b => decide (d < b.toInt))

/-- The instant `d` lies in the interval (the valid-at filter). -/
def validAt (v : Valid) (d : Int64) : Bool := v.containsInt d.toInt

/-- The overlap test: `(a.from absent or b.to absent or a.from < b.to) and
(b.from absent or a.to absent or b.from < a.to)`. -/
def overlaps (a b : Valid) : Bool :=
  (match a.vFrom, b.vTo with
   | some x, some y => decide (x.toInt < y.toInt)
   | _, _ => true) &&
  (match b.vFrom, a.vTo with
   | some x, some y => decide (x.toInt < y.toInt)
   | _, _ => true)

end Valid

end Tiramemsu.Engine
