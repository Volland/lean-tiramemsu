/- `bv_decide` in a codec proof module: accepted when the theorem is allowlisted, rejected by
`axiom-set` otherwise (the tactic's certificate axiom `…._native.bv_decide.ax…`). -/
import Std.Tactic.BVDecide
theorem Fixture.Codec.BvOk.and_or_add (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by bv_decide
