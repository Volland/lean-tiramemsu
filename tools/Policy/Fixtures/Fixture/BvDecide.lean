/- Seeded violation `bv-decide-scope`: `bv_decide` outside the codec proof modules. -/
import Std.Tactic.BVDecide
example (x : BitVec 8) : x &&& x = x := by bv_decide
