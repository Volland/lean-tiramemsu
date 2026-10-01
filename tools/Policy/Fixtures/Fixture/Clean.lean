/- Accepted: a total definition and theorems using only the standard axioms. -/
def Fixture.Clean.double (n : Nat) : Nat := n + n
theorem Fixture.Clean.std_axioms (p : Prop) : p ∨ ¬ p := Classical.em p
theorem Fixture.Clean.double_eq (n : Nat) : Fixture.Clean.double n = 2 * n := by
  unfold Fixture.Clean.double; omega
