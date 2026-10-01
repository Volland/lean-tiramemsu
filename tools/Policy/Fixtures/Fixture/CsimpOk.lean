/- Accepted: an override justified by a `@[csimp]` equality theorem. -/
def Fixture.CsimpOk.fast (n : Nat) : Nat := n
def Fixture.CsimpOk.slow (n : Nat) : Nat := n + 0
@[csimp] theorem Fixture.CsimpOk.slow_eq_fast : @Fixture.CsimpOk.slow = @Fixture.CsimpOk.fast := by
  funext n; rfl
attribute [implemented_by Fixture.CsimpOk.fast] Fixture.CsimpOk.slow
