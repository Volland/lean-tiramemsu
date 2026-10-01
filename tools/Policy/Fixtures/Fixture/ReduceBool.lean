/- Seeded violation `axiom-set`: a theorem depending on `Lean.ofReduceBool` without being on the
allowlist (and without the tactic that the source rules look for). -/
def Fixture.ReduceBool.yes : Bool := true
theorem Fixture.ReduceBool.thm : Fixture.ReduceBool.yes = true :=
  Lean.ofReduceBool Fixture.ReduceBool.yes true rfl
