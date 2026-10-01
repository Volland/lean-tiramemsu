/- Seeded violation `override-csimp`: `implemented_by` with no `@[csimp]` theorem. -/
def Fixture.Override.fast (n : Nat) : Nat := n
@[implemented_by Fixture.Override.fast]
def Fixture.Override.slow (n : Nat) : Nat := n + 0
