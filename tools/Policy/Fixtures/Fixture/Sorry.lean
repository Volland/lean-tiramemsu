/- Seeded violation `no-sorry`: a helper lemma left unfinished, used through another theorem. -/
theorem Fixture.Sorry.helper : 1 + 1 = 3 := by sorry
theorem Fixture.Sorry.uses : 2 = 3 := by have := Fixture.Sorry.helper; omega
