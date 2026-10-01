/- Seeded violation `verified-total` when the module is designated verified; accepted otherwise
(shell code may be partial). -/
partial def Fixture.Partial.spin (n : Nat) : Nat := Fixture.Partial.spin (n + 1)
