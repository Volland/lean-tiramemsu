/-
Proofs of the integer canonical form: canonicalizing is idempotent, keeps the value, and two
lexical forms canonicalize to the same text exactly when they denote the same integer.
-/
import Tiramemsu.Codec.Integer
import TiramemsuProofs.Codec.Text
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Ring

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Numbers]]

/-- The canonical decimal of an integer parses back to it. -/
theorem parseIntLex_intText (i : Int) : parseIntLex (intText i) = some i := by
  unfold parseIntLex parseIntChars
  rw [intText_toList]
  by_cases h : i < 0
  · simp [h, splitSign, digitsVal_natChars]
    rw [abs_of_neg h]; ring
  · simp [h, splitSign_natChars, digitsVal_natChars]
    omega

/-- Canonicalizing an integer form is idempotent and keeps its value. -/
theorem canonInteger_idem (s c : String) (h : canonInteger s = some c) :
    canonInteger c = some c ∧ parseIntLex c = parseIntLex s := by
  unfold canonInteger at h ⊢
  cases hs : parseIntLex s with
  | none => rw [hs] at h; cases h
  | some i =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    rw [parseIntLex_intText]
    exact ⟨rfl, rfl⟩

/-- Two integer forms canonicalize to the same text exactly when they denote the same integer. -/
theorem canonInteger_eq_iff (s t c d : String) (hs : canonInteger s = some c)
    (ht : canonInteger t = some d) : c = d ↔ parseIntLex s = parseIntLex t := by
  have h1 := (canonInteger_idem s c hs).2
  have h2 := (canonInteger_idem t d ht).2
  constructor
  · rintro rfl; rw [← h1, ← h2]
  · intro h
    unfold canonInteger at hs ht
    rw [h] at hs
    rw [hs] at ht
    exact Option.some.inj ht

end Tiramemsu.Codec
