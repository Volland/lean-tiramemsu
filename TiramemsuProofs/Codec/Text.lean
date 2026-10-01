/-
Facts about the decimal rendering and parsing helpers shared by the literal proofs.
-/
import Tiramemsu.Codec.Text
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Induction

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals]]

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := Nat.toDigits_ne_nil

theorem natChars_all_digit (n : Nat) : (natChars n).all isDigitChar = true := by
  rw [List.all_eq_true]
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem natChars_val (n : Nat) : Nat.ofDigitChars 10 (natChars n) 0 = n :=
  Nat.ofDigitChars_ten_toDigits

theorem digitsVal_natChars (n : Nat) : digitsVal? (natChars n) = some n := by
  simp [digitsVal?, natChars_ne_nil, natChars_all_digit, natChars_val]

theorem isDigit_not_sign {c : Char} (h : c.isDigit = true) : c ≠ '-' ∧ c ≠ '+' := by
  constructor <;> (rintro rfl; revert h; decide)

theorem splitSign_digit_head (c : Char) (l : List Char) (hc : c.isDigit = true) :
    splitSign (c :: l) = (false, c :: l) := by
  obtain ⟨h1, h2⟩ := isDigit_not_sign hc
  unfold splitSign
  split <;> simp_all

theorem splitSign_natChars (n : Nat) : splitSign (natChars n) = (false, natChars n) := by
  have hall := natChars_all_digit n
  cases h : natChars n with
  | nil => exact absurd h (natChars_ne_nil n)
  | cons c rest =>
    rw [h] at hall
    have hc : c.isDigit = true := by simp at hall; exact hall.1
    obtain ⟨h1, h2⟩ := isDigit_not_sign hc
    unfold splitSign
    split <;> simp_all

theorem natText_toList (n : Nat) : (natText n).toList = natChars n := String.toList_ofList

theorem intText_toList (i : Int) :
    (intText i).toList = if i < 0 then '-' :: natChars i.natAbs else natChars i.toNat := by
  unfold intText
  split
  · simp [String.toList_append, natText_toList]
  · exact natText_toList _

/-- The digits of `n` have at most `k` characters exactly when `n < 10^k`. -/
theorem natChars_length_le (n k : Nat) (hk : 0 < k) : (natChars n).length ≤ k ↔ n < 10 ^ k :=
  Nat.length_toDigits_le_iff (by decide) hk

theorem natChars_length_pos (n : Nat) : 0 < (natChars n).length := by
  have := natChars_ne_nil n
  cases h : natChars n with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem digitChar_ne_zero (n : Nat) (h0 : 0 < n) (h : n < 10) : n.digitChar ≠ '0' := by
  have : n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9] := by simp; omega
  simp at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The first digit of a positive number is not `0`. -/
theorem natChars_head_ne_zero (n : Nat) (hn : 0 < n) : ∃ c rest, natChars n = c :: rest ∧ c ≠ '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold natChars
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · exact ⟨_, [], rfl, digitChar_ne_zero n hn (by omega)⟩
    · obtain ⟨c, rest, h, hc⟩ := ih (n / 10) (by omega) (by omega)
      unfold natChars at h
      exact ⟨c, rest ++ [(n % 10).digitChar], by rw [h]; rfl, hc⟩

theorem digitChar_of_isDigit (c : Char) (h : c.isDigit = true) : (c.toNat - 48).digitChar = c := by
  have h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simp [Char.isDigit] at h
    exact ⟨h.1, h.2⟩
  apply Char.toNat_inj.mp
  generalize hv : c.toNat = v at h1 ⊢
  obtain ⟨a, b⟩ := h1
  have : v - 48 < 10 := by omega
  generalize hd : v - 48 = d at this
  have hv' : v = d + 48 := by omega
  subst hv'
  interval_cases d <;> rfl

theorem ofDigitChars_pos (c : Char) (t : List Char) (hc : c.isDigit = true) (hz : c ≠ '0') :
    0 < Nat.ofDigitChars 10 (c :: t) 0 := by
  rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_eq_ofDigitChars_zero]
  have : 0 < c.toNat - '0'.toNat := by
    have h1 : 48 ≤ c.toNat := by simp [Char.isDigit] at hc; exact hc.1
    have h2 : c.toNat ≠ 48 := by
      intro e; apply hz; apply Char.toNat_inj.mp; rw [e]; rfl
    simp; omega
  have : 0 < 10 ^ t.length * (10 * 0 + (c.toNat - '0'.toNat)) := by
    apply Nat.mul_pos (Nat.pow_pos (by decide)); omega
  omega

/-- A canonical digit list (non-empty, no leading zero) is the rendering of its value. -/
theorem natChars_ofDigitChars (l : List Char) (hne : l ≠ []) (hd : l.all isDigitChar = true)
    (hz : ∀ t, l ≠ '0' :: t) : natChars (Nat.ofDigitChars 10 l 0) = l := by
  induction l using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton l' c ih =>
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hd
    obtain ⟨hd', hc⟩ := hd
    have hcl : c.toNat - 48 < 10 := by
      have : c.toNat ≤ 57 := by simp [Char.isDigit] at hc; exact hc.2
      omega
    rw [Nat.ofDigitChars_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil]
    cases l' with
    | nil =>
      simp only [List.nil_append] at hz ⊢
      have hc0 : c ≠ '0' := fun e => hz [] (by rw [e])
      simp only [Nat.ofDigitChars_nil, Nat.mul_zero, Nat.zero_add]
      unfold natChars
      rw [Nat.toDigits_of_lt_base (by simpa using hcl)]
      simp only [List.cons.injEq, and_true]
      simpa using digitChar_of_isDigit c hc
    | cons c' t' =>
      have hz' : c' ≠ '0' := fun e => hz (t' ++ [c]) (by rw [e]; rfl)
      have hc'd : c'.isDigit = true := by simp at hd'; exact hd'.1
      have hpos := ofDigitChars_pos c' t' hc'd hz'
      have ih' := ih (by simp) hd' (fun t e => hz' (List.cons.inj e).1)
      generalize hu : Nat.ofDigitChars 10 (c' :: t') 0 = u at hpos ih'
      unfold natChars at ih' ⊢
      have hc48 : c.toNat - '0'.toNat = c.toNat - 48 := rfl
      rw [hc48, Nat.toDigits_eq_ite (by decide)]
      rw [if_neg (by omega)]
      rw [show (10 * u + (c.toNat - 48)) / 10 = u by omega,
        show (10 * u + (c.toNat - 48)) % 10 = c.toNat - 48 by omega, ih', digitChar_of_isDigit c hc]

end Tiramemsu.Codec
