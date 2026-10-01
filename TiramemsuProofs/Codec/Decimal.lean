/-
Proofs of the decimal canonical form against the rational value `decVal`: canonicalizing is
idempotent, keeps the value, and two valid forms canonicalize to the same text exactly when
they denote the same rational.
-/
import Tiramemsu.Codec.Decimal
import TiramemsuProofs.Codec.Text
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Numbers]]

/-- The rational value of (negative, mantissa, scale): `±m / 10^k`. -/
def decValOf (x : Bool × Nat × Nat) : ℚ := (if x.1 then -1 else 1) * (x.2.1 : ℚ) / 10 ^ x.2.2

/-- The rational value of a decimal lexical form (0 when ill-typed). -/
def decVal (s : String) : ℚ :=
  match scanDecimal s.toList with
  | some x => decValOf x
  | none => 0

/-- The normal form: no trailing fraction zero, no sign on zero. -/
def DecNormal (x : Bool × Nat × Nat) : Prop :=
  (x.2.2 = 0 ∨ x.2.1 % 10 ≠ 0) ∧ (x.1 = true → x.2.1 ≠ 0)

theorem stripZeros_spec (fuel m k : Nat) (hk : k ≤ fuel) :
    ((stripZeros fuel m k).1 : ℚ) / 10 ^ (stripZeros fuel m k).2 = (m : ℚ) / 10 ^ k ∧
      ((stripZeros fuel m k).2 = 0 ∨ (stripZeros fuel m k).1 % 10 ≠ 0) ∧
      ((stripZeros fuel m k).1 = 0 ↔ m = 0) := by
  induction fuel generalizing m k with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp [stripZeros]
  | succ fuel ih =>
    unfold stripZeros
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨a, b, c⟩ := ih (m / 10) (k - 1) (by omega)
      refine ⟨?_, b, ?_⟩
      · rw [a]
        have hm : (m : ℚ) = 10 * ((m / 10 : ℕ) : ℚ) := by
          have : m = 10 * (m / 10) := by omega
          exact_mod_cast this
        rw [hm]
        have hk' : k = (k - 1) + 1 := by omega
        rw [hk', pow_succ]
        simp only [Nat.add_sub_cancel]
        field_simp
      · rw [c]; omega
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at h
      refine ⟨rfl, ?_, Iff.rfl⟩
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · exact Or.inr (h (by omega))

theorem normDec_spec (n : Bool) (m k : Nat) :
    decValOf (normDec n m k) = decValOf (n, m, k) ∧ DecNormal (normDec n m k) := by
  obtain ⟨a, b, c⟩ := stripZeros_spec k m k (le_refl _)
  unfold normDec decValOf DecNormal
  generalize stripZeros k m k = r at a b c
  obtain ⟨m', k'⟩ := r
  simp only at a b c ⊢
  refine ⟨?_, b, ?_⟩
  · by_cases hm : m' = 0
    · have : m = 0 := c.mp hm
      subst hm this; simp
    · have hb : (m' != 0) = true := by simp [hm]
      simp only [hb, Bool.and_true]
      rw [mul_div_assoc, mul_div_assoc, a]
  · simp

theorem isDigit_zero : ('0' : Char).isDigit = true := by decide

theorem stripZeros_normal (fuel m k : Nat) (h : k = 0 ∨ m % 10 ≠ 0) : stripZeros fuel m k = (m, k) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    unfold stripZeros
    have : ¬ (decide (k > 0) && m % 10 == 0) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]; omega
    rw [if_neg this]

theorem normDec_normal {n : Bool} {m k : Nat} (h : DecNormal (n, m, k)) : normDec n m k = (n, m, k) := by
  obtain ⟨hz, hs⟩ := h
  simp only at hz hs
  unfold normDec
  rw [stripZeros_normal _ _ _ hz]
  simp only [Prod.mk.injEq, and_true]
  cases n
  · rfl
  · simp [hs rfl]

theorem normDec_ten (n : Bool) (m : Nat) : normDec n (10 * m) 1 = normDec n m 0 := by
  unfold normDec
  have : stripZeros 1 (10 * m) 1 = (m, 0) := by
    unfold stripZeros
    have h1 : (decide (1 > 0) && 10 * m % 10 == 0) = true := by simp
    rw [if_pos h1]
    simp [stripZeros]
  rw [this, stripZeros_normal _ _ _ (Or.inl rfl)]

theorem takeWhile_digits (l r : List Char) (hl : l.all isDigitChar = true) :
    (l ++ '.' :: r).takeWhile (· != '.') = l := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    have hc : c ≠ '.' := by rintro rfl; exact absurd hl.1 (by decide)
    simp [hc, ih hl.2]

theorem padLeft_digits (k : Nat) (l : List Char) (hl : l.all isDigitChar = true) :
    (padLeft k '0' l).all isDigitChar = true := by
  simp only [padLeft, List.all_append, hl, Bool.and_true, List.all_eq_true]
  intro c hc
  rw [List.eq_of_mem_replicate hc]; decide

theorem ofDigitChars_padLeft (k : Nat) (l : List Char) :
    Nat.ofDigitChars 10 (padLeft k '0' l) 0 = Nat.ofDigitChars 10 l 0 := by
  simp [padLeft, Nat.ofDigitChars_append]

theorem padLeft_length (k : Nat) (l : List Char) (h : l.length ≤ k) : (padLeft k '0' l).length = k := by
  simp [padLeft]; omega

/-- Scanning the text of a normal-form decimal gives a decimal with the same normal form. -/
theorem scan_render (n : Bool) (m k : Nat) (hN : DecNormal (n, m, k)) :
    ∃ y, scanDecimal (renderDec n m k).toList = some y ∧ normDec y.1 y.2.1 y.2.2 = (n, m, k) := by
  obtain ⟨hz, hs⟩ := hN
  simp only at hz hs
  -- the fraction digits
  obtain ⟨F, hF, hFall, hFval, hFlen⟩ : ∃ F : List Char,
      (if k = 0 then "0" else String.ofList (padLeft k '0' (natChars (m % 10 ^ k)))).toList = F ∧
      F.all isDigitChar = true ∧
      Nat.ofDigitChars 10 F 0 = (if k = 0 then 0 else m % 10 ^ k) ∧ F.length = (if k = 0 then 1 else k) := by
    by_cases hk : k = 0
    · subst hk; exact ⟨['0'], by simp, by simp; decide, by simp [Nat.ofDigitChars_cons], by simp⟩
    · refine ⟨padLeft k '0' (natChars (m % 10 ^ k)), by simp [hk, String.toList_ofList], ?_, ?_, ?_⟩
      · exact padLeft_digits _ _ (natChars_all_digit _)
      · simp [hk, ofDigitChars_padLeft, natChars_val]
      · simp only [hk, ite_false]
        apply padLeft_length
        exact (natChars_length_le _ _ (by omega)).mpr (Nat.mod_lt _ (by positivity))
  have hbody : (renderDec n m k).toList =
      (if n then ['-'] else []) ++ (natChars (m / 10 ^ k) ++ '.' :: F) := by
    simp only [renderDec, String.toList_append, natText_toList, ← hF]
    split <;> simp
  obtain ⟨c0, rest0, hc0⟩ : ∃ c rest, natChars (m / 10 ^ k) = c :: rest := by
    cases h : natChars (m / 10 ^ k) with
    | nil => exact absurd h (natChars_ne_nil _)
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hc0d : c0.isDigit = true := by
    have := natChars_all_digit (m / 10 ^ k); rw [hc0] at this; simp at this; exact this.1
  have hsplit : splitSign ((if n then ['-'] else []) ++ (natChars (m / 10 ^ k) ++ '.' :: F)) =
      (n, natChars (m / 10 ^ k) ++ '.' :: F) := by
    cases n
    · simp only [Bool.false_eq_true, ite_false, List.nil_append, hc0, List.cons_append]
      rw [splitSign_digit_head _ _ hc0d]
    · simp [splitSign]
  refine ⟨(n, Nat.ofDigitChars 10 (natChars (m / 10 ^ k) ++ F) 0, F.length), ?_, ?_⟩
  · unfold scanDecimal
    rw [hbody, hsplit]
    simp only
    rw [takeWhile_digits _ _ (natChars_all_digit _)]
    simp only [List.drop_left', hc0, List.isEmpty_cons, Bool.false_and, Bool.false_eq_true,
      ite_false]
    rw [← hc0]
    simp [natChars_all_digit, hFall]
  · have hval : Nat.ofDigitChars 10 (natChars (m / 10 ^ k) ++ F) 0 = (if k = 0 then 10 * m else m) := by
      rw [Nat.ofDigitChars_append, Nat.ofDigitChars_eq_ofDigitChars_zero, natChars_val, hFval, hFlen]
      by_cases hk : k = 0
      · subst hk; simp
      · simp only [hk, ite_false]; exact Nat.div_add_mod m (10 ^ k)
    simp only
    rw [hval, hFlen]
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true]
      rw [normDec_ten, normDec_normal ⟨Or.inl rfl, hs⟩]
    · simp only [hk, ite_false]
      exact normDec_normal ⟨hz, hs⟩

theorem signed_cast (b : Bool) (a j : ℕ) :
    (if b then (-1 : ℚ) else 1) * (a : ℚ) * 10 ^ j = (((if b then -1 else 1) * ((a * 10 ^ j : ℕ) : ℤ) : ℤ) : ℚ) := by
  cases b <;> simp

theorem pow_ten_shift (a b j j' : Nat) (hj : j < j') (e : a * 10 ^ j' = b * 10 ^ j) : b % 10 = 0 := by
  have : b = a * 10 ^ (j' - j) := by
    have e2 : a * 10 ^ (j' - j) * 10 ^ j = b * 10 ^ j := by
      rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]; exact e
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) e2).symm
  rw [this, show j' - j = (j' - j - 1) + 1 by omega, Nat.pow_succ]
  simp [Nat.mul_mod, Nat.mul_assoc]

/-- Normal forms are determined by their value. -/
theorem normal_unique (x y : Bool × Nat × Nat) (hx : DecNormal x) (hy : DecNormal y)
    (h : decValOf x = decValOf y) : x = y := by
  obtain ⟨n, m, k⟩ := x
  obtain ⟨n', m', k'⟩ := y
  obtain ⟨hz, hs⟩ := hx
  obtain ⟨hz', hs'⟩ := hy
  simp only [decValOf] at h hz hs hz' hs'
  have p1 : (0 : ℚ) < 10 ^ k := by positivity
  have p2 : (0 : ℚ) < 10 ^ k' := by positivity
  rw [div_eq_div_iff (ne_of_gt p1) (ne_of_gt p2), signed_cast, signed_cast] at h
  have hi : ((if n then -1 else 1) * ((m * 10 ^ k' : ℕ) : ℤ) : ℤ) =
      (if n' then -1 else 1) * ((m' * 10 ^ k : ℕ) : ℤ) := by exact_mod_cast h
  have pk : 0 < 10 ^ k := by positivity
  have pk' : 0 < 10 ^ k' := by positivity
  -- the same Nat equation, or both zero with opposite signs
  have hnat : m * 10 ^ k' = m' * 10 ^ k ∧ (m = 0 ∨ n = n') := by
    cases n <;> cases n' <;> simp only [ite_true, ite_false, Bool.false_eq_true, one_mul,
      neg_one_mul, neg_inj, Nat.cast_inj] at hi
    · exact ⟨hi, Or.inr rfl⟩
    · have h0 : ((m * 10 ^ k' : ℕ) : ℤ) = 0 ∧ ((m' * 10 ^ k : ℕ) : ℤ) = 0 := by omega
      have h2 := h0.2
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_eq_zero] at h2
      rcases h2 with h1 | h1
      · exact absurd (by exact_mod_cast h1) (hs' rfl)
      · exact absurd h1 (by positivity)
    · have h0 : ((m * 10 ^ k' : ℕ) : ℤ) = 0 ∧ ((m' * 10 ^ k : ℕ) : ℤ) = 0 := by omega
      have h2 := h0.1
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_eq_zero] at h2
      rcases h2 with h1 | h1
      · exact absurd (by exact_mod_cast h1) (hs rfl)
      · exact absurd h1 (by positivity)
    · exact ⟨hi, Or.inr rfl⟩
  obtain ⟨e, hsign⟩ := hnat
  by_cases hm : m = 0
  · subst hm
    have hm' : m' = 0 := by
      simp only [Nat.zero_mul] at e
      rcases Nat.mul_eq_zero.mp e.symm with h1 | h1
      · exact h1
      · omega
    subst hm'
    have hk : k = 0 := by omega
    have hk' : k' = 0 := by omega
    have hn : n = false := by cases n <;> simp_all
    have hn' : n' = false := by cases n' <;> simp_all
    subst hk hk' hn hn'; rfl
  · have hn : n = n' := by rcases hsign with h1 | h1 <;> [exact absurd h1 hm; exact h1]
    subst hn
    rcases lt_trichotomy k k' with hk | hk | hk
    · exact absurd (pow_ten_shift m m' k k' hk e) (by omega)
    · subst hk
      have : m = m' := Nat.eq_of_mul_eq_mul_right pk e
      subst this; rfl
    · exact absurd (pow_ten_shift m' m k' k hk e.symm) (by omega)

/-- Canonicalizing a decimal form is idempotent and keeps its rational value. -/
theorem canonDecimal_idem (s c : String) (h : canonDecimal s = some c) :
    canonDecimal c = some c ∧ decVal c = decVal s := by
  unfold canonDecimal at h
  cases hs : scanDecimal s.toList with
  | none => rw [hs] at h; cases h
  | some x =>
    rw [hs] at h
    obtain ⟨n, m, k⟩ := x
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨hv, hN⟩ := normDec_spec n m k
    generalize hy : normDec n m k = y at hv hN h
    obtain ⟨n', m', k'⟩ := y
    simp only at h
    subst h
    obtain ⟨z, hz, hzn⟩ := scan_render n' m' k' hN
    have hzv := (normDec_spec z.1 z.2.1 z.2.2).1
    rw [hzn] at hzv
    refine ⟨?_, ?_⟩
    · unfold canonDecimal
      rw [hz]
      simp only [Option.map_some]
      rw [hzn]
    · unfold decVal
      rw [hz, hs]
      simp only
      rw [← hv, hzv]

/-- Two valid decimal forms canonicalize to the same text exactly when they denote the same
rational. -/
theorem canonDecimal_eq_iff (s t c d : String) (hs : canonDecimal s = some c)
    (ht : canonDecimal t = some d) : c = d ↔ decVal s = decVal t := by
  have h1 := (canonDecimal_idem s c hs).2
  have h2 := (canonDecimal_idem t d ht).2
  constructor
  · rintro rfl; rw [← h1, ← h2]
  · intro h
    unfold canonDecimal at hs ht
    unfold decVal at h
    cases e1 : scanDecimal s.toList with
    | none => rw [e1] at hs; cases hs
    | some x =>
      cases e2 : scanDecimal t.toList with
      | none => rw [e2] at ht; cases ht
      | some y =>
        rw [e1] at hs h; rw [e2] at ht h
        simp only [Option.map_some, Option.some.injEq] at hs ht h
        obtain ⟨n, m, k⟩ := x
        obtain ⟨n', m', k'⟩ := y
        obtain ⟨hv1, hN1⟩ := normDec_spec n m k
        obtain ⟨hv2, hN2⟩ := normDec_spec n' m' k'
        have := normal_unique _ _ hN1 hN2 (by rw [hv1, hv2]; exact h)
        rw [← hs, ← ht]
        simp only at this ⊢
        rw [this]

end Tiramemsu.Codec
