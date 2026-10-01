/-
Correctness of the exact `xsd:double` parser: every accepted numeric form parses to the
round-to-nearest-even binary64 value of its exact decimal value (`roundBinary64`), including
the overflow and underflow clamps, which never form a power.
-/
import TiramemsuProofs.Codec.Double.Basic

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-! ## Rounding a ratio of naturals -/

/-- `rhe` of a ratio of naturals is the integer computation of `roundRatio`. -/
theorem rhe_ratio (num den : Nat) (hd : 0 < den) :
    rhe ((num : ℚ) / den) =
      (if 2 * (num % den) > den || (2 * (num % den) == den && (num / den) % 2 == 1)
        then num / den + 1 else num / den) := by
  have hdq : (0 : ℚ) < den := by exact_mod_cast hd
  have hfloor : ⌊(num : ℚ) / den⌋₊ = num / den := Nat.floor_div_eq_div num den
  have hsplit : (num : ℚ) / den - ((num / den : ℕ) : ℚ) = ((num % den : ℕ) : ℚ) / den := by
    have e : (num : ℚ) = den * ((num / den : ℕ) : ℚ) + ((num % den : ℕ) : ℚ) := by
      exact_mod_cast (Nat.div_add_mod num den).symm
    rw [e]; field_simp; ring
  unfold rhe
  simp only [hfloor, hsplit]
  have c1 : ((num % den : ℕ) : ℚ) / den < 1 / 2 ↔ 2 * (num % den) < den := by
    rw [div_lt_div_iff₀ hdq (by norm_num), one_mul]
    constructor
    · intro h; have : ((2 * (num % den) : ℕ) : ℚ) < den := by push_cast; linarith
      exact_mod_cast this
    · intro h; have : ((2 * (num % den) : ℕ) : ℚ) < den := by exact_mod_cast h
      push_cast at this; linarith
  have c2 : 1 / 2 < ((num % den : ℕ) : ℚ) / den ↔ den < 2 * (num % den) := by
    rw [div_lt_div_iff₀ (by norm_num) hdq, one_mul]
    constructor
    · intro h; have : (den : ℚ) < ((2 * (num % den) : ℕ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    · intro h; have : (den : ℚ) < ((2 * (num % den) : ℕ) : ℚ) := by exact_mod_cast h
      push_cast at this; linarith
  by_cases h1 : 2 * (num % den) < den
  · rw [if_pos (c1.mpr h1)]
    have : ¬ (2 * (num % den) > den || (2 * (num % den) == den && num / den % 2 == 1)) = true := by
      simp; omega
    rw [if_neg this]
  · rw [if_neg (fun h => h1 (c1.mp h))]
    by_cases h2 : den < 2 * (num % den)
    · rw [if_pos (c2.mpr h2)]
      have : (2 * (num % den) > den || (2 * (num % den) == den && num / den % 2 == 1)) = true := by
        simp; omega
      rw [if_pos this]
    · rw [if_neg (fun h => h2 (c2.mp h))]
      have heq : 2 * (num % den) = den := by omega
      by_cases h3 : num / den % 2 = 0
      · rw [if_pos h3]
        have : ¬ (2 * (num % den) > den || (2 * (num % den) == den && num / den % 2 == 1)) = true := by
          simp; omega
        rw [if_neg this]
      · rw [if_neg h3]
        have : (2 * (num % den) > den || (2 * (num % den) == den && num / den % 2 == 1)) = true := by
          simp; omega
        rw [if_pos this]

/-- `roundRatio` computes the reference rounding of `a / b`. -/
theorem roundRatio_eq (neg : Bool) (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    roundRatio neg a b = roundBinary64 neg ((a : ℚ) / b) := by
  have hr : (0 : ℚ) < (a : ℚ) / b := by positivity
  unfold roundRatio roundBinary64
  rw [if_neg (not_le.mpr hr), floorLog2Ratio_eq a b ha hb]
  dsimp only
  generalize max (Int.log 2 ((a : ℚ) / b)) (-1022) - 52 = E
  congr 1
  by_cases hE : 0 ≤ E
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hE
    simp only [hE, ite_true, Int.toNat_natCast, Nat.shiftLeft_eq]
    rw [← rhe_ratio a (b * 2 ^ n) (by positivity)]
    congr 1
    push_cast
    rw [zpow_natCast, div_div]
  · obtain ⟨n, hn⟩ : ∃ n : Nat, E = -(n : Int) := ⟨(-E).toNat, by omega⟩
    subst hn
    simp only [hE, ite_false, neg_neg, Int.toNat_natCast, Nat.shiftLeft_eq]
    rw [← rhe_ratio (a * 2 ^ n) b hb]
    congr 1
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp

/-! ## Overflow and underflow -/

theorem rhe_bounds (x : ℚ) (A B : Nat) (h1 : (A : ℚ) ≤ x) (h2 : x < B) : A ≤ rhe x ∧ rhe x ≤ B := by
  have hx : 0 ≤ x := le_trans (by positivity) h1
  have f1 : A ≤ ⌊x⌋₊ := Nat.le_floor h1
  have f2 : ⌊x⌋₊ < B := (Nat.floor_lt hx).mpr h2
  unfold rhe
  dsimp only
  split_ifs <;> omega

theorem rhe_small (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1 / 2) : rhe x = 0 := by
  have f : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  unfold rhe
  simp only [f, Nat.cast_zero, sub_zero]
  rw [if_pos h1]

theorem two_zpow_pos (t : Int) : (0 : ℚ) < (2 : ℚ) ^ t := zpow_pos (by norm_num) t

/-- The binade facts used by the rounding: for `r > 0` in the normal range, `r / 2^E` lies in
`[2^52, 2^53)`. -/
theorem scaled_bounds (r : ℚ) (hr : 0 < r) (h : -1022 ≤ Int.log 2 r) :
    (2 : ℚ) ^ (52 : Int) ≤ r / (2 : ℚ) ^ (max (Int.log 2 r) (-1022) - 52) ∧
      r / (2 : ℚ) ^ (max (Int.log 2 r) (-1022) - 52) < (2 : ℚ) ^ (53 : Int) := by
  rw [max_eq_left h]
  have l1 := Int.zpow_log_le_self (b := 2) (by decide) hr
  have l2 := Int.lt_zpow_succ_log_self (b := 2) (by decide) r
  push_cast at l1 l2
  have hp := two_zpow_pos (Int.log 2 r - 52)
  constructor
  · rw [le_div_iff₀ hp, ← zpow_add₀ (by norm_num)]; simpa using l1
  · rw [div_lt_iff₀ hp, ← zpow_add₀ (by norm_num)]
    rw [show (53 : Int) + (Int.log 2 r - 52) = Int.log 2 r + 1 by ring]; exact l2

theorem Double64.zero_eq_ofFields (neg : Bool) : Double64.zero neg = Double64.ofFields neg 0 0 := by
  cases neg <;> rfl

/-- Magnitudes of at least `2^1024` round to `±∞`. -/
theorem round_overflow (neg : Bool) (r : ℚ) (h : (2 : ℚ) ^ (1024 : Int) ≤ r) :
    roundBinary64 neg r = Double64.inf neg := by
  have hr : 0 < r := lt_of_lt_of_le (two_zpow_pos _) h
  have ht : 1024 ≤ Int.log 2 r := (Int.zpow_le_iff_le_log (b := 2) (by decide) hr).mp (by simpa using h)
  obtain ⟨s1, s2⟩ := scaled_bounds r hr (by omega)
  unfold roundBinary64
  rw [if_neg (not_le.mpr hr)]
  dsimp only
  generalize hE : max (Int.log 2 r) (-1022) - 52 = E at s1 s2
  have hE' : 972 ≤ E := by omega
  obtain ⟨m1, m2⟩ := rhe_bounds _ (2 ^ 52) (2 ^ 53) (by exact_mod_cast s1) (by exact_mod_cast s2)
  generalize rhe (r / 2 ^ E) = M at m1 m2
  unfold Double64.ofMantExp
  dsimp only
  split_ifs <;> first | omega | rfl

/-- Magnitudes below `2^−1075` round to `±0`. -/
theorem round_underflow (neg : Bool) (r : ℚ) (hr : 0 < r) (h : r < (2 : ℚ) ^ (-1075 : Int)) :
    roundBinary64 neg r = Double64.zero neg := by
  have ht : Int.log 2 r < -1075 := (Int.lt_zpow_iff_log_lt (b := 2) (by decide) hr).mp (by simpa using h)
  unfold roundBinary64
  rw [if_neg (not_le.mpr hr)]
  dsimp only
  rw [show max (Int.log 2 r) (-1022) - 52 = -1074 by omega]
  have hs : r / (2 : ℚ) ^ (-1074 : Int) < 1 / 2 := by
    rw [div_lt_iff₀ (two_zpow_pos _)]
    calc r < (2 : ℚ) ^ (-1075 : Int) := h
      _ = 1 / 2 * (2 : ℚ) ^ (-1074 : Int) := by
        rw [show (-1075 : Int) = -1 + -1074 by norm_num, zpow_add₀ (by norm_num)]; norm_num
  rw [rhe_small _ (le_of_lt (div_pos hr (two_zpow_pos _))) hs]
  unfold Double64.ofMantExp
  simp [Double64.zero_eq_ofFields]

/-! ## Decimal values -/

theorem numDigits_spec (m : Nat) (hm : 1 ≤ m) :
    10 ^ (numDigits m - 1) ≤ m ∧ m < 10 ^ numDigits m := by
  have := natLog_spec 10 m (by decide) hm
  unfold numDigits; simpa using this

theorem pow_2_1024_le : (2 : ℕ) ^ 1024 ≤ 10 ^ 310 := by decide +kernel
theorem pow_2_1075_lt : (2 : ℕ) ^ 1075 < 10 ^ 325 := by decide +kernel

/-- `roundDec` computes the reference rounding of `m · 10^q`, through the clamps. -/
theorem roundDec_eq (neg : Bool) (m : Nat) (q : Int) :
    roundDec neg m q = roundBinary64 neg ((m : ℚ) * (10 : ℚ) ^ q) := by
  unfold roundDec
  by_cases hm : m = 0
  · subst hm
    simp [roundBinary64]
  rw [if_neg hm]
  have hmq : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have h10 : (0 : ℚ) < (10 : ℚ) ^ q := zpow_pos (by norm_num) q
  obtain ⟨d1, d2⟩ := numDigits_spec m (by omega)
  have d1' : ((10 : ℚ) ^ ((numDigits m : Int) - 1)) ≤ m := by
    have : (1 : Int) ≤ numDigits m := by unfold numDigits; omega
    rw [show ((numDigits m : Int) - 1) = ((numDigits m - 1 : Nat) : Int) by omega, zpow_natCast]
    exact_mod_cast d1
  have d2' : (m : ℚ) < (10 : ℚ) ^ (numDigits m : Int) := by rw [zpow_natCast]; exact_mod_cast d2
  dsimp only
  split_ifs with h1 h2 h3
  · -- overflow: m · 10^q ≥ 10^310 > 2^1024
    symm; apply round_overflow
    calc (2 : ℚ) ^ (1024 : Int) ≤ (10 : ℚ) ^ (310 : Int) := by
          rw [show (1024 : Int) = ((1024 : Nat) : Int) by norm_num,
            show (310 : Int) = ((310 : Nat) : Int) by norm_num, zpow_natCast, zpow_natCast]
          exact_mod_cast pow_2_1024_le
      _ ≤ (10 : ℚ) ^ ((numDigits m : Int) - 1 + q) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = (10 : ℚ) ^ ((numDigits m : Int) - 1) * (10 : ℚ) ^ q := zpow_add₀ (by norm_num) _ _
      _ ≤ m * (10 : ℚ) ^ q := by gcongr
  · -- underflow: m · 10^q < 10^−324 < 2^−1075
    symm; apply round_underflow _ _ (mul_pos hmq h10)
    calc (m : ℚ) * (10 : ℚ) ^ q < (10 : ℚ) ^ (numDigits m : Int) * (10 : ℚ) ^ q := by gcongr
      _ = (10 : ℚ) ^ ((numDigits m : Int) + q) := (zpow_add₀ (by norm_num) _ _).symm
      _ ≤ (10 : ℚ) ^ (-325 : Int) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ < (2 : ℚ) ^ (-1075 : Int) := by
          rw [show (-325 : Int) = -((325 : Nat) : Int) by norm_num,
            show (-1075 : Int) = -((1075 : Nat) : Int) by norm_num, zpow_neg, zpow_neg, zpow_natCast,
            zpow_natCast, inv_lt_inv₀ (by positivity) (by positivity)]
          exact_mod_cast pow_2_1075_lt
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h3
    rw [roundRatio_eq neg _ _ (by positivity) (by norm_num)]
    congr 1
    push_cast; simp [zpow_natCast]
  · obtain ⟨n, hn⟩ : ∃ n : Nat, q = -(n : Int) := ⟨(-q).toNat, by omega⟩
    subst hn
    rw [roundRatio_eq neg _ _ (by positivity) (by positivity)]
    congr 1
    simp only [neg_neg, Int.toNat_natCast, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast]
    rfl

/-- The exact decimal value of a numeric form: `(int ++ frac) · 10^(±exp − |frac|)`. -/
def DoubleSyntax.decValue (intDigits fracDigits : List Char) (expNeg : Bool) (expDigits : List Char) : ℚ :=
  (Nat.ofDigitChars 10 (intDigits ++ fracDigits) 0 : ℚ) * (10 : ℚ) ^ DoubleSyntax.decExp fracDigits expNeg expDigits

/-- Parser correctness: every accepted numeric form parses to the round-to-nearest-even binary64
value of its exact decimal value. -/
theorem parseDouble_correct (s : String) (neg : Bool) (i f : List Char) (en : Bool) (ed : List Char)
    (h : scanDouble s = some (.numeric neg i f en ed)) :
    parseDouble s = some (roundBinary64 neg (DoubleSyntax.decValue i f en ed)) := by
  unfold parseDouble
  rw [h]
  simp only [Option.map_some, DoubleSyntax.value, roundDec_eq, DoubleSyntax.decValue]

/-- The special forms parse to their values. -/
theorem parseDouble_special (s : String) (x : Double64) (h : scanDouble s = some (.special x)) :
    parseDouble s = some x := by
  unfold parseDouble; rw [h]; rfl

/-! ## Parsed values are never a non-canonical NaN -/

theorem Double64.ofFields_finite (neg : Bool) (e f : Nat) (he : e < 2047) (hf : f < 2 ^ 52) :
    (Double64.ofFields neg e f).isNaN = false := by
  have := Double64.ofFields_fields neg e f (by omega) hf
  simp [Double64.isNaN, this.2.1]; omega

theorem Double64.inf_not_nan (neg : Bool) : (Double64.inf neg).isNaN = false := by
  cases neg <;> decide

theorem Double64.ofMantExp_not_nan (neg : Bool) (M : Nat) (E : Int) (hM : M ≤ 2 ^ 53) :
    (Double64.ofMantExp neg M E).isNaN = false := by
  unfold Double64.ofMantExp
  dsimp only
  split_ifs with h1 h2 h3 h4 h5 h6
  all_goals first
    | exact Double64.inf_not_nan neg
    | (apply Double64.ofFields_finite <;> omega)

theorem rhe_le_of_lt (x : ℚ) (hx : 0 ≤ x) (B : Nat) (h : x < B) : rhe x ≤ B :=
  (rhe_bounds x 0 B (by simpa using hx) h).2

theorem roundBinary64_not_nan (neg : Bool) (r : ℚ) : (roundBinary64 neg r).isNaN = false := by
  unfold roundBinary64
  split
  · cases neg <;> decide
  · rename_i hr
    push_neg at hr
    dsimp only
    apply Double64.ofMantExp_not_nan
    apply rhe_le_of_lt _ (le_of_lt (div_pos hr (two_zpow_pos _)))
    by_cases ht : -1022 ≤ Int.log 2 r
    · have := (scaled_bounds r hr ht).2
      have e : (2 : ℚ) ^ (53 : Int) = ((2 ^ 53 : ℕ) : ℚ) := by norm_num
      rw [e] at this; exact this
    · rw [show max (Int.log 2 r) (-1022) - 52 = -1074 by omega]
      have l2 := Int.lt_zpow_succ_log_self (b := 2) (by decide) r
      push_cast at l2
      have : r < (2 : ℚ) ^ (-1022 : Int) :=
        lt_of_lt_of_le l2 (zpow_le_zpow_right₀ (by norm_num) (by omega))
      rw [div_lt_iff₀ (two_zpow_pos _)]
      calc r < (2 : ℚ) ^ (-1022 : Int) := this
        _ ≤ ((2 ^ 53 : ℕ) : ℚ) * (2 : ℚ) ^ (-1074 : Int) := by
          rw [show ((2 ^ 53 : ℕ) : ℚ) = (2 : ℚ) ^ (53 : Int) by norm_num, ← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)

/-- A parsed double is never a NaN other than the canonical one. -/
theorem parseDouble_canon (s : String) (x : Double64) (h : parseDouble s = some x) : x.canon = x := by
  unfold parseDouble at h
  cases hs : scanDouble s with
  | none => rw [hs] at h; cases h
  | some syn =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    cases syn with
    | special y =>
      unfold scanDouble at hs
      split_ifs at hs <;> (try cases hs) <;> (try decide)
      · -- scanNumeric never produces a special
        unfold scanNumeric at hs
        dsimp only at hs
        split_ifs at hs <;> (try cases hs)
        split at hs <;> (try cases hs)
        split_ifs at hs <;> cases hs
    | numeric neg i f en ed =>
      simp only [DoubleSyntax.value, roundDec_eq, Double64.canon, roundBinary64_not_nan]
      rfl

end Tiramemsu.Codec
