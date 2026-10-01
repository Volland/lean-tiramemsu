/-
The numeric meaning of `Double64` (Mathlib's `ℚ`), the IEEE 754 round-to-nearest-even
reference `roundBinary64`, field extraction of the bit layout, and the exact logarithms the
parser and printer compute in `Nat`.
-/
import Tiramemsu.Codec.Double.Print
import Std.Tactic.BVDecide
import Mathlib.Data.Int.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-! ## Reference semantics -/

/-- The magnitude `M · 2^E` of a finite value. -/
def Double64.mag (x : Double64) : ℚ := (x.mantExp.1 : ℚ) * (2 : ℚ) ^ x.mantExp.2

/-- The rational value of a finite double (`none` for infinities and NaN). -/
def Double64.toRat? (x : Double64) : Option ℚ :=
  if x.isFinite then some ((if x.neg then -1 else 1) * x.mag) else none

/-- Round half to even of a non-negative rational. -/
def rhe (r : ℚ) : ℕ :=
  let f := ⌊r⌋₊
  if r - f < 1 / 2 then f
  else if 1 / 2 < r - f then f + 1
  else if f % 2 = 0 then f else f + 1

/-- The IEEE 754 binary64 value nearest to `±r` (`r ≥ 0` is the magnitude), ties to even:
the exponent `E` is that of `r`'s binade (at least the subnormal exponent), the significand is
`r / 2^E` rounded half to even, and `ofMantExp` normalizes a carry and overflows to `±∞`. -/
def roundBinary64 (neg : Bool) (r : ℚ) : Double64 :=
  if r ≤ 0 then Double64.zero neg
  else
    let E := max (Int.log 2 r) (-1022) - 52
    Double64.ofMantExp neg (rhe (r / (2 : ℚ) ^ E)) E

/-! ## Bit fields -/

theorem fields_bits (b e f : UInt64) (hb : b < 2) (he : e < 2048)
    (hf : f < (1 : UInt64) <<< 52) :
    ((b <<< 63) ||| (e <<< 52) ||| f) >>> 63 = b ∧
      (((b <<< 63) ||| (e <<< 52) ||| f) >>> 52) &&& 0x7FF = e ∧
      ((b <<< 63) ||| (e <<< 52) ||| f) &&& 0xFFFFFFFFFFFFF = f := by
  bv_decide

theorem bits_fields (x : UInt64) :
    x = ((x >>> 63) <<< 63) ||| ((((x >>> 52) &&& 0x7FF)) <<< 52) ||| (x &&& 0xFFFFFFFFFFFFF) := by
  bv_decide

theorem field_bounds (x : UInt64) :
    (x >>> (63 : UInt64)) < (2 : UInt64) ∧ ((x >>> (52 : UInt64)) &&& (0x7FF : UInt64)) < (2048 : UInt64) ∧
      (x &&& (0xFFFFFFFFFFFFF : UInt64)) < ((1 : UInt64) <<< (52 : UInt64)) := by
  bv_decide

theorem uint64_toNat_toUInt64 (n : Nat) (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq]; exact UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using h)

theorem Double64.ofFields_fields (neg : Bool) (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    (Double64.ofFields neg e f).neg = neg ∧ (Double64.ofFields neg e f).biasedExp = e ∧
      (Double64.ofFields neg e f).frac = f := by
  have he' : e.toUInt64 < 2048 := by
    rw [UInt64.lt_iff_toNat_lt, uint64_toNat_toUInt64 e (by omega)]; simpa using he
  have hf' : f.toUInt64 < (1 : UInt64) <<< 52 := by
    rw [UInt64.lt_iff_toNat_lt, uint64_toNat_toUInt64 f (by omega)]
    have : ((1 : UInt64) <<< 52).toNat = 2 ^ 52 := by decide
    rw [this]; exact hf
  have hb : (if neg then (1 : UInt64) else 0) < 2 := by split <;> decide
  obtain ⟨h1, h2, h3⟩ := fields_bits _ _ _ hb he' hf'
  simp only [Double64.ofFields, Double64.neg, Double64.biasedExp, Double64.frac, h1, h2, h3]
  refine ⟨by cases neg <;> decide, uint64_toNat_toUInt64 e (by omega), uint64_toNat_toUInt64 f (by omega)⟩

theorem sign_bit (b : UInt64) : (if (b >>> 63 == 1) = true then (1 : UInt64) else 0) = b >>> 63 := by
  have : b >>> 63 = 0 ∨ b >>> 63 = 1 := by bv_decide
  rcases this with h | h <;> simp [h]

theorem Double64.eq_ofFields (x : Double64) : x = Double64.ofFields x.neg x.biasedExp x.frac := by
  obtain ⟨b⟩ := x
  unfold Double64.ofFields Double64.neg Double64.biasedExp Double64.frac
  congr 1
  show b = (if (b >>> 63 == 1) = true then (1 : UInt64) else 0) <<< (63 : UInt64) |||
      ((b >>> (52 : UInt64)) &&& (2047 : UInt64)).toNat.toUInt64 <<< (52 : UInt64) |||
      (b &&& (4503599627370495 : UInt64)).toNat.toUInt64
  rw [sign_bit]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_toNat]
  exact bits_fields b

theorem Double64.biasedExp_lt (x : Double64) : x.biasedExp < 2048 := by
  have := (field_bounds x.bits).2.1
  unfold Double64.biasedExp
  have h : ((x.bits >>> 52) &&& 0x7FF).toNat < (2048 : UInt64).toNat := UInt64.lt_iff_toNat_lt.mp this
  simpa using h

theorem Double64.frac_lt (x : Double64) : x.frac < 2 ^ 52 := by
  have := (field_bounds x.bits).2.2
  unfold Double64.frac
  have h := UInt64.lt_iff_toNat_lt.mp this
  have : ((1 : UInt64) <<< 52).toNat = 2 ^ 52 := by decide
  rw [this] at h; exact h

theorem Double64.ofFields_inj {n n' : Bool} {e e' f f' : Nat} (he : e < 2048) (he' : e' < 2048)
    (hf : f < 2 ^ 52) (hf' : f' < 2 ^ 52)
    (h : Double64.ofFields n e f = Double64.ofFields n' e' f') : n = n' ∧ e = e' ∧ f = f' := by
  have a := Double64.ofFields_fields n e f he hf
  have b := Double64.ofFields_fields n' e' f' he' hf'
  rw [h] at a
  exact ⟨a.1.symm.trans b.1, a.2.1.symm.trans b.2.1, a.2.2.symm.trans b.2.2⟩

/-! ## Exact logarithms -/

theorem natLogAux_spec (b : Nat) (hb : 1 < b) (fuel n : Nat) (hn : 1 ≤ n) (hf : n ≤ fuel) :
    b ^ natLogAux b fuel n ≤ n ∧ n < b ^ (natLogAux b fuel n + 1) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold natLogAux
    by_cases h : b ≤ n
    · have hc : (b ≤ n && 1 < b) = true := by simp [h, hb]
      rw [if_pos hc]
      have hq : 1 ≤ n / b := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      have hlt : n / b < n := Nat.div_lt_self (by omega) hb
      obtain ⟨i1, i2⟩ := ih (n / b) hq (by omega)
      constructor
      · rw [Nat.pow_succ]
        calc b ^ natLogAux b fuel (n / b) * b ≤ n / b * b := Nat.mul_le_mul_right _ i1
          _ ≤ n := Nat.div_mul_le_self n b
      · rw [Nat.pow_succ]
        have : n < (n / b + 1) * b := by
          have := Nat.lt_div_mul_add (a := n) (b := b) (by omega)
          rw [Nat.add_mul, Nat.one_mul]; omega
        calc n < (n / b + 1) * b := this
          _ ≤ b ^ (natLogAux b fuel (n / b) + 1) * b := Nat.mul_le_mul_right _ i2
    · have hc : ¬ (b ≤ n && 1 < b) = true := by simp [h]
      rw [if_neg hc]
      simp; omega

theorem natLog_spec (b n : Nat) (hb : 1 < b) (hn : 1 ≤ n) :
    b ^ natLog b n ≤ n ∧ n < b ^ (natLog b n + 1) :=
  natLogAux_spec b hb n n hn (le_refl _)

theorem log2_spec (n : Nat) (hn : n ≠ 0) : 2 ^ n.log2 ≤ n ∧ n < 2 ^ (n.log2 + 1) :=
  ⟨Nat.log2_self_le hn, Nat.lt_log2_self⟩

/-- `Int.log` is determined by the bracketing powers. -/
theorem int_log_eq {b : Nat} (hb : 1 < b) {r : ℚ} (hr : 0 < r) {t : Int}
    (h1 : (b : ℚ) ^ t ≤ r) (h2 : r < (b : ℚ) ^ (t + 1)) : Int.log b r = t := by
  have a := (Int.zpow_le_iff_le_log hb hr).mp h1
  have c := (Int.lt_zpow_iff_log_lt hb hr).mp h2
  omega

theorem pow2Le_iff (t : Int) (a b : Nat) (hb : 0 < b) :
    pow2Le t a b = true ↔ (2 : ℚ) ^ t ≤ (a : ℚ) / b := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  unfold pow2Le
  rw [le_div_iff₀ hbq]
  split
  · rename_i ht
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    simp only [Int.toNat_natCast, Nat.shiftLeft_eq, decide_eq_true_eq, zpow_natCast]
    rw [mul_comm]; exact_mod_cast Iff.rfl
  · rename_i ht
    obtain ⟨n, hn⟩ : ∃ n : Nat, t = -(n : Int) := ⟨(-t).toNat, by omega⟩
    subst hn
    simp only [neg_neg, Int.toNat_natCast, Nat.shiftLeft_eq, decide_eq_true_eq, zpow_neg,
      zpow_natCast]
    have h2 : (0 : ℚ) < 2 ^ n := by positivity
    rw [← div_eq_inv_mul, div_le_iff₀ h2]
    exact_mod_cast Iff.rfl

theorem pow10Le_iff (t : Int) (a b : Nat) (hb : 0 < b) :
    pow10Le t a b = true ↔ (10 : ℚ) ^ t ≤ (a : ℚ) / b := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  unfold pow10Le
  rw [le_div_iff₀ hbq]
  split
  · rename_i ht
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    simp only [Int.toNat_natCast, decide_eq_true_eq, zpow_natCast]
    rw [mul_comm]; exact_mod_cast Iff.rfl
  · rename_i ht
    obtain ⟨n, hn⟩ : ∃ n : Nat, t = -(n : Int) := ⟨(-t).toNat, by omega⟩
    subst hn
    simp only [neg_neg, Int.toNat_natCast, decide_eq_true_eq, zpow_neg, zpow_natCast]
    have h2 : (0 : ℚ) < 10 ^ n := by positivity
    rw [← div_eq_inv_mul, div_le_iff₀ h2]
    exact_mod_cast Iff.rfl

/-- Bracketing of a ratio by the logarithms of its parts. -/
theorem ratio_bracket (base : Nat) (hb : 1 < base) (a b la lb : Nat) (ha : 0 < a) (hb0 : 0 < b)
    (ha1 : base ^ la ≤ a) (ha2 : a < base ^ (la + 1)) (hb1 : base ^ lb ≤ b) (hb2 : b < base ^ (lb + 1)) :
    (base : ℚ) ^ ((la : Int) - lb - 1) < (a : ℚ) / b ∧ (a : ℚ) / b < (base : ℚ) ^ ((la : Int) - lb + 1) := by
  have hB : (0 : ℚ) < base := by exact_mod_cast (show 0 < base by omega)
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
  have ha1' : (base : ℚ) ^ la ≤ a := by exact_mod_cast ha1
  have ha2' : (a : ℚ) < (base : ℚ) ^ (la + 1) := by exact_mod_cast ha2
  have hb1' : (base : ℚ) ^ lb ≤ b := by exact_mod_cast hb1
  have hb2' : (b : ℚ) < (base : ℚ) ^ (lb + 1) := by exact_mod_cast hb2
  have e1 : (base : ℚ) ^ ((la : Int) - lb - 1) = (base : ℚ) ^ la / (base : ℚ) ^ (lb + 1) := by
    rw [show ((la : Int) - lb - 1) = (la : Int) - ((lb + 1 : Nat) : Int) by push_cast; ring,
      zpow_sub₀ (ne_of_gt hB), zpow_natCast, zpow_natCast]
  have e2 : (base : ℚ) ^ ((la : Int) - lb + 1) = (base : ℚ) ^ (la + 1) / (base : ℚ) ^ lb := by
    rw [show ((la : Int) - lb + 1) = ((la + 1 : Nat) : Int) - (lb : Int) by push_cast; ring,
      zpow_sub₀ (ne_of_gt hB), zpow_natCast, zpow_natCast]
  rw [e1, e2]
  have p1 : (0 : ℚ) < (base : ℚ) ^ (lb + 1) := by positivity
  have p2 : (0 : ℚ) < (base : ℚ) ^ lb := by positivity
  constructor
  · rw [div_lt_div_iff₀ p1 hbq]
    calc (base : ℚ) ^ la * b ≤ a * b := by gcongr
      _ < a * (base : ℚ) ^ (lb + 1) := by gcongr
  · rw [div_lt_div_iff₀ hbq p2]
    calc (a : ℚ) * (base : ℚ) ^ lb ≤ a * b := by gcongr
      _ < (base : ℚ) ^ (la + 1) * b := by gcongr

theorem floorLog2Ratio_eq (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    floorLog2Ratio a b = Int.log 2 ((a : ℚ) / b) := by
  have hr : (0 : ℚ) < (a : ℚ) / b := by positivity
  obtain ⟨a1, a2⟩ := log2_spec a (by omega)
  obtain ⟨b1, b2⟩ := log2_spec b (by omega)
  obtain ⟨lo, hi⟩ := ratio_bracket 2 (by decide) a b _ _ ha hb a1 a2 b1 b2
  push_cast at lo hi
  unfold floorLog2Ratio
  dsimp only
  split
  · rename_i h
    rw [pow2Le_iff _ _ _ hb] at h
    exact (int_log_eq (b := 2) (by decide) hr (by exact_mod_cast h) (by exact_mod_cast hi)).symm
  · rename_i h
    rw [pow2Le_iff _ _ _ hb, not_le] at h
    exact (int_log_eq (b := 2) (by decide) hr (by exact_mod_cast le_of_lt lo)
      (by rw [sub_add_cancel]; exact_mod_cast h)).symm

theorem floorLog10Ratio_eq (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    floorLog10Ratio a b = Int.log 10 ((a : ℚ) / b) := by
  have hr : (0 : ℚ) < (a : ℚ) / b := by positivity
  obtain ⟨a1, a2⟩ := natLog_spec 10 a (by decide) ha
  obtain ⟨b1, b2⟩ := natLog_spec 10 b (by decide) hb
  obtain ⟨lo, hi⟩ := ratio_bracket 10 (by decide) a b _ _ ha hb a1 a2 b1 b2
  push_cast at lo hi
  unfold floorLog10Ratio
  dsimp only
  split
  · rename_i h
    rw [pow10Le_iff _ _ _ hb] at h
    exact (int_log_eq (b := 10) (by decide) hr (by exact_mod_cast h) (by exact_mod_cast hi)).symm
  · rename_i h
    rw [pow10Le_iff _ _ _ hb, not_le] at h
    exact (int_log_eq (b := 10) (by decide) hr (by exact_mod_cast le_of_lt lo)
      (by rw [sub_add_cancel]; exact_mod_cast h)).symm

end Tiramemsu.Codec
