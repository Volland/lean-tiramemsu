/-
Proofs of timezone codes and `DATETIME` packing: the code is a bijection between
`{none} ∪ [−840, 840]` and `0 … 1681`, unpacking a packed (instant, timezone) gives it back,
packing an accepted payload's unpacking gives the payload back, and `id >> 15` is the instant.
-/
import Tiramemsu.Codec.DateTime
import Std.Tactic.BVDecide
import Mathlib.Tactic.NormNum

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Dates And Times]]

/-! ## Timezone codes -/

theorem tzOfCode_tzCode (tz : Option Int) (h : tzValid tz = true) : tzOfCode (tzCode tz) = .ok tz := by
  cases tz with
  | none => rfl
  | some m =>
    simp [tzValid, maxOffsetMin] at h
    have hc : tzCode (some m) = (m + 841).toNat := rfl
    unfold tzOfCode
    rw [if_neg (by rw [hc]; omega), if_pos (by rw [hc]; omega), hc]
    simp only [Except.ok.injEq, Option.some.injEq]
    omega

theorem tzCode_tzOfCode (c : Nat) (tz : Option Int) (h : tzOfCode c = .ok tz) :
    tzValid tz = true ∧ tzCode tz = c := by
  unfold tzOfCode at h
  split_ifs at h with h1 h2
  · cases h; simp [tzValid, tzCode, h1]
  · cases h
    simp [tzValid, tzCode, maxOffsetMin]
    omega

theorem tzOfCode_reject (c : Nat) (h : 1681 < c) :
    tzOfCode c = .error (.invalidTerm s!"timezone code {c} out of range") := by
  unfold tzOfCode
  split_ifs <;> first | omega | rfl

theorem tzCode_le (tz : Option Int) (h : tzValid tz = true) : tzCode tz ≤ 1681 := by
  cases tz with
  | none => simp [tzCode]
  | some m =>
    simp [tzValid, maxOffsetMin] at h
    simp only [tzCode]; omega

theorem tzCode_inj {a b : Option Int} (ha : tzValid a = true) (hb : tzValid b = true)
    (h : tzCode a = tzCode b) : a = b := by
  have h1 := tzOfCode_tzCode a ha
  have h2 := tzOfCode_tzCode b hb
  rw [h] at h1
  rw [h1] at h2
  exact Except.ok.inj h2

/-! ## Int64 helpers -/

theorem int64_ofInt_le_iff {a b : Int} (ha : -2 ^ 63 ≤ a) (ha' : a < 2 ^ 63) (hb : -2 ^ 63 ≤ b)
    (hb' : b < 2 ^ 63) : Int64.ofInt a ≤ Int64.ofInt b ↔ a ≤ b := by
  rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le ha ha', Int64.toInt_ofInt_of_le hb hb']

theorem int64_ofInt_lt_iff {a b : Int} (ha : -2 ^ 63 ≤ a) (ha' : a < 2 ^ 63) (hb : -2 ^ 63 ≤ b)
    (hb' : b < 2 ^ 63) : Int64.ofInt a < Int64.ofInt b ↔ a < b := by
  rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofInt_of_le ha ha', Int64.toInt_ofInt_of_le hb hb']

theorem int64_ofInt_eq_iff {a b : Int} (ha : -2 ^ 63 ≤ a) (ha' : a < 2 ^ 63) (hb : -2 ^ 63 ≤ b)
    (hb' : b < 2 ^ 63) : Int64.ofInt a = Int64.ofInt b ↔ a = b := by
  rw [← Int64.toInt_inj, Int64.toInt_ofInt_of_le ha ha', Int64.toInt_ofInt_of_le hb hb']

/-- Range of an `Int64.ofInt`, as Int64 comparisons with constants. -/
theorem int64_bounds {v lo hi : Int} (hlo : -2 ^ 63 ≤ lo) (hhi : hi ≤ 2 ^ 63) (h0 : lo ≤ v) (h1 : v < hi) :
    Int64.ofInt lo ≤ Int64.ofInt v ∧ Int64.ofInt v < Int64.ofInt hi ∨ hi = 2 ^ 63 := by
  by_cases h : hi = 2 ^ 63
  · exact Or.inr h
  · left
    exact ⟨(int64_ofInt_le_iff hlo (by omega) (by omega) (by omega)).mpr h0,
      (int64_ofInt_lt_iff (by omega) (by omega) (by omega) (by omega)).mpr h1⟩

theorem int64_ofInt_ge {v lo : Int} (hlo : -2 ^ 63 ≤ lo) (hlo' : lo < 2 ^ 63) (h0 : lo ≤ v)
    (h1 : v < 2 ^ 63) : Int64.ofInt lo ≤ Int64.ofInt v :=
  (int64_ofInt_le_iff hlo hlo' (by omega) h1).mpr h0

theorem int64_ofInt_lt {v hi : Int} (hhi : -2 ^ 63 ≤ hi) (hhi' : hi < 2 ^ 63) (h0 : -2 ^ 63 ≤ v)
    (h1 : v < hi) : Int64.ofInt v < Int64.ofInt hi :=
  (int64_ofInt_lt_iff h0 (by omega) hhi hhi').mpr h1

/-! ## Packing -/

/-- Bit layout of the `DATETIME` payload and id. -/
theorem dt_bits (m c : Int64) (hm0 : Int64.ofInt (-(2 ^ 48)) ≤ m) (hm1 : m < Int64.ofInt (2 ^ 48))
    (hc0 : 0 ≤ c) (hc1 : c < 2048) :
    (((m <<< 11) ||| c) &&& 0x7FF) = c ∧ ((m <<< 11) ||| c) >>> 11 = m ∧
      -((1 : Int64) <<< 59) ≤ ((m <<< 11) ||| c) ∧ ((m <<< 11) ||| c) < (1 : Int64) <<< 59 ∧
      ((((m <<< 11) ||| c) <<< 4) ||| 7) >>> 15 = m := by
  have e1 : Int64.ofInt (-(2 ^ 48)) = -((1 : Int64) <<< 48) := by decide
  have e2 : Int64.ofInt (2 ^ 48) = (1 : Int64) <<< 48 := by decide
  rw [e1] at hm0; rw [e2] at hm1
  bv_decide

theorem dt_unbits (p : Int64) : ((p >>> 11) <<< 11) ||| (p &&& 0x7FF) = p := by
  bv_decide

theorem dt_code_nonneg (p : Int64) : 0 ≤ p &&& 0x7FF := by
  bv_decide

theorem ms_bounds (ms : Int) (h : dtInRange ms = true) :
    Int64.ofInt (-(2 ^ 48)) ≤ Int64.ofInt ms ∧ Int64.ofInt ms < Int64.ofInt (2 ^ 48) := by
  simp [dtInRange, dtMinMs, dtLimitMs] at h
  exact ⟨int64_ofInt_ge (by norm_num) (by norm_num) h.1 (by omega),
    int64_ofInt_lt (by norm_num) (by norm_num) (by omega) h.2⟩

theorem code_bounds (tz : Option Int) (h : tzValid tz = true) :
    0 ≤ Int64.ofNat (tzCode tz) ∧ Int64.ofNat (tzCode tz) < 2048 ∧
      (Int64.ofNat (tzCode tz)).toNatClampNeg = tzCode tz := by
  have hle := tzCode_le tz h
  have h0 : (Int64.ofNat (tzCode tz)).toInt = tzCode tz := Int64.toInt_ofNat_of_lt (by omega)
  refine ⟨?_, ?_, Int64.toNatClampNeg_ofNat_of_lt (by omega)⟩
  · rw [Int64.le_iff_toInt_le, h0]; simp
  · rw [Int64.lt_iff_toInt_lt, h0]
    have : (2048 : Int64).toInt = 2048 := by decide
    rw [this]; omega

/-- Unpacking a packed (instant, timezone) gives it back. -/
theorem unpackDT_packDT (ms : Int) (tz : Option Int) (hms : dtInRange ms = true)
    (htz : tzValid tz = true) : unpackDT (packDT ms (tzCode tz)) = .ok (ms, tz) := by
  obtain ⟨hm0, hm1⟩ := ms_bounds ms hms
  obtain ⟨hc0, hc1, hcn⟩ := code_bounds tz htz
  obtain ⟨b1, b2, -, -, -⟩ := dt_bits _ _ hm0 hm1 hc0 hc1
  simp [dtInRange, dtMinMs, dtLimitMs] at hms
  simp only [unpackDT, packDT, b1, b2, hcn, tzOfCode_tzCode tz htz, bind, Except.bind, pure,
    Except.pure]
  rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]

/-- Packing the unpacking of an accepted payload gives the payload back. -/
theorem packDT_unpackDT (p : Int64) (ms : Int) (tz : Option Int)
    (h : unpackDT p = .ok (ms, tz)) : packDT ms (tzCode tz) = p := by
  simp only [unpackDT, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i tz' htz
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc := (tzCode_tzOfCode _ _ htz).2
    simp only [packDT, Int64.ofInt_toInt, hc]
    rw [Int64.ofNat_toNatClampNeg _ (dt_code_nonneg p), dt_unbits]

/-- The instant of a `DATETIME` id is `id >> 15`. -/
theorem instant_encDT (ms : Int) (tz : Option Int) (hms : dtInRange ms = true)
    (htz : tzValid tz = true) : (encDT ms tz).instant = Int64.ofInt ms ∧ (encDT ms tz).instant.toInt = ms := by
  obtain ⟨hm0, hm1⟩ := ms_bounds ms hms
  obtain ⟨hc0, hc1, -⟩ := code_bounds tz htz
  obtain ⟨-, -, -, -, b5⟩ := dt_bits _ _ hm0 hm1 hc0 hc1
  simp [dtInRange, dtMinMs, dtLimitMs] at hms
  have : (encDT ms tz).instant = Int64.ofInt ms := b5
  exact ⟨this, by rw [this, Int64.toInt_ofInt_of_le (by omega) (by omega)]⟩

/-- `encDT` is `ofSigned` of the packed payload, and the payload is a signed 60-bit value. -/
theorem encDT_payload (ms : Int) (tz : Option Int) (hms : dtInRange ms = true)
    (htz : tzValid tz = true) :
    -((1 : Int64) <<< 59) ≤ packDT ms (tzCode tz) ∧ packDT ms (tzCode tz) < (1 : Int64) <<< 59 := by
  obtain ⟨hm0, hm1⟩ := ms_bounds ms hms
  obtain ⟨hc0, hc1, -⟩ := code_bounds tz htz
  obtain ⟨-, -, b3, b4, -⟩ := dt_bits _ _ hm0 hm1 hc0 hc1
  exact ⟨b3, b4⟩

end Tiramemsu.Codec
