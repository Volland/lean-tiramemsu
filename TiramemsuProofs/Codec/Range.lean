/-
Proofs that signed id order is value order within a tag (`INT`, `DATE`, `DATETIME`, origin-0
counters) and that the range-scan bounds select exactly the ids of the tag whose value (or
instant) lies in the range.
-/
import Tiramemsu.Codec.Range
import Tiramemsu.Codec.Origin
import TiramemsuProofs.Codec.ObjectId
import TiramemsuProofs.Codec.DateTime

namespace Tiramemsu.Codec

--# @lat: [[codec#Order And Ranges]]

/-! ## Bit-level facts -/

theorem signed_order_bits (a b tb : Int64) (ht0 : 0 ≤ tb) (ht : tb < 15)
    (ha0 : -((1 : Int64) <<< 59) ≤ a) (ha1 : a < (1 : Int64) <<< 59)
    (hb0 : -((1 : Int64) <<< 59) ≤ b) (hb1 : b < (1 : Int64) <<< 59) :
    a < b ↔ ((a <<< 4) ||| tb) < ((b <<< 4) ||| tb) := by
  bv_decide

theorem dt_order_bits (m1 c1 m2 c2 : Int64)
    (h10 : -((1 : Int64) <<< 48) ≤ m1) (h11 : m1 < (1 : Int64) <<< 48) (c10 : 0 ≤ c1) (c11 : c1 < 2048)
    (h20 : -((1 : Int64) <<< 48) ≤ m2) (h21 : m2 < (1 : Int64) <<< 48) (c20 : 0 ≤ c2) (c21 : c2 < 2048) :
    (m1 < m2 ∨ (m1 = m2 ∧ c1 < c2)) ↔
      ((((m1 <<< (11 : Int64)) ||| c1) <<< (4 : Int64)) ||| (7 : Int64)) <
        ((((m2 <<< (11 : Int64)) ||| c2) <<< (4 : Int64)) ||| (7 : Int64)) := by
  bv_decide

theorem counter_order_bits (c1 c2 tb : UInt64) (ht : tb < 15) (h1 : c1 < (1 : UInt64) <<< 48)
    (h2 : c2 < (1 : UInt64) <<< 48) :
    c1 < c2 ↔ ((c1 <<< 4) ||| tb).toInt64 < ((c2 <<< 4) ||| tb).toInt64 := by
  bv_decide

theorem range_bits (x a b tb : Int64) (ht0 : 0 ≤ tb) (ht : tb < 15)
    (ha0 : -((1 : Int64) <<< 59) ≤ a) (ha1 : a < (1 : Int64) <<< 59)
    (hb0 : -((1 : Int64) <<< 59) ≤ b) (hb1 : b < (1 : Int64) <<< 59)
    (hx : x.toUInt64 &&& 15 = tb.toUInt64) :
    (((a <<< 4) ||| tb) ≤ x ∧ x ≤ ((b <<< 4) ||| tb)) ↔ (a ≤ x >>> 4 ∧ x >>> 4 ≤ b) := by
  bv_decide

theorem instant_bits (x a b : Int64) (ha0 : -((1 : Int64) <<< 48) ≤ a) (ha1 : a < (1 : Int64) <<< 48)
    (hb0 : -((1 : Int64) <<< 48) ≤ b) (hb1 : b < (1 : Int64) <<< 48) (hx : x.toUInt64 &&& 15 = 7) :
    (((a <<< 15) ||| 7) ≤ x ∧ x ≤ ((b <<< 15) ||| 0x7FF7)) ↔ (a ≤ x >>> 15 ∧ x >>> 15 ≤ b) := by
  bv_decide

/-! ## Value-level statements -/

/-- Signed 60-bit values as Int64 bounds. -/
theorem int60_bounds (v : Int) (h0 : intMin ≤ v) (h1 : v ≤ intMax) :
    -((1 : Int64) <<< 59) ≤ Int64.ofInt v ∧ Int64.ofInt v < (1 : Int64) <<< 59 := by
  have e1 : -((1 : Int64) <<< 59) = Int64.ofInt (-(2 ^ 59)) := by decide
  have e2 : (1 : Int64) <<< 59 = Int64.ofInt (2 ^ 59) := by decide
  simp only [intMin, intMax] at h0 h1
  rw [e1, e2]
  exact ⟨int64_ofInt_ge (by norm_num) (by norm_num) h0 (by omega),
    int64_ofInt_lt (by norm_num) (by norm_num) (by omega) (by omega)⟩

theorem int48_bounds (v : Int) (h0 : dtMinMs ≤ v) (h1 : v < dtLimitMs) :
    -((1 : Int64) <<< 48) ≤ Int64.ofInt v ∧ Int64.ofInt v < (1 : Int64) <<< 48 := by
  have e1 : -((1 : Int64) <<< 48) = Int64.ofInt (-(2 ^ 48)) := by decide
  have e2 : (1 : Int64) <<< 48 = Int64.ofInt (2 ^ 48) := by decide
  simp only [dtMinMs, dtLimitMs] at h0 h1
  rw [e1, e2]
  exact ⟨int64_ofInt_ge (by norm_num) (by norm_num) h0 (by omega),
    int64_ofInt_lt (by norm_num) (by norm_num) (by omega) h1⟩

/-- `INT` and `DATE` (any signed tag): signed id order is value order. -/
theorem int_lt_iff (t : Tag) (a b : Int) (ha0 : intMin ≤ a) (ha1 : a ≤ intMax) (hb0 : intMin ≤ b)
    (hb1 : b ≤ intMax) : a < b ↔ (encSigned t a).raw < (encSigned t b).raw := by
  obtain ⟨a0, a1⟩ := int60_bounds a ha0 ha1
  obtain ⟨b0, b1⟩ := int60_bounds b hb0 hb1
  have ht := Tag.toInt64_bounds t
  simp only [intMin, intMax] at ha0 ha1 hb0 hb1
  rw [← int64_ofInt_lt_iff (by omega) (by omega) (by omega) (by omega)]
  exact signed_order_bits _ _ _ ht.1 ht.2 a0 a1 b0 b1

/-- `DATETIME`: signed id order is the lexicographic order of (instant, timezone code). -/
theorem datetime_lt_iff (ms1 ms2 : Int) (tz1 tz2 : Option Int) (h1 : dtInRange ms1 = true)
    (h2 : dtInRange ms2 = true) (t1 : tzValid tz1 = true) (t2 : tzValid tz2 = true) :
    (ms1 < ms2 ∨ (ms1 = ms2 ∧ tzCode tz1 < tzCode tz2)) ↔ (encDT ms1 tz1).raw < (encDT ms2 tz2).raw := by
  have r1 := h1; have r2 := h2
  simp [dtInRange] at r1 r2
  obtain ⟨m10, m11⟩ := int48_bounds ms1 r1.1 r1.2
  obtain ⟨m20, m21⟩ := int48_bounds ms2 r2.1 r2.2
  obtain ⟨c10, c11, -⟩ := code_bounds tz1 t1
  obtain ⟨c20, c21, -⟩ := code_bounds tz2 t2
  have hb := dt_order_bits _ _ _ _ m10 m11 c10 c11 m20 m21 c20 c21
  have hcode : tzCode tz1 < tzCode tz2 ↔ Int64.ofNat (tzCode tz1) < Int64.ofNat (tzCode tz2) := by
    rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofNat_of_lt (by have := tzCode_le tz1 t1; omega),
      Int64.toInt_ofNat_of_lt (by have := tzCode_le tz2 t2; omega)]
    omega
  simp only [dtMinMs, dtLimitMs] at r1 r2
  rw [← int64_ofInt_lt_iff (by omega) (by omega) (by omega) (by omega),
    ← int64_ofInt_eq_iff (by omega) (by omega) (by omega) (by omega), hcode]
  exact hb

/-- Origin-0 counters: signed id order is counter order. -/
theorem counter_lt_iff (k : AllocTag) (c1 c2 : Nat) (h1 : c1 < 2 ^ 48) (h2 : c2 < 2 ^ 48) :
    c1 < c2 ↔ (mkAlloc k 0 c1.toUInt64).raw < (mkAlloc k 0 c2.toUInt64).raw := by
  have h48 : ((1 : UInt64) <<< 48).toNat = 2 ^ 48 := by decide
  have n1 : c1.toUInt64.toNat = c1 := by
    simp only [Nat.toUInt64_eq]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have n2 : c2.toUInt64.toNat = c2 := by
    simp only [Nat.toUInt64_eq]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have b1 : c1.toUInt64 < (1 : UInt64) <<< 48 := by rw [UInt64.lt_iff_toNat_lt, h48, n1]; exact h1
  have b2 : c2.toUInt64 < (1 : UInt64) <<< 48 := by rw [UInt64.lt_iff_toNat_lt, h48, n2]; exact h2
  rw [mkAlloc_zero, mkAlloc_zero]
  have : c1 < c2 ↔ c1.toUInt64 < c2.toUInt64 := by rw [UInt64.lt_iff_toNat_lt, n1, n2]
  rw [this]
  exact counter_order_bits _ _ _ (Tag.toUInt64_lt _) b1 b2

/-- `INT` / `DATE` range bounds: for every id of the tag, lying within the bounds is
equivalent to its value lying within the range. -/
theorem range_iff (t : Tag) (a b : Int) (ha0 : intMin ≤ a) (ha1 : a ≤ intMax) (hb0 : intMin ≤ b)
    (hb1 : b ≤ intMax) (x : ObjectId) (hx : x.tagBits = t.toUInt64) :
    (rangeLower t a ≤ x.raw ∧ x.raw ≤ rangeUpper t b) ↔
      (a ≤ x.spayload.toInt ∧ x.spayload.toInt ≤ b) := by
  obtain ⟨a0, a1⟩ := int60_bounds a ha0 ha1
  obtain ⟨b0, b1⟩ := int60_bounds b hb0 hb1
  have ht := Tag.toInt64_bounds t
  have hx' : x.raw.toUInt64 &&& 15 = t.toInt64.toUInt64 := by
    rw [Tag.toInt64_toUInt64]; exact hx
  simp only [intMin, intMax] at ha0 ha1 hb0 hb1
  have e1 : a ≤ x.spayload.toInt ↔ Int64.ofInt a ≤ x.spayload := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have e2 : x.spayload.toInt ≤ b ↔ x.spayload ≤ Int64.ofInt b := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by omega) (by omega)]
  rw [e1, e2]
  exact range_bits x.raw _ _ _ ht.1 ht.2 a0 a1 b0 b1 hx'

/-- `DATETIME` instant bounds: for every `DATETIME` id, lying within the bounds is equivalent
to its instant lying within the range, whatever its timezone code. -/
theorem instant_range_iff (a b : Int) (ha0 : dtMinMs ≤ a) (ha1 : a < dtLimitMs) (hb0 : dtMinMs ≤ b)
    (hb1 : b < dtLimitMs) (x : ObjectId) (hx : x.tagBits = Tag.dateTime.toUInt64) :
    (instantLower a ≤ x.raw ∧ x.raw ≤ instantUpper b) ↔
      (a ≤ x.instant.toInt ∧ x.instant.toInt ≤ b) := by
  obtain ⟨a0, a1⟩ := int48_bounds a ha0 ha1
  obtain ⟨b0, b1⟩ := int48_bounds b hb0 hb1
  simp only [dtMinMs, dtLimitMs] at ha0 ha1 hb0 hb1
  have e1 : a ≤ x.instant.toInt ↔ Int64.ofInt a ≤ x.instant := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have e2 : x.instant.toInt ≤ b ↔ x.instant ≤ Int64.ofInt b := by
    rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by omega) (by omega)]
  rw [e1, e2]
  exact instant_bits x.raw _ _ a0 a1 b0 b1 hx

end Tiramemsu.Codec
