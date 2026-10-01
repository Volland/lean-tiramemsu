/-
Proofs of `SHORT_STR` packing: unpacking a packed string of at most 7 bytes gives it back, and
packing the string of an accepted payload gives the payload back.
-/
import Tiramemsu.Codec.ShortStr
import Std.Tactic.BVDecide
import Mathlib.Tactic.IntervalCases

namespace Tiramemsu.Codec

--# @lat: [[codec#Inline Values#Short Strings]]

theorem shortBytes_eq (p : UInt64) :
    shortBytes p = [((p >>> 52) &&& 0xFF).toUInt8, ((p >>> 44) &&& 0xFF).toUInt8,
      ((p >>> 36) &&& 0xFF).toUInt8, ((p >>> 28) &&& 0xFF).toUInt8, ((p >>> 20) &&& 0xFF).toUInt8,
      ((p >>> 12) &&& 0xFF).toUInt8, ((p >>> 4) &&& 0xFF).toUInt8] := rfl

/-- The bytes and length of a packed word read back. -/
theorem packWord_bits (b0 b1 b2 b3 b4 b5 b6 : UInt8) (len : UInt64) (hl : len < 16) :
    let p := packWord b0.toUInt64 b1.toUInt64 b2.toUInt64 b3.toUInt64 b4.toUInt64 b5.toUInt64
      b6.toUInt64 len
    (((p >>> 52) &&& 0xFF).toUInt8 = b0 ∧ ((p >>> 44) &&& 0xFF).toUInt8 = b1 ∧
      ((p >>> 36) &&& 0xFF).toUInt8 = b2 ∧ ((p >>> 28) &&& 0xFF).toUInt8 = b3 ∧
      ((p >>> 20) &&& 0xFF).toUInt8 = b4 ∧ ((p >>> 12) &&& 0xFF).toUInt8 = b5 ∧
      ((p >>> 4) &&& 0xFF).toUInt8 = b6) ∧ p &&& 15 = len ∧ p < (1 : UInt64) <<< 60 := by
  simp only [packWord]
  bv_decide

/-- A payload below `2^60` is the word of its own bytes and length. -/
theorem packWord_of_bytes (p : UInt64) (hp : p < (1 : UInt64) <<< 60) :
    packWord (((p >>> 52) &&& 0xFF).toUInt8.toUInt64) (((p >>> 44) &&& 0xFF).toUInt8.toUInt64)
      (((p >>> 36) &&& 0xFF).toUInt8.toUInt64) (((p >>> 28) &&& 0xFF).toUInt8.toUInt64)
      (((p >>> 20) &&& 0xFF).toUInt8.toUInt64) (((p >>> 12) &&& 0xFF).toUInt8.toUInt64)
      (((p >>> 4) &&& 0xFF).toUInt8.toUInt64) (p &&& 15) = p := by
  simp only [packWord]
  bv_decide

/-- The seven bytes of a short list, padded with zeros. -/
def pad7 (l : List UInt8) : List UInt8 :=
  [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0]

theorem pad7_eq (l : List UInt8) (h : l.length ≤ 7) :
    pad7 l = l ++ List.replicate (7 - l.length) 0 := by
  apply List.ext_getElem
  · simp [pad7]; omega
  · intro i h1 h2
    have hi : i < 7 := by simpa [pad7] using h1
    rw [List.getElem_append]
    interval_cases i <;> (simp only [pad7]; split <;> simp_all [List.getD_eq_getElem?_getD])

theorem byteAt_eq (l : List UInt8) (i : Nat) : byteAt l i = (l.getD i 0).toUInt64 := rfl

theorem toNat_and_15 (p : UInt64) : (p &&& 15).toNat < 16 := by
  have : p &&& 15 < 16 := by bv_decide
  exact this

theorem len_toUInt64 (n : Nat) (h : n < 16) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq]
  exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp only [String.fromUTF8?, s.isValidUTF8, ↓reduceDIte]
  rfl

theorem toByteArray_of_fromUTF8? {b : ByteArray} {s : String} (h : String.fromUTF8? b = some s) :
    s.toByteArray = b := by
  simp only [String.fromUTF8?] at h
  split at h
  · cases h; rfl
  · cases h

theorem byteArray_mk_toList (b : ByteArray) : ByteArray.mk b.data.toList.toArray = b := by
  cases b; simp

/-- Unpacking a packed string of at most 7 bytes gives the string back. -/
theorem unpackShort_packShort (s : String) (h : s.utf8ByteSize ≤ 7) :
    unpackShort (packShort s) = .ok s := by
  have hlen : s.toUTF8.data.toList.length = s.utf8ByteSize := by
    simp [String.size_toByteArray]
  generalize hl : s.toUTF8.data.toList = l at hlen
  have hbits := packWord_bits (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) (l.getD 4 0)
    (l.getD 5 0) (l.getD 6 0) s.utf8ByteSize.toUInt64
    (by rw [UInt64.lt_iff_toNat_lt, len_toUInt64 _ (by omega)]; show s.utf8ByteSize < 16; omega)
  simp only [packShort, hl, byteAt_eq] at hbits ⊢
  generalize hp : packWord _ _ _ _ _ _ _ _ = p at hbits
  obtain ⟨hb, hlow, _⟩ := hbits
  have hbytes : shortBytes p = pad7 l := by
    rw [shortBytes_eq]; simp only [pad7, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
      hb.2.2.2.2.2.1, hb.2.2.2.2.2.2]
  have hn : (p &&& 15).toNat = s.utf8ByteSize := by
    rw [hlow, len_toUInt64 _ (by omega)]
  unfold unpackShort
  have hl7 : l.length ≤ 7 := by rw [hlen]; omega
  rw [pad7_eq l hl7] at hbytes
  simp only [hn, shortMaxLen, hbytes, ← hlen]
  simp only [show ¬ l.length > 7 by omega, ite_false, List.drop_left', List.take_left',
    List.all_replicate]
  have : ByteArray.mk l.toArray = s.toByteArray := by
    rw [← hl, String.toUTF8_eq_toByteArray, byteArray_mk_toList]
  simp [this, fromUTF8?_toByteArray]

/-- Packing the string of an accepted payload (below `2^60`) gives the payload back. -/
theorem packShort_unpackShort (p : UInt64) (s : String) (hp : p < (1 : UInt64) <<< 60)
    (h : unpackShort p = .ok s) : packShort s = p := by
  unfold unpackShort at h
  have h16 := toNat_and_15 p
  generalize hn : (p &&& 15).toNat = n at h h16
  dsimp only at h
  split at h
  · cases h
  rename_i hle
  simp only [shortMaxLen, gt_iff_lt, Nat.not_lt] at hle
  split at h
  · rename_i hzero
    split at h
    · rename_i s' hs
      cases h
      have hsb := toByteArray_of_fromUTF8? hs
      have hl : s.toUTF8.data.toList = (shortBytes p).take n := by
        rw [String.toUTF8_eq_toByteArray, hsb]
      have hsize : s.utf8ByteSize = n := by
        rw [← String.size_toByteArray, hsb]; simp [ByteArray.size, shortBytes]; omega
      have hpad : pad7 ((shortBytes p).take n) = shortBytes p := by
        rw [pad7_eq _ (by simp [shortBytes])]
        have hz : (shortBytes p).drop n = List.replicate (7 - n) 0 := by
          apply List.eq_replicate_iff.mpr
          refine ⟨by simp [shortBytes], fun b hb => ?_⟩
          have := List.all_eq_true.mp hzero b hb
          simpa using this
        have hlen : ((shortBytes p).take n).length = n := by simp [shortBytes]; omega
        rw [hlen, ← hz, List.take_append_drop]
      simp only [packShort, hl, hsize, byteAt_eq]
      have e : ∀ i < 7, (List.take n (shortBytes p)).getD i 0 = (shortBytes p).getD i 0 := by
        intro i hi
        have := congrArg (fun l => l.getD i 0) hpad
        interval_cases i <;> simpa [pad7] using this
      rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
        e 5 (by omega), e 6 (by omega)]
      simp only [shortBytes_eq, List.getD_cons_zero, List.getD_cons_succ]
      have hlen' : n.toUInt64 = p &&& 15 := by
        apply UInt64.toNat_inj.mp; rw [len_toUInt64 _ h16, hn]
      rw [hlen']
      exact packWord_of_bytes p hp
    · cases h
  · cases h

end Tiramemsu.Codec
