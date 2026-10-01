/-
Proofs about the ObjectId layout, the reserved tag 15, origins and allocation.
Bit-level facts are proven by `bv_decide` (allowlisted in `policy/bv-decide-allowlist.txt`).
-/
import Tiramemsu.Codec.Origin
import Std.Tactic.BVDecide
import Mathlib.Tactic.IntervalCases

namespace Tiramemsu.Codec

--# @lat: [[codec#ObjectId Layout]]

theorem Tag.toUInt64_lt (t : Tag) : t.toUInt64 < 15 := by
  cases t <;> decide

theorem Tag.ofBits_toUInt64 (t : Tag) : Tag.ofBits t.toUInt64 = .ok t := by
  cases t <;> rfl

theorem Tag.toUInt64_inj {t u : Tag} (h : t.toUInt64 = u.toUInt64) : t = u := by
  have := Tag.ofBits_toUInt64 t
  rw [h, Tag.ofBits_toUInt64] at this
  exact (Except.ok.inj this).symm

theorem Tag.toInt64_eq (t : Tag) : t.toInt64 = t.toUInt64.toInt64 := by
  cases t <;> rfl

/-- Bit layout of `ofPayload`: the low 4 bits are the tag bits and the logical shift gives the
payload back, for every tag value below 15 and every 60-bit payload. -/
theorem ofPayload_bits (tb p : UInt64) (ht : tb < 15) (hp : p < (1 : UInt64) <<< 60) :
    ((((p <<< 4) ||| tb).toInt64.toUInt64 &&& 15) = tb) ∧
      ((((p <<< 4) ||| tb).toInt64.toUInt64 >>> 4) = p) := by
  bv_decide

/-- Layout: reading the tag and payload of an id built from any tag and 60-bit payload gives
back that tag and payload. -/
theorem layout (t : Tag) (p : UInt64) (hp : p < ObjectId.payloadLimit) :
    (ObjectId.ofPayload t p).tagBits = t.toUInt64 ∧ (ObjectId.ofPayload t p).tag = .ok t ∧
      (ObjectId.ofPayload t p).upayload = p := by
  have h := ofPayload_bits t.toUInt64 p (Tag.toUInt64_lt t) hp
  refine ⟨h.1, ?_, h.2⟩
  simp only [ObjectId.tag, ObjectId.tagBits, ObjectId.ofPayload] at h ⊢
  rw [h.1, Tag.ofBits_toUInt64]

/-- The tag bits determine the tag: two ids with the same tag bits have the same tag result. -/
theorem tag_of_tagBits {x : ObjectId} {t : Tag} (h : x.tagBits = t.toUInt64) : x.tag = .ok t := by
  simp only [ObjectId.tag, h, Tag.ofBits_toUInt64]

theorem Tag.ofNat?_spec {n : Nat} {t : Tag} (h : Tag.ofNat? n = some t) : t.toNat = n := by
  unfold Tag.ofNat? at h
  split at h <;> cases h <;> rfl

theorem Tag.toNat_lt (t : Tag) : t.toNat < 15 := by
  cases t <;> decide

theorem tagBits_of_tag {x : ObjectId} {t : Tag} (h : x.tag = .ok t) : x.tagBits = t.toUInt64 := by
  simp only [ObjectId.tag, Tag.ofBits] at h
  split at h
  · rename_i t' ht'
    cases h
    have h1 := Tag.ofNat?_spec ht'
    apply UInt64.toNat_inj.mp
    rw [← h1]
    simp only [Tag.toUInt64, Nat.toUInt64_eq]
    rw [UInt64.toNat_ofNat_of_lt' (by have := Tag.toNat_lt t; simp [UInt64.size]; omega)]
  · split at h <;> cases h

/-- Signed layout: the arithmetic shift gives back a signed 60-bit payload. -/
theorem ofSigned_bits (tb v : Int64) (ht0 : 0 ≤ tb) (ht : tb < 15)
    (hv0 : -((1 : Int64) <<< 59) ≤ v) (hv1 : v < (1 : Int64) <<< 59) :
    ((((v <<< 4) ||| tb).toUInt64 &&& 15) = tb.toUInt64) ∧ (((v <<< 4) ||| tb) >>> 4 = v) := by
  bv_decide

theorem Tag.toInt64_bounds (t : Tag) : 0 ≤ t.toInt64 ∧ t.toInt64 < 15 := by
  cases t <;> decide

theorem Tag.toInt64_toUInt64 (t : Tag) : t.toInt64.toUInt64 = t.toUInt64 := by
  cases t <;> rfl

/-- Signed layout: the tag and the signed payload read back. -/
theorem layout_signed (t : Tag) (v : Int64) (hv0 : -((1 : Int64) <<< 59) ≤ v)
    (hv1 : v < (1 : Int64) <<< 59) :
    (ObjectId.ofSigned t v).tagBits = t.toUInt64 ∧ (ObjectId.ofSigned t v).tag = .ok t ∧
      (ObjectId.ofSigned t v).spayload = v := by
  have hb := Tag.toInt64_bounds t
  have h := ofSigned_bits t.toInt64 v hb.1 hb.2 hv0 hv1
  rw [Tag.toInt64_toUInt64] at h
  exact ⟨h.1, tag_of_tagBits h.1, h.2⟩

/-! ## The reserved tag 15 -/

--# @lat: [[codec#ObjectId Layout#Reserved Tag]]

/-- Every raw id whose low 4 bits are 15 fails tag extraction with `Unsupported "SEALED (M6)"`. -/
theorem sealed_rejected (x : ObjectId) (h : x.tagBits = 15) :
    x.tag = .error (.unsupported sealedFeature) := by
  simp only [ObjectId.tag, h]
  rfl

/-- No id built by `ofPayload` or `ofSigned` has tag bits 15. -/
theorem ofPayload_not_sealed (t : Tag) (p : UInt64) (hp : p < ObjectId.payloadLimit) :
    (ObjectId.ofPayload t p).tagBits ≠ 15 := by
  rw [(layout t p hp).1]
  have := Tag.toUInt64_lt t
  intro h; rw [h] at this; exact absurd this (by decide)

theorem ofSigned_not_sealed (t : Tag) (v : Int64) (hv0 : -((1 : Int64) <<< 59) ≤ v)
    (hv1 : v < (1 : Int64) <<< 59) : (ObjectId.ofSigned t v).tagBits ≠ 15 := by
  rw [(layout_signed t v hv0 hv1).1]
  have := Tag.toUInt64_lt t
  intro h; rw [h] at this; exact absurd this (by decide)

/-! ## Origins and allocation -/

--# @lat: [[codec#Origins And Allocation]]

theorem AllocTag.tag_isAllocated (k : AllocTag) : k.tag.isAllocated = true := by
  cases k <;> rfl

theorem AllocTag.ofTag?_tag (k : AllocTag) : AllocTag.ofTag? k.tag = some k := by
  cases k <;> rfl

theorem mkAlloc_bits (tb o c : UInt64) (ht : tb < 15) (ho : o < (1 : UInt64) <<< 12)
    (hc : c < (1 : UInt64) <<< 48) :
    ((((((o <<< 48) ||| c) <<< 4) ||| tb).toInt64.toUInt64 >>> 4) >>> 48 = o) ∧
      ((((((o <<< 48) ||| c) <<< 4) ||| tb).toInt64.toUInt64 >>> 4) &&& 0xFFFFFFFFFFFF = c) ∧
      ((o <<< 48) ||| c) < (1 : UInt64) <<< 60 := by
  bv_decide

/-- Splitting the id built from an origin and a counter gives back both, and its tag. -/
theorem origin_split (k : AllocTag) (o c : UInt64) (ho : o < (1 : UInt64) <<< 12)
    (hc : c < (1 : UInt64) <<< 48) :
    (mkAlloc k o c).origin = o ∧ (mkAlloc k o c).counter = c ∧ (mkAlloc k o c).tag = .ok k.tag := by
  have h := mkAlloc_bits k.tag.toUInt64 o c (Tag.toUInt64_lt _) ho hc
  refine ⟨h.1, h.2.1, (layout k.tag _ h.2.2).2.1⟩

/-- Origin-0 ids are the plain layout of the counter. -/
theorem mkAlloc_zero (k : AllocTag) (c : UInt64) : mkAlloc k 0 c = ObjectId.ofPayload k.tag c := by
  have : ((0 : UInt64) <<< 48) ||| c = c := by bv_decide
  simp only [mkAlloc, this]

/-- An allocated-tag id with a non-zero origin is rejected with `Unsupported "origin <n>"`. -/
theorem checkOrigin_rejects (x : ObjectId) (t : Tag) (ht : x.tag = .ok t)
    (ha : t.isAllocated = true) (ho : x.origin ≠ 0) :
    checkOrigin x = .error (.unsupported (originFeature x.origin.toNat)) := by
  simp [checkOrigin, ht, ha, ho]

/-- Origin-0 and non-allocated ids pass the origin check. -/
theorem checkOrigin_ok (x : ObjectId) (h : ∀ t, x.tag = .ok t → t.isAllocated = true → x.origin = 0) :
    checkOrigin x = .ok () := by
  unfold checkOrigin
  split
  · rename_i t ht
    by_cases ha : t.isAllocated = true
    · simp [ha, h t ht ha]
    · simp [ha]
  · rfl

/-- Allocation succeeds exactly when the counter is at most `2^48 − 1`. -/
theorem alloc_ok_iff (k : AllocTag) (n : Nat) : (∃ r, alloc k n = .ok r) ↔ n ≤ 2 ^ 48 - 1 := by
  unfold alloc counterMax
  constructor
  · rintro ⟨r, h⟩
    split at h
    · assumption
    · cases h
  · intro h
    exact ⟨_, by simp only [show n ≤ 281474976710655 by omega, ite_true]; rfl⟩

/-- A failed allocation names the kind and produces no id. -/
theorem alloc_error (k : AllocTag) (n : Nat) (h : 2 ^ 48 - 1 < n) :
    alloc k n = .error (.idSpaceExhausted k.kind) := by
  unfold alloc counterMax
  simp only [show ¬ n ≤ 2 ^ 48 - 1 by omega, ite_false]

/-- A successful allocation has origin 0, the counter `n`, the allocated tag, and advances the
counter by one. -/
theorem alloc_spec (k : AllocTag) (n : Nat) (x : ObjectId) (n' : Nat) (h : alloc k n = .ok (x, n')) :
    x.origin = 0 ∧ x.counter.toNat = n ∧ x.tag = .ok k.tag ∧ n' = n + 1 ∧
      x = ObjectId.ofPayload k.tag n.toUInt64 := by
  unfold alloc counterMax at h
  split at h
  · rename_i hn
    cases h
    have h48 : ((1 : UInt64) <<< 48).toNat = 2 ^ 48 := by decide
    have hn : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64_eq]
      exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hc : n.toUInt64 < (1 : UInt64) <<< 48 := by
      rw [UInt64.lt_iff_toNat_lt, h48, hn]; omega
    have hs := origin_split k 0 n.toUInt64 (by decide) hc
    refine ⟨hs.1, ?_, hs.2.2, rfl, mkAlloc_zero k _⟩
    rw [hs.2.1, hn]
  · cases h

end Tiramemsu.Codec
