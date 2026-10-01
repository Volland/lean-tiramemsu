/-
Proofs of encoding and decoding: decode after encode is the identity on canonical inline
values, encode after decode is the identity on accepted ids (so decoding is injective), two
values encode alike exactly when their canonical forms are equal, and inline kinds never
reach the dictionary.
-/
import Tiramemsu.Codec.Encode
import TiramemsuProofs.Codec.ObjectId
import TiramemsuProofs.Codec.ShortStr
import TiramemsuProofs.Codec.DateTime
import TiramemsuProofs.Codec.Range
import TiramemsuProofs.Codec.Decimal
import TiramemsuProofs.Codec.Double.RoundTrip

namespace Tiramemsu.Codec

--# @lat: [[codec#Encoding]]

/-! ## Bit-level facts -/

theorem ofPayload_eta_bits (r : Int64) (tb : UInt64) (ht : tb < 15) (h : r.toUInt64 &&& 15 = tb) :
    (((r.toUInt64 >>> 4) <<< 4) ||| tb).toInt64 = r := by
  bv_decide

theorem ofSigned_eta_bits (r tb : Int64) (h0 : 0 ≤ tb) (ht : tb < 15) (h : r.toUInt64 &&& 15 = tb.toUInt64) :
    ((r >>> 4) <<< 4) ||| tb = r := by
  bv_decide

theorem spayload_bits (r : Int64) : -((1 : Int64) <<< 59) ≤ r >>> 4 ∧ r >>> 4 < (1 : Int64) <<< 59 := by
  bv_decide

theorem upayload_bits (r : Int64) : r.toUInt64 >>> 4 < (1 : UInt64) <<< 60 := by
  bv_decide

theorem dt_ms_bits (p : Int64) (h0 : -((1 : Int64) <<< 59) ≤ p) (h1 : p < (1 : Int64) <<< 59) :
    -((1 : Int64) <<< 48) ≤ p >>> 11 ∧ p >>> 11 < (1 : Int64) <<< 48 := by
  bv_decide

theorem alloc_eta_bits (r : Int64) (tb : UInt64) (ht : tb < 15) (h : r.toUInt64 &&& 15 = tb)
    (ho : (r.toUInt64 >>> 4) >>> 48 = 0) :
    (((((0 : UInt64) <<< 48) ||| ((r.toUInt64 >>> 4) &&& 0xFFFFFFFFFFFF)) <<< 4) ||| tb).toInt64 = r := by
  bv_decide

theorem counter_bits (r : Int64) :
    ((r.toUInt64 >>> (4 : UInt64)) &&& (0xFFFFFFFFFFFF : UInt64)) < ((1 : UInt64) <<< (48 : UInt64)) := by
  bv_decide

theorem ofPayload_eta (x : ObjectId) (t : Tag) (h : x.tagBits = t.toUInt64) :
    ObjectId.ofPayload t x.upayload = x := by
  obtain ⟨r⟩ := x
  simp only [ObjectId.ofPayload, ObjectId.upayload, ObjectId.mk.injEq]
  exact ofPayload_eta_bits r _ (Tag.toUInt64_lt t) h

theorem ofSigned_eta (x : ObjectId) (t : Tag) (h : x.tagBits = t.toUInt64) :
    ObjectId.ofSigned t x.spayload = x := by
  obtain ⟨r⟩ := x
  simp only [ObjectId.ofSigned, ObjectId.spayload, ObjectId.mk.injEq]
  have hb := Tag.toInt64_bounds t
  exact ofSigned_eta_bits r _ hb.1 hb.2 (by rw [Tag.toInt64_toUInt64]; exact h)

theorem spayload_range (x : ObjectId) : inIntRange x.spayload.toInt = true := by
  obtain ⟨a, b⟩ := spayload_bits x.raw
  have e1 : -((1 : Int64) <<< 59) = Int64.ofInt (-(2 ^ 59)) := by decide
  have e2 : (1 : Int64) <<< 59 = Int64.ofInt (2 ^ 59) := by decide
  rw [e1, Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by norm_num) (by norm_num)] at a
  rw [e2, Int64.lt_iff_toInt_lt, Int64.toInt_ofInt_of_le (by norm_num) (by norm_num)] at b
  unfold inIntRange
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [intMin, intMax, ObjectId.spayload]
  constructor <;> omega

theorem upayload_lt (x : ObjectId) : x.upayload < (1 : UInt64) <<< 60 := upayload_bits x.raw

/-! ## Canonical values -/

/-- The invariant canonical values satisfy and encoding relies on. -/
def Value.WF : Value → Prop
  | .int i => inIntRange i = true
  | .date d => inIntRange d = true
  | .dateTime ms tz => dtInRange ms = true ∧ tzValid tz = true
  | .double x => x.canon = x
  | _ => True

theorem Double64.canon_canon (x : Double64) : x.canon.canon = x.canon := by
  unfold Double64.canon
  split
  · have : Double64.canonNaN.isNaN = true := by decide
    simp [this]
  · simp_all

theorem bigInteger_wf (lex : String) : (bigInteger lex).WF := by
  unfold bigInteger
  split
  · split
    · rename_i h; exact h
    · trivial
  · trivial

theorem literal_wf (lex : String) (dt lang : Option String) : (literal lex dt lang).WF := by
  unfold literal
  cases lang with
  | some l => trivial
  | none =>
    cases dt with
    | none => trivial
    | some d =>
      simp only
      split
      · trivial
      split
      · exact bigInteger_wf lex
      split
      · split
        · trivial
        · split <;> trivial
      split
      · split
        · rename_i ms tz _
          split
          · rename_i h
            simp only [Bool.and_eq_true] at h
            exact h
          · trivial
        · trivial
      split
      · split
        · split
          · rename_i h; exact h
          · trivial
        · trivial
      split
      · split
        · exact parseDouble_canon _ _ (by assumption)
        · trivial
      split
      · split <;> trivial
      trivial

theorem canonical_wf (v : Value) : v.canonical.WF := by
  cases v with
  | iri s =>
    show (match skolemValue? s with
      | some (k, n) => Value.ofAlloc k n
      | none => Value.iri s).WF
    split
    · rename_i k n _; cases k <;> trivial
    · trivial
  | int i =>
    show (if inIntRange i then Value.int i else .typed (intText i) xsdInteger).WF
    split
    · rename_i h; exact h
    · trivial
  | dateTime ms tz =>
    show (if dtInRange ms && tzValid tz then Value.dateTime ms tz
      else .typed (formatDateTime ms tz) xsdDateTime).WF
    split
    · rename_i h; simp only [Bool.and_eq_true] at h; exact h
    · trivial
  | date d =>
    show (if inIntRange d then Value.date d else .typed (formatDate d) xsdDate).WF
    split
    · rename_i h; exact h
    · trivial
  | typed lex dt => exact literal_wf lex (some dt) none
  | decimal s =>
    show (match canonDecimal s with
      | some c => Value.decimal c
      | none => .typed s xsdDecimal).WF
    split <;> trivial
  | double x => exact Double64.canon_canon x
  | node _ | bnode _ | stmt _ | tx _ | bool _ | str _ | langStr _ _ => trivial

/-! ## Inline round trips -/

theorem encodeAlloc_ok (k : AllocTag) (n : Nat) (x : ObjectId) (h : encodeAlloc k n = .ok x) :
    n < 2 ^ 48 ∧ x = mkAlloc k 0 n.toUInt64 := by
  unfold encodeAlloc at h
  split_ifs at h with h1 h2
  · cases h; exact ⟨h1, rfl⟩

theorem decode_alloc (k : AllocTag) (n : Nat) (h : n < 2 ^ 48) :
    decodeInline (mkAlloc k 0 n.toUInt64) = .ok (some (.ofAlloc k n)) := by
  have h48 : ((1 : UInt64) <<< 48).toNat = 2 ^ 48 := by decide
  have hn : n.toUInt64.toNat = n := uint64_toNat_toUInt64 n (by omega)
  have hc : n.toUInt64 < (1 : UInt64) <<< 48 := by rw [UInt64.lt_iff_toNat_lt, h48, hn]; exact h
  obtain ⟨ho, hcn, ht⟩ := origin_split k 0 n.toUInt64 (by decide) hc
  have hok : checkOrigin (mkAlloc k 0 n.toUInt64) = .ok () :=
    checkOrigin_ok _ (fun _ _ _ => ho)
  unfold decodeInline
  rw [ht]
  simp only
  cases k <;> simp [hok, AllocTag.ofTag?, AllocTag.tag, Value.ofAlloc, hcn, hn]

/-- Decoding the encoding of a canonical inline value gives the value back. -/
theorem decode_encode (v : Value) (hv : v.WF) (x : ObjectId) (h : encodeCanonical v = .ok (.inline x)) :
    decodeInline x = .ok (some v) := by
  cases v with
  | iri s => simp [encodeCanonical] at h
  | node n =>
    simp only [encodeCanonical] at h
    rcases he : encodeAlloc .node n with e | y <;> rw [he] at h <;> simp at h
    subst h
    obtain ⟨hn, rfl⟩ := encodeAlloc_ok _ _ _ he
    exact decode_alloc .node n hn
  | bnode n =>
    simp only [encodeCanonical] at h
    rcases he : encodeAlloc .bnode n with e | y <;> rw [he] at h <;> simp at h
    subst h
    obtain ⟨hn, rfl⟩ := encodeAlloc_ok _ _ _ he
    exact decode_alloc .bnode n hn
  | stmt n =>
    simp only [encodeCanonical] at h
    rcases he : encodeAlloc .stmt n with e | y <;> rw [he] at h <;> simp at h
    subst h
    obtain ⟨hn, rfl⟩ := encodeAlloc_ok _ _ _ he
    exact decode_alloc .stmt n hn
  | tx n =>
    simp only [encodeCanonical] at h
    rcases he : encodeAlloc .tx n with e | y <;> rw [he] at h <;> simp at h
    subst h
    obtain ⟨hn, rfl⟩ := encodeAlloc_ok _ _ _ he
    exact decode_alloc .tx n hn
  | int i =>
    simp only [encodeCanonical, Except.ok.injEq, Encoded.inline.injEq] at h
    subst h
    simp only [Value.WF, inIntRange, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨a, b⟩ := int60_bounds i hv.1 hv.2
    simp only [intMin, intMax] at hv
    obtain ⟨-, ht, hp⟩ := layout_signed .int (Int64.ofInt i) a b
    unfold decodeInline encSigned
    rw [ht]
    simp only [hp, Except.ok.injEq, Option.some.injEq, Value.int.injEq]
    exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  | bool b =>
    simp only [encodeCanonical, Except.ok.injEq, Encoded.inline.injEq] at h
    subst h
    have hp : (if b then (1 : UInt64) else 0) < ObjectId.payloadLimit := by cases b <;> decide
    obtain ⟨-, ht, hpl⟩ := layout .bool _ hp
    unfold decodeInline
    rw [ht]
    simp only [hpl]
    cases b <;> rfl
  | dateTime ms tz =>
    simp only [encodeCanonical, Except.ok.injEq, Encoded.inline.injEq] at h
    subst h
    obtain ⟨hms, htz⟩ := hv
    obtain ⟨a, b⟩ := encDT_payload ms tz hms htz
    obtain ⟨-, ht, hp⟩ := layout_signed .dateTime _ a b
    unfold decodeInline
    have : encDT ms tz = ObjectId.ofSigned .dateTime (packDT ms (tzCode tz)) := rfl
    rw [this, ht]
    simp only [hp, unpackDT_packDT ms tz hms htz]
  | date d =>
    simp only [encodeCanonical, Except.ok.injEq, Encoded.inline.injEq] at h
    subst h
    simp only [Value.WF, inIntRange, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨a, b⟩ := int60_bounds d hv.1 hv.2
    simp only [intMin, intMax] at hv
    obtain ⟨-, ht, hp⟩ := layout_signed .date (Int64.ofInt d) a b
    unfold decodeInline encSigned
    rw [ht]
    simp only [hp, Except.ok.injEq, Option.some.injEq, Value.date.injEq]
    exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  | str s =>
    simp only [encodeCanonical] at h
    split at h
    · rename_i hs
      simp only [Except.ok.injEq, Encoded.inline.injEq] at h
      subst h
      have hb := packWord_bits (s.toUTF8.data.toList.getD 0 0) (s.toUTF8.data.toList.getD 1 0)
        (s.toUTF8.data.toList.getD 2 0) (s.toUTF8.data.toList.getD 3 0) (s.toUTF8.data.toList.getD 4 0)
        (s.toUTF8.data.toList.getD 5 0) (s.toUTF8.data.toList.getD 6 0) s.utf8ByteSize.toUInt64
        (by rw [UInt64.lt_iff_toNat_lt, len_toUInt64 _ (by unfold shortMaxLen at hs; omega)]
            show s.utf8ByteSize < 16; unfold shortMaxLen at hs; omega)
      have hlt : packShort s < ObjectId.payloadLimit := by
        have := hb.2.2
        show packShort s < (1 : UInt64) <<< 60
        simpa [packShort, byteAt_eq] using this
      obtain ⟨-, ht, hp⟩ := layout .shortStr _ hlt
      unfold decodeInline
      rw [ht]
      simp only [hp, unpackShort_packShort s (by unfold shortMaxLen at hs; omega)]
    · simp at h
  | langStr l g => simp [encodeCanonical] at h
  | typed l d => simp [encodeCanonical] at h
  | double y => simp [encodeCanonical] at h
  | decimal y => simp [encodeCanonical] at h

theorem unpackShort_len (p : UInt64) (s : String) (h : unpackShort p = .ok s) : s.utf8ByteSize ≤ 7 := by
  unfold unpackShort at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hle
    split at h
    · split at h
      · rename_i s' hs
        cases h
        have hb := toByteArray_of_fromUTF8? hs
        rw [← String.size_toByteArray, hb]
        simp [ByteArray.size, shortBytes, shortMaxLen] at hle ⊢
        try omega
      · cases h
    · cases h

/-- Encoding the value of an accepted inline id gives the id back. -/
theorem encode_decode (x : ObjectId) (v : Value) (h : decodeInline x = .ok (some v)) :
    v.canonical = v ∧ encodeCanonical v = .ok (.inline x) ∧ encode v = .ok (.inline x) := by
  suffices hc : v.canonical = v ∧ encodeCanonical v = .ok (.inline x) by
    exact ⟨hc.1, hc.2, by unfold encode; rw [hc.1]; exact hc.2⟩
  unfold decodeInline at h
  split at h
  · cases h
  rename_i t ht
  have htb := tagBits_of_tag ht
  have alloc : ∀ k : AllocTag, t = k.tag →
      (match checkOrigin x, AllocTag.ofTag? k.tag with
        | .error e, _ => .error e
        | .ok (), some k => .ok (some (Value.ofAlloc k x.counter.toNat))
        | .ok (), none => .ok none) = Except.ok (some v) →
      v.canonical = v ∧ encodeCanonical v = .ok (.inline x) := by
    intro k hkt hm
    subst hkt
    rw [AllocTag.ofTag?_tag] at hm
    rcases hco : checkOrigin x with e | u
    · rw [hco] at hm; simp at hm
    rw [hco] at hm
    simp only [Except.ok.injEq, Option.some.injEq] at hm
    subst hm
    have ho : x.origin = 0 := by
      by_contra hne
      have := checkOrigin_rejects x _ ht (AllocTag.tag_isAllocated k) hne
      rw [hco] at this; cases this
    have hct := counter_bits x.raw
    have h48 : ((1 : UInt64) <<< 48).toNat = 2 ^ 48 := by decide
    have hlt : x.counter.toNat < 2 ^ 48 := by
      have := UInt64.lt_iff_toNat_lt.mp hct; rw [h48] at this; exact this
    have henc : encodeAlloc k x.counter.toNat = .ok x := by
      simp only [encodeAlloc, if_pos hlt]
      congr 1
      obtain ⟨r⟩ := x
      simp only [mkAlloc, ObjectId.ofPayload, Nat.toUInt64_eq, UInt64.ofNat_toNat, ObjectId.mk.injEq,
        ObjectId.counter, ObjectId.upayload, counterMask]
      exact alloc_eta_bits r _ (Tag.toUInt64_lt _) htb ho
    cases k <;> exact ⟨rfl, by simp [Value.ofAlloc, encodeCanonical, henc]⟩
  cases t with
  | node => exact alloc .node rfl h
  | bnode => exact alloc .bnode rfl h
  | stmt => exact alloc .stmt rfl h
  | tx => exact alloc .tx rfl h
  | int =>
    simp only [Except.ok.injEq, Option.some.injEq] at h
    subst h
    refine ⟨by simp [Value.canonical, spayload_range], ?_⟩
    simp only [encodeCanonical, encSigned, Int64.ofInt_toInt, Except.ok.injEq, Encoded.inline.injEq]
    exact ofSigned_eta x .int htb
  | bool =>
    simp only at h
    split_ifs at h with h0 h1
    · cases h
      refine ⟨rfl, ?_⟩
      simp only [encodeCanonical, Bool.false_eq_true, ite_false, Except.ok.injEq, Encoded.inline.injEq]
      rw [← h0]; exact ofPayload_eta x .bool htb
    · cases h
      refine ⟨rfl, ?_⟩
      simp only [encodeCanonical, ite_true, Except.ok.injEq, Encoded.inline.injEq]
      rw [← h1]; exact ofPayload_eta x .bool htb
  | dateTime =>
    simp only at h
    split at h
    · rename_i ms tz hu
      cases h
      have hp := packDT_unpackDT _ _ _ hu
      have hcode := hu
      simp only [unpackDT, bind, Except.bind] at hcode
      split at hcode
      · cases hcode
      rename_i tz' htz'
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcode
      obtain ⟨hms, rfl⟩ := hcode
      have hv := (tzCode_tzOfCode _ _ htz').1
      obtain ⟨a, b⟩ := spayload_bits x.raw
      obtain ⟨c, d⟩ := dt_ms_bits _ a b
      have e1 : -((1 : Int64) <<< 48) = Int64.ofInt (-(2 ^ 48)) := by decide
      have e2 : (1 : Int64) <<< 48 = Int64.ofInt (2 ^ 48) := by decide
      rw [e1, Int64.le_iff_toInt_le, Int64.toInt_ofInt_of_le (by norm_num) (by norm_num)] at c
      rw [e2, Int64.lt_iff_toInt_lt, Int64.toInt_ofInt_of_le (by norm_num) (by norm_num)] at d
      have hr : dtInRange ms = true := by
        unfold dtInRange
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        simp only [dtMinMs, dtLimitMs, ← hms, ObjectId.spayload]
        constructor <;> omega
      refine ⟨by simp [Value.canonical, hr, hv], ?_⟩
      simp only [encodeCanonical, encDT, hp, Except.ok.injEq, Encoded.inline.injEq]
      exact ofSigned_eta x .dateTime htb
    · cases h
  | date =>
    simp only [Except.ok.injEq, Option.some.injEq] at h
    subst h
    refine ⟨by simp [Value.canonical, spayload_range], ?_⟩
    simp only [encodeCanonical, encSigned, Int64.ofInt_toInt, Except.ok.injEq, Encoded.inline.injEq]
    exact ofSigned_eta x .date htb
  | shortStr =>
    simp only at h
    split at h
    · rename_i s hs
      cases h
      refine ⟨rfl, ?_⟩
      have hle := unpackShort_len _ _ hs
      have hp := packShort_unpackShort _ _ (upayload_lt x) hs
      simp only [encodeCanonical, shortMaxLen, show s.utf8ByteSize ≤ 7 from hle, ite_true, hp,
        Except.ok.injEq, Encoded.inline.injEq]
      exact ofPayload_eta x .shortStr htb
    · cases h
  | iri | str | langStr | typed | double | decimal => cases h

/-- Decoding is injective: two accepted ids decoding to one value are equal. -/
theorem decode_injective (x y : ObjectId) (v : Value) (hx : decodeInline x = .ok (some v))
    (hy : decodeInline y = .ok (some v)) : x = y := by
  have a := (encode_decode x v hx).2.1
  have b := (encode_decode y v hy).2.1
  rw [a] at b
  simpa using b

/-- A tag-15 id is rejected on decode. -/
theorem decode_sealed (x : ObjectId) (h : x.tagBits = 15) :
    decodeInline x = .error (.unsupported sealedFeature) := by
  unfold decodeInline
  rw [sealed_rejected x h]

/-- An allocated-tag id with a non-zero origin is rejected on decode. -/
theorem decode_origin (x : ObjectId) (k : AllocTag) (ht : x.tag = .ok k.tag) (ho : x.origin ≠ 0) :
    decodeInline x = .error (.unsupported (originFeature x.origin.toNat)) := by
  have hc := checkOrigin_rejects x k.tag ht (AllocTag.tag_isAllocated k) ho
  unfold decodeInline
  rw [ht]
  cases k <;> simp [AllocTag.tag, hc]

/-- A value with a non-zero origin is rejected on input. -/
theorem encode_origin (k : AllocTag) (n : Nat) (h1 : 2 ^ 48 ≤ n) (h2 : n < 2 ^ 60) :
    encode (.ofAlloc k n) = .error (.unsupported (originFeature (n / 2 ^ 48))) := by
  unfold encode
  have hc : (Value.ofAlloc k n).canonical = .ofAlloc k n := by cases k <;> rfl
  rw [hc]
  have he : encodeAlloc k n = .error (.unsupported (originFeature (n / 2 ^ 48))) := by
    unfold encodeAlloc; rw [if_neg (by omega), if_pos h2]
  cases k <;> simp [Value.ofAlloc, encodeCanonical, he]

/-! ## Dictionary terms -/

/-- The term spec of a canonical value decodes to the value. -/
theorem term_value (v : Value) (hv : v.WF) (t : TermSpec) (h : encodeCanonical v = .ok (.term t)) :
    t.value = .ok v := by
  cases v with
  | iri s => simp only [encodeCanonical, Except.ok.injEq, Encoded.term.injEq] at h; subst h; rfl
  | str s =>
    simp only [encodeCanonical] at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq, Encoded.term.injEq] at h; subst h; rfl
  | langStr l g => simp only [encodeCanonical, Except.ok.injEq, Encoded.term.injEq] at h; subst h; rfl
  | typed l d => simp only [encodeCanonical, Except.ok.injEq, Encoded.term.injEq] at h; subst h; rfl
  | double y =>
    simp only [encodeCanonical, Except.ok.injEq, Encoded.term.injEq] at h
    subst h
    simp only [TermSpec.value, valueFromTerm, parseDouble_printDouble, Option.getD_some]
    simp only [Value.WF] at hv
    rw [hv]
  | decimal y => simp only [encodeCanonical, Except.ok.injEq, Encoded.term.injEq] at h; subst h; rfl
  | node n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .node n with _ | _ <;> rw [he] at h <;> simp at h
  | bnode n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .bnode n with _ | _ <;> rw [he] at h <;> simp at h
  | stmt n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .stmt n with _ | _ <;> rw [he] at h <;> simp at h
  | tx n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .tx n with _ | _ <;> rw [he] at h <;> simp at h
  | int _ | bool _ | dateTime _ _ | date _ => simp [encodeCanonical] at h

/-- Every value decodes from its encoding to its canonical form. -/
theorem encode_value (v : Value) (e : Encoded) (h : encode v = .ok e) :
    match e with
    | .inline x => decodeInline x = .ok (some v.canonical)
    | .term t => t.value = .ok v.canonical := by
  unfold encode at h
  cases e with
  | inline x => exact decode_encode _ (canonical_wf v) x h
  | term t => exact term_value _ (canonical_wf v) t h

/-- One ObjectId per value: two values encode alike exactly when their canonical forms are
equal. -/
theorem encode_eq_iff (v w : Value) (e e' : Encoded) (hv : encode v = .ok e) (hw : encode w = .ok e') :
    e = e' ↔ v.canonical = w.canonical := by
  constructor
  · rintro rfl
    have a := encode_value v e hv
    have b := encode_value w e hw
    cases e with
    | inline x =>
      simp only at a b
      rw [a] at b
      simpa using b
    | term t =>
      simp only at a b
      rw [a] at b
      simpa using b
  · intro hc
    unfold encode at hv hw
    rw [hc] at hv
    rw [hv] at hw
    simpa using hw

/-- Encoding produces dictionary terms only for dictionary tags. -/
theorem encode_term_tag (v : Value) (t : TermSpec) (h : encode v = .ok (.term t)) : t.tag.isDictionary = true := by
  unfold encode at h
  generalize v.canonical = c at h
  cases c with
  | str s =>
    simp only [encodeCanonical] at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq, Encoded.term.injEq] at h; subst h; rfl
  | node n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .node n with _ | _ <;> rw [he] at h <;> simp at h
  | bnode n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .bnode n with _ | _ <;> rw [he] at h <;> simp at h
  | stmt n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .stmt n with _ | _ <;> rw [he] at h <;> simp at h
  | tx n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .tx n with _ | _ <;> rw [he] at h <;> simp at h
  | _ => simp only [encodeCanonical, Except.ok.injEq, Encoded.term.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- Inline kinds never reach the dictionary: a value whose canonical form is an allocated
value, an integer, a boolean, a date, a date-time or a string of at most 7 bytes has no term
encoding. -/
theorem inline_never_term (v : Value) (t : TermSpec)
    (hk : match v.canonical with
      | .node _ | .bnode _ | .stmt _ | .tx _ | .int _ | .bool _ | .date _ | .dateTime _ _ => True
      | .str s => s.utf8ByteSize ≤ 7
      | _ => False) : encode v ≠ .ok (.term t) := by
  unfold encode
  generalize v.canonical = c at hk
  intro h
  cases c with
  | str s =>
    simp only [encodeCanonical] at h
    split at h
    · simp at h
    · rename_i hs; exact hs (by unfold shortMaxLen; exact hk)
  | node n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .node n with _ | _ <;> rw [he] at h <;> simp at h
  | bnode n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .bnode n with _ | _ <;> rw [he] at h <;> simp at h
  | stmt n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .stmt n with _ | _ <;> rw [he] at h <;> simp at h
  | tx n => simp only [encodeCanonical] at h; rcases he : encodeAlloc .tx n with _ | _ <;> rw [he] at h <;> simp at h
  | int _ | bool _ | date _ | dateTime _ _ => simp [encodeCanonical] at h
  | _ => exact hk.elim

end Tiramemsu.Codec
