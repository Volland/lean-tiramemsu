/-
Laws of the term dictionary, proven on the pure model `Dict`: lookup after intern, idempotent
intern, append-only rows, fresh ids, the `2^60 − 1` bound, key/id uniqueness on reachable
dictionaries, and the decode round trip. The codec facts the round trip needs enter as the
hypothesis `CodecLaws` (discharged in `TiramemsuProofs.Codec.Laws`), so these theorems use only
the standard axioms.
-/
import Tiramemsu.Term.Dict
import Mathlib.Data.List.Nodup
import Mathlib.Order.Basic

namespace Tiramemsu.Term

open Tiramemsu.Codec

--# @lat: [[codec#Term Dictionary]]

/-- The codec facts the dictionary round trip relies on. -/
structure CodecLaws : Prop where
  inline : ∀ v x, encode v = .ok (.inline x) → decodeInline x = .ok (some v.canonical)
  term : ∀ v t, encode v = .ok (.term t) → t.value = .ok v.canonical ∧ t.tag.isDictionary = true
  layout : ∀ t i, i < 2 ^ 60 → (termId t i).tag = .ok t ∧ (termId t i).upayload.toNat = i ∧
    (termId t i).tagBits = t.toUInt64
  decodeDict : ∀ x t, x.tag = .ok t → t.isDictionary = true → decodeInline x = .ok none

namespace Dict

/-- The invariant of reachable dictionaries. -/
structure WF (d : Dict) : Prop where
  ids : ∀ r ∈ d.rows, 1 ≤ r.id ∧ r.id < d.next
  nodupIds : (d.rows.map (·.id)).Nodup
  nodupKeys : d.rows.Pairwise (fun a b => a.key.equiv b.key = false)
  next_pos : 1 ≤ d.next
  next_le : d.next ≤ termIdMax + 1

theorem empty_wf : Dict.empty.WF :=
  ⟨by simp [Dict.empty], by simp [Dict.empty], by simp [Dict.empty], by simp [Dict.empty],
    by simp [Dict.empty, termIdMax]⟩

theorem TermKey.equiv_symm (a b : TermKey) : a.equiv b = b.equiv a := by
  unfold TermKey.equiv; exact Bool.beq_comm

theorem TermKey.equiv_trans {a b c : TermKey} (h1 : a.equiv b = true) (h2 : b.equiv c = true) :
    a.equiv c = true := by
  unfold TermKey.equiv at *; simp only [beq_iff_eq] at *; rw [h1, h2]

theorem TermKey.equiv_refl (a : TermKey) : a.equiv a = true := by
  unfold TermKey.equiv; simp

theorem lookup_some {d : Dict} {k : TermKey} {i : Nat} (h : d.lookup k = some i) :
    ∃ r ∈ d.rows, r.key.equiv k = true ∧ r.id = i := by
  unfold lookup at h
  rcases hf : d.rows.find? (fun r => r.key.equiv k) with _ | r
  · rw [hf] at h; cases h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨r, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩

theorem lookup_none {d : Dict} {k : TermKey} (h : d.lookup k = none) :
    ∀ r ∈ d.rows, r.key.equiv k = false := by
  unfold lookup at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro r hr; simpa using h r hr

theorem byId_mem {d : Dict} (hw : d.WF) {r : Row} (hr : r ∈ d.rows) : d.byId r.id = some r := by
  unfold byId
  rcases hf : d.rows.find? (·.id == r.id) with _ | r'
  · rw [List.find?_eq_none] at hf; simpa using hf r hr
  · have hm := List.mem_of_find?_eq_some hf
    have he : r'.id = r.id := by simpa using (List.find?_some hf)
    have := List.inj_on_of_nodup_map hw.nodupIds hm hr he
    exact this ▸ hf

theorem byId_none_zero {d : Dict} (hw : d.WF) : d.byId 0 = none := by
  unfold byId
  rw [List.find?_eq_none]
  intro r hr; have := (hw.ids r hr).1; simp; omega

/-! ## Intern -/

/-- A value is found by lookup right after it is interned. -/
theorem lookup_intern (d : Dict) (k : TermKey) (n : Option UInt64) (i : Nat) (d' : Dict)
    (h : d.intern k n = .ok (i, d')) : d'.lookup k = some i := by
  unfold intern at h
  split at h
  · rename_i j hj; cases h; exact hj
  · rename_i hn
    split at h
    · cases h
      have hno := lookup_none hn
      unfold lookup
      rw [List.find?_append, List.find?_eq_none.mpr (fun r hr => by simpa using hno r hr)]
      simp [Row.key, TermKey.equiv_refl]
    · cases h

/-- Interning a present key changes nothing. -/
theorem intern_idem (d : Dict) (k : TermKey) (n : Option UInt64) (i : Nat) (h : d.lookup k = some i) :
    d.intern k n = .ok (i, d) := by
  unfold intern; rw [h]

/-- Interning keeps the previous rows as a prefix and never decreases `next_term`. -/
theorem intern_append_only (d : Dict) (k : TermKey) (n : Option UInt64) (i : Nat) (d' : Dict)
    (h : d.intern k n = .ok (i, d')) : d.rows <+: d'.rows ∧ d.next ≤ d'.next := by
  unfold intern at h
  split at h
  · cases h; exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  · split at h
    · cases h; exact ⟨List.prefix_append _ _, by simp⟩
    · cases h

/-- Interning an absent key returns the previous `next_term` and advances it by one. -/
theorem fresh_id (d : Dict) (k : TermKey) (n : Option UInt64) (h : d.lookup k = none)
    (hle : d.next ≤ termIdMax) :
    ∃ d', d.intern k n = .ok (d.next, d') ∧ d'.next = d.next + 1 ∧
      d'.rows = d.rows ++ [⟨d.next, k.tag, k.lex, k.dt, k.lang, n⟩] := by
  unfold intern; rw [h, if_pos hle]; exact ⟨_, rfl, rfl, rfl⟩

/-- A full dictionary rejects a new key with `IdSpaceExhausted TERM` and is unchanged. -/
theorem intern_full (d : Dict) (k : TermKey) (n : Option UInt64) (h : d.lookup k = none)
    (hfull : termIdMax < d.next) : d.intern k n = .error (.idSpaceExhausted .term) := by
  unfold intern; rw [h, if_neg (by omega)]

theorem intern_wf (d : Dict) (hw : d.WF) (k : TermKey) (n : Option UInt64) (i : Nat) (d' : Dict)
    (h : d.intern k n = .ok (i, d')) : d'.WF ∧ 1 ≤ i ∧ i < d'.next := by
  unfold intern at h
  split at h
  · rename_i j hj
    cases h
    obtain ⟨r, hr, -, rfl⟩ := lookup_some hj
    exact ⟨hw, (hw.ids r hr).1, (hw.ids r hr).2⟩
  · rename_i hn
    split at h
    · rename_i hle
      cases h
      have hno := lookup_none hn
      have hnp := hw.next_pos
      refine ⟨⟨?_, ?_, ?_, by simp, by simp; omega⟩, hnp, by simp⟩
      · intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · have := hw.ids r hr; simp; omega
        · exact ⟨hnp, by simp⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨hw.nodupIds, by simp, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        simp only [List.mem_map] at ha
        obtain ⟨r, hr, rfl⟩ := ha
        have := (hw.ids r hr).2; simp at *; omega
      · rw [List.pairwise_append]
        refine ⟨hw.nodupKeys, by simp, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        exact hno a ha
    · cases h

/-! ## Key and id uniqueness -/

/-- Each id belongs to at most one key: two keys found with the same id are equal as the
`term_key` index compares them. -/
theorem ids_unique (d : Dict) (hw : d.WF) (k₁ k₂ : TermKey) (i : Nat) (h₁ : d.lookup k₁ = some i)
    (h₂ : d.lookup k₂ = some i) : k₁.equiv k₂ = true := by
  obtain ⟨r₁, m₁, e₁, rfl⟩ := lookup_some h₁
  obtain ⟨r₂, m₂, e₂, i₂⟩ := lookup_some h₂
  have := List.inj_on_of_nodup_map hw.nodupIds m₁ m₂ i₂.symm
  subst this
  rw [TermKey.equiv_symm] at e₁
  exact TermKey.equiv_trans e₁ e₂

theorem pairwise_unique (l : List Row) (hp : l.Pairwise (fun a b => a.key.equiv b.key = false)) :
    ∀ r₁ r₂, r₁ ∈ l → r₂ ∈ l → r₁.key.equiv r₂.key = true → r₁ = r₂ := by
  induction l with
  | nil => intro r₁ r₂ m₁; simp at m₁
  | cons a l ih =>
    intro r₁ r₂ m₁ m₂ h
    rw [List.pairwise_cons] at hp
    simp only [List.mem_cons] at m₁ m₂
    rcases m₁ with rfl | m₁ <;> rcases m₂ with rfl | m₂
    · rfl
    · have := hp.1 _ m₂; rw [this] at h; cases h
    · have := hp.1 _ m₁; rw [TermKey.equiv_symm, this] at h; cases h
    · exact ih hp.2 r₁ r₂ m₁ m₂ h

/-- Each key belongs to at most one row. -/
theorem key_unique (d : Dict) (hw : d.WF) (r₁ r₂ : Row) (m₁ : r₁ ∈ d.rows) (m₂ : r₂ ∈ d.rows)
    (h : r₁.key.equiv r₂.key = true) : r₁ = r₂ :=
  pairwise_unique d.rows hw.nodupKeys r₁ r₂ m₁ m₂ h

theorem internSpec_wf (d : Dict) (hw : d.WF) (t : TermSpec) (i : Nat) (d' : Dict)
    (h : d.internSpec t = .ok (i, d')) : d'.WF ∧ 1 ≤ i ∧ i < d'.next := by
  unfold internSpec at h
  cases hdt : t.datatype with
  | none =>
    rw [hdt] at h
    exact intern_wf d hw _ _ i d' h
  | some iri =>
    rw [hdt] at h
    simp only [bind, Except.bind] at h
    rcases hj : d.intern ⟨.iri, iri, none, none⟩ none with e | ⟨j, d1⟩
    · rw [hj] at h; cases h
    · rw [hj] at h
      simp only [pure, Except.pure] at h
      exact intern_wf d1 (intern_wf d hw _ _ j d1 hj).1 _ _ i d' h

/-- Every dictionary reached from the empty one by interning values. -/
inductive Reachable : Dict → Prop
  | empty : Reachable Dict.empty
  | intern {d d' : Dict} {v : Value} {x : ObjectId} :
      Reachable d → d.internValue v = .ok (x, d') → Reachable d'

theorem internValue_wf (d : Dict) (hw : d.WF) (v : Value) (x : ObjectId) (d' : Dict)
    (h : d.internValue v = .ok (x, d')) : d'.WF := by
  unfold internValue at h
  split at h
  · cases h
  · cases h; exact hw
  · simp only [bind, Except.bind] at h
    rcases hs : d.internSpec _ with e | ⟨i, d1⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact (internSpec_wf d hw _ i d1 hs).1

theorem reachable_wf (d : Dict) (h : Reachable d) : d.WF := by
  induction h with
  | empty => exact empty_wf
  | intern _ hi ih => exact internValue_wf _ ih _ _ _ hi

/-- Key uniqueness on every reachable dictionary: each id maps to at most one key and each key to
at most one row. -/
theorem reachable_unique (d : Dict) (h : Reachable d) :
    (∀ k₁ k₂ i, d.lookup k₁ = some i → d.lookup k₂ = some i → k₁.equiv k₂ = true) ∧
      (∀ r₁ r₂, r₁ ∈ d.rows → r₂ ∈ d.rows → r₁.key.equiv r₂.key = true → r₁ = r₂) := by
  have hw := reachable_wf d h
  exact ⟨fun k₁ k₂ i => ids_unique d hw k₁ k₂ i, fun r₁ r₂ => key_unique d hw r₁ r₂⟩

/-! ## The decode round trip -/

theorem intern_prefix_byId {d d' : Dict} (hw' : d'.WF) (hp : d.rows <+: d'.rows) {r : Row}
    (hr : r ∈ d.rows) : d'.byId r.id = some r :=
  byId_mem hw' (hp.subset hr)

theorem intern_row (d : Dict) (hw : d.WF) (k : TermKey) (n : Option UInt64) (i : Nat) (d' : Dict)
    (h : d.intern k n = .ok (i, d')) : ∃ r ∈ d'.rows, r.id = i ∧ r.key.equiv k = true := by
  obtain ⟨r, hr, he, hi⟩ := lookup_some (lookup_intern d k n i d' h)
  exact ⟨r, hr, hi, he⟩

theorem key_fields {a b : TermKey} (h : a.equiv b = true) :
    a.tag = b.tag ∧ a.lex = b.lex ∧ a.dt.getD 0 = b.dt.getD 0 ∧ a.lang.getD "" = b.lang.getD "" := by
  unfold TermKey.equiv TermKey.coalesced at h
  simp only [beq_iff_eq, Prod.mk.injEq] at h
  exact h

theorem valueFromTerm_congr (tag : Tag) (lex : String) (d1 d2 l1 l2 : Option String)
    (hd : d1.getD "" = d2.getD "") (hl : l1.getD "" = l2.getD "") :
    valueFromTerm tag lex d1 l1 = valueFromTerm tag lex d2 l2 := by
  cases tag <;> simp [valueFromTerm, hd, hl]

/-- Decoding the id returned by interning any value gives the value's canonical form. -/
theorem decode_internValue (laws : CodecLaws) (d : Dict) (hw : d.WF) (v : Value) (x : ObjectId)
    (d' : Dict) (h : d.internValue v = .ok (x, d')) : d'.decode x = .ok v.canonical := by
  unfold internValue at h
  rcases ht : encode v with e | enc <;> rw [ht] at h
  · cases h
  cases enc with
  | inline y =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hy, hd⟩ := h
    subst hd
    rw [← hy]
    unfold decode
    rw [laws.inline v y ht]
  | term t =>
    obtain ⟨hval, hdict⟩ := laws.term v t ht
    simp only [bind, Except.bind] at h
    rcases hs : d.internSpec t with e | ⟨i, d1⟩
    · rw [hs] at h; cases h
    rw [hs] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hw1, hi1, hi2⟩ := internSpec_wf d hw t i d1 hs
    have hlt : i < 2 ^ 60 := by have := hw1.next_le; unfold termIdMax at this; omega
    obtain ⟨htag, hpay, -⟩ := laws.layout t.tag i hlt
    unfold decode
    rw [laws.decodeDict _ _ htag hdict, htag]
    simp only [hpay]
    -- the term row and the datatype row
    unfold internSpec at hs
    cases hdt : t.datatype with
    | none =>
      rw [hdt] at hs
      obtain ⟨r, hr, hri, hrk⟩ := intern_row d hw _ _ i d1 hs
      obtain ⟨k1, k2, k3, k4⟩ := key_fields hrk
      rw [← hri, byId_mem hw1 hr]
      simp only [Row.key] at k1 k2 k3 k4
      dsimp only
      rw [if_pos k1, ← hval, TermSpec.value, k1, k2]
      apply valueFromTerm_congr
      · -- an absent datatype stays absent (a stray 0 names no row)
        rw [hdt]
        simp only [Option.getD_none] at k3 ⊢
        cases hrd : r.dt with
        | none => rfl
        | some raw =>
          rw [hrd] at k3; simp at k3; subst k3
          simp only [Option.bind_some]
          unfold iriText
          have : (⟨0⟩ : ObjectId).upayload.toNat = 0 := by decide
          simp [this, byId_none_zero hw1]
      · exact k4
    | some iri =>
      rw [hdt] at hs
      simp only [bind, Except.bind] at hs
      rcases hj : d.intern ⟨.iri, iri, none, none⟩ none with e | ⟨j, d0⟩
      · rw [hj] at hs; cases hs
      rw [hj] at hs
      simp only [pure, Except.pure] at hs
      obtain ⟨hw0, hj1, hj2⟩ := intern_wf d hw _ _ j d0 hj
      obtain ⟨rj, hrj, hrji, hrjk⟩ := intern_row d hw _ _ j d0 hj
      obtain ⟨rjt, rjl, -, -⟩ := key_fields hrjk
      obtain ⟨r, hr, hri, hrk⟩ := intern_row d0 hw0 _ _ i d1 hs
      obtain ⟨k1, k2, k3, k4⟩ := key_fields hrk
      simp only [Row.key] at k1 k2 k3 k4 rjt rjl
      have hpre := (intern_append_only d0 _ _ i d1 hs).1
      have hj60 : j < 2 ^ 60 := by have := hw0.next_le; unfold termIdMax at this; omega
      obtain ⟨jtag, jpay, jbits⟩ := laws.layout .iri j hj60
      have hraw : (termId .iri j).raw ≠ 0 := by
        intro e
        have : (termId .iri j).upayload = 0 := by
          unfold ObjectId.upayload; rw [e]; decide
        rw [this] at jpay; simp at jpay; omega
      have hrdt : r.dt = some (termId .iri j).raw := by
        cases hrd : r.dt with
        | none => rw [hrd] at k3; simp at k3; exact absurd k3.symm hraw
        | some raw => rw [hrd] at k3; simp at k3; rw [k3]
      rw [← hri, byId_mem hw1 hr]
      dsimp only
      rw [if_pos k1, ← hval, TermSpec.value, k1, k2, hdt, hrdt]
      apply valueFromTerm_congr
      · simp only [Option.bind_some, Option.getD_some]
        unfold iriText
        dsimp only
        simp only [show ({ raw := (termId Tag.iri j).raw } : ObjectId) = termId .iri j from rfl, jbits,
          jpay, beq_self_eq_true, ite_true]
        rw [← hrji, intern_prefix_byId hw1 hpre hrj]
        simp [rjt, rjl]
      · exact k4

end Dict

end Tiramemsu.Term
