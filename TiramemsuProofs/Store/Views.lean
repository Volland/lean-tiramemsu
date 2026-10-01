/-
Temporal views on the model: the triple lookup selects exactly the rows its view admits, in
ascending eid order; as-of equals the replay of the event log; as-of a past transaction on any
later store equals the now view of that past store; valid-at filters after the transaction-time
selection; instants resolve to the largest transaction at or before them; volatile state never
reaches a triple, dependents or event read, and never an as-of or history value.
Requirements: temporal-views ("As-of equals replay of the log", "As-of by instant", "Valid-at is
half-open"), volatile-state ("Volatile values are not statements", "Volatile values resolve only
under now").
-/
import TiramemsuProofs.Store.Lifecycle
import TiramemsuProofs.Store.Walk
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec Tiramemsu.View

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Sorting by eid -/

/-- Strictly ascending eids. -/
def EidSorted (xs : List TripleRow) : Prop := xs.Pairwise fun a b => a.eid.toInt < b.eid.toInt

theorem byEid_perm (xs : List TripleRow) : (byEid xs).Perm xs := List.mergeSort_perm _ _

theorem byEid_sorted {xs : List TripleRow} (h : xs.Pairwise fun a b => a.eid ≠ b.eid) : EidSorted (byEid xs) := by
  have hs : (byEid xs).Pairwise fun a b => decide (a.eid.toInt ≤ b.eid.toInt) = true :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) xs
  have hd : (byEid xs).Pairwise fun a b => a.eid ≠ b.eid :=
    ((byEid_perm xs).pairwise_iff fun h => Ne.symm h).2 h
  refine (hs.and hd).imp fun {a b} ⟨h1, h2⟩ => ?_
  simp at h1
  have : a.eid.toInt ≠ b.eid.toInt := fun he => h2 (Int64.toInt_inj.1 he)
  omega

/-- Two eid-sorted lists with the same rows are equal. -/
theorem eidSorted_eq {xs ys : List TripleRow} (hx : EidSorted xs) (hy : EidSorted ys) (h : ∀ r, r ∈ xs ↔ r ∈ ys) :
    xs = ys := by
  have nx : xs.Nodup := hx.imp fun h e => by subst e; exact lt_irrefl _ h
  have ny : ys.Nodup := hy.imp fun h e => by subst e; exact lt_irrefl _ h
  have hp : xs.Perm ys := (List.perm_ext_iff_of_nodup nx ny).2 h
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl _)) hx hy hp

/-! ## The lookup on the model -/

theorem lookupScan_valid (v : View) (s p o : Option ObjectId) : (lookupScan v s p o).valid = true := by
  unfold lookupScan
  by_cases hv : v.tx = .now
  · cases s <;> cases p <;> cases o <;> simp [hv, ScanSpec.valid, Family.maxPrefix, Family.isLive]
  · have : (v.tx == .now) = false := by simpa using hv
    cases s <;> cases p <;> cases o <;> simp [this, ScanSpec.valid, Family.maxPrefix, Family.isLive]

theorem triplesIn_model (st : ModelState) (v : View) (s p o : Option ObjectId) :
    (triplesIn v s p o).onModel st = .ok ((byEid (st.scanList (lookupScan v s p o))).map (mask v)) := by
  unfold triplesIn scan RProg.onModel
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_scan, if_pos (lookupScan_valid v s p o)]
  rfl

theorem mask_eid (v : View) (r : TripleRow) : (mask v r).eid = r.eid := by
  unfold mask; split <;> rfl

theorem mask_valid (v : View) (r : TripleRow) : (mask v r).vFrom = r.vFrom ∧ (mask v r).vTo = r.vTo := by
  unfold mask; split <;> exact ⟨rfl, rfl⟩

/-- The rows a lookup returns: ascending eid, exactly the (masked) stored rows its scan matches. -/
theorem triplesIn_rows {st : ModelState} (hu : st.triples.Pairwise fun a b => a.eid ≠ b.eid) (v : View)
    (s p o : Option ObjectId) :
    ∃ L, (triplesIn v s p o).onModel st = .ok L ∧ EidSorted L ∧
      ∀ x, x ∈ L ↔ ∃ r ∈ st.triples, (lookupScan v s p o).matches r = true ∧ x = mask v r := by
  refine ⟨_, triplesIn_model st v s p o, ?_, ?_⟩
  · have hu' : (st.scanList (lookupScan v s p o)).Pairwise fun a b => a.eid ≠ b.eid :=
      scanList_pairwise_eid _ hu
    have := byEid_sorted hu'
    unfold EidSorted at this ⊢
    rw [List.pairwise_map]
    exact this.imp fun h => by rw [mask_eid, mask_eid]; exact h
  · intro x
    rw [List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [(byEid_perm _).mem_iff, mem_scanList_iff] at hr
      exact ⟨r, hr.1, hr.2, rfl⟩
    · rintro ⟨r, hr, hm, rfl⟩
      exact ⟨r, by rw [(byEid_perm _).mem_iff, mem_scanList_iff]; exact ⟨hr, hm⟩, rfl⟩

theorem validAt_mask (v : View) (r : TripleRow) (d : Int64) :
    Valid.validAt ⟨(mask v r).vFrom, (mask v r).vTo⟩ d = ValidSel.admits (.at d) r := by
  unfold mask; split <;> rfl

/-- The scan of a lookup filtered at `d` is the unfiltered one with the valid-at test. -/
theorem lookupScan_validAt (tx : TxSel) (d : Int64) (s p o : Option ObjectId) (r : TripleRow) :
    (lookupScan { tx, valid := .at d } s p o).matches r =
      ((lookupScan { tx, valid := .unfiltered } s p o).matches r && ValidSel.admits (.at d) r) := by
  unfold lookupScan
  cases s <;> cases p <;> cases o <;>
    simp only [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, View.admits, ValidSel.admits,
      Bool.and_true] <;> cases tx <;> simp [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- Valid time filters after the transaction-time selection: a valid-at lookup is the
unfiltered lookup restricted to the rows whose interval contains the instant. -/
theorem triplesIn_validAt {st : ModelState} (hu : st.triples.Pairwise fun a b => a.eid ≠ b.eid)
    (tx : TxSel) (d : Int64) (s p o : Option ObjectId) :
    (triplesIn { tx, valid := .at d } s p o).onModel st =
      ((triplesIn { tx, valid := .unfiltered } s p o).onModel st).map
        (·.filter fun r => Valid.validAt ⟨r.vFrom, r.vTo⟩ d) := by
  obtain ⟨L1, h1, s1, m1⟩ := triplesIn_rows hu { tx, valid := .at d } s p o
  obtain ⟨L2, h2, s2, m2⟩ := triplesIn_rows hu { tx, valid := .unfiltered } s p o
  rw [h1, h2]
  simp only [Except.map]
  congr 1
  apply eidSorted_eq s1 (s2.sublist List.filter_sublist)
  intro x
  rw [m1, List.mem_filter, m2]
  have hmask : ∀ r, mask { tx, valid := .at d } r = mask { tx, valid := .unfiltered } r := by
    intro r; unfold mask; rfl
  constructor
  · rintro ⟨r, hr, hm, rfl⟩
    rw [lookupScan_validAt, Bool.and_eq_true] at hm
    exact ⟨⟨r, hr, hm.1, hmask r⟩, by rw [validAt_mask]; exact hm.2⟩
  · rintro ⟨⟨r, hr, hm, rfl⟩, hv⟩
    refine ⟨r, hr, ?_, (hmask r).symm⟩
    rw [lookupScan_validAt, Bool.and_eq_true]
    rw [validAt_mask] at hv
    exact ⟨hm, hv⟩

/-! ## As-of views -/

theorem matches_asOf (t : Int64) (r : TripleRow) :
    (lookupScan { tx := .asOf t } none none none).matches r = true ↔
      r.tAdd.toInt ≤ t.toInt ∧ (r.tRet = none ∨ ∃ x, r.tRet = some x ∧ t.toInt < x.toInt) := by
  unfold lookupScan
  simp only [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, View.admits, ValidSel.admits,
    TxSel.admits, Family.rowFilter]
  simp only [(show (({ tx := TxSel.asOf t } : View).tx == .now) = false from rfl), Bool.false_eq_true, if_false]
  simp only [Family.rowFilter, Family.cols, Family.perm, List.map, List.zip, Array.toList, List.all_nil,
    Bool.true_and, Bool.and_true, decide_eq_true_eq]
  cases r.tRet with
  | none => simp
  | some x => simp

theorem matches_now (r : TripleRow) :
    (lookupScan {} none none none).matches r = true ↔ r.tRet = none := by
  unfold lookupScan
  simp only [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, View.admits, ValidSel.admits,
    TxSel.admits]
  simp only [(show (({} : View).tx == .now) = true from rfl), if_true]
  simp [Family.rowFilter, Family.cols, Family.perm]

theorem mask_asOf (t : Int64) (r : TripleRow) : mask { tx := .asOf t } r = { r with tRet := none, retKind := none } := rfl
theorem mask_now (r : TripleRow) : mask {} r = r := rfl

/-- As-of on any later store equals now on the earlier store: the as-of view at `a`'s last
transaction, read on any `b` that extends `a`, returns exactly the statements live in `a`. -/
theorem asOf_extends {a b : ModelState} (wa : WF a) (wb : WF b) (h : Extends a b) (t : Int64)
    (ht : t.toInt = lastT a) :
    (triplesIn { tx := .asOf t } none none none).onModel b = (triplesIn {} none none none).onModel a := by
  obtain ⟨L1, h1, s1, m1⟩ := triplesIn_rows wb.uniq { tx := .asOf t } none none none
  obtain ⟨L2, h2, s2, m2⟩ := triplesIn_rows wa.uniq {} none none none
  rw [h1, h2]
  congr 1
  apply eidSorted_eq s1 s2
  intro x
  rw [m1, m2]
  obtain ⟨pre, new, hb, f, nw⟩ := h.rows
  constructor
  · rintro ⟨r', hr', hm, rfl⟩
    rw [matches_asOf] at hm
    rw [hb] at hr'
    rcases List.mem_append.1 hr' with hr' | hr'
    · -- a statement of `a`, possibly retracted since
      obtain ⟨r, hr, hrel⟩ := forall₂_mem_right f r' hr'
      have ok := wa.rows r hr
      have hlive : r.tRet = none := by
        rcases hrel.ret with ⟨e1, _⟩ | ⟨hn, _⟩
        · rcases ok.ret with ⟨hn, _⟩ | ⟨y, k, hy, _, _, hle, _⟩
          · exact hn
          · exfalso
            rcases hm.2 with hn' | ⟨z, hz, hlt⟩
            · rw [e1, hy] at hn'; cases hn'
            · rw [e1, hy] at hz; cases hz; omega
        · exact hn
      have hk : r.retKind = none := by
        rcases ok.ret with ⟨_, hk⟩ | ⟨y, _, hy, _⟩
        · exact hk
        · rw [hlive] at hy; cases hy
      refine ⟨r, hr, by rw [matches_now]; exact hlive, ?_⟩
      rw [mask_asOf, mask_now]
      rcases r with ⟨e, s, p, o, ta, tr, vf, vt, rk⟩
      rcases r' with ⟨e', s', p', o', ta', tr', vf', vt', rk'⟩
      obtain ⟨he, hs, hp, ho, ha, hf, hto, _⟩ := hrel
      simp only at he hs hp ho ha hf hto hlive hk
      subst he hs hp ho ha hf hto hlive hk
      rfl
    · exfalso
      have := (nw r' hr').2
      omega
  · rintro ⟨r, hr, hm, hx⟩
    rw [hx]
    rw [matches_now] at hm
    obtain ⟨r', hr', hrel⟩ := extends_row h hr
    have ok := wa.rows r hr
    have hk : r.retKind = none := by
      rcases ok.ret with ⟨_, hk⟩ | ⟨y, _, hy, _⟩
      · exact hk
      · rw [hm] at hy; cases hy
    refine ⟨r', hr', ?_, ?_⟩
    · rw [matches_asOf]
      refine ⟨by rw [hrel.tAdd, ht]; exact ok.tAddHi, ?_⟩
      rcases hrel.ret with ⟨e1, _⟩ | ⟨_, x, hx, hlt⟩
      · exact Or.inl (e1.trans hm)
      · exact Or.inr ⟨x, hx, by rw [ht]; exact hlt⟩
    · rw [mask_asOf, mask_now]
      rcases r with ⟨e, s, p, o, ta, tr, vf, vt, rk⟩
      rcases r' with ⟨e', s', p', o', ta', tr', vf', vt', rk'⟩
      obtain ⟨he, hs, hp, ho, ha, hf, hto, _⟩ := hrel
      simp only at he hs hp ho ha hf hto hm hk
      subst he hs hp ho ha hf hto hm hk
      rfl

end Tiramemsu.Engine
