/-
Read programs on the model: a read program run on a model state is a pure function of the
state's rows; the scan read is the model scan. The basis of every view and cascade theorem.
-/
import Tiramemsu.View.Read
import TiramemsuProofs.Store.Model
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The free monad of reads -/

section
variable {σ α β : Type} (h : (r : ROp) → σ → Except StoreError r.Res) (s : σ)

@[simp] theorem RProg.runPure_pure (a : α) : RProg.runPure h s (pure a : RProg α) = .ok a := rfl

@[simp] theorem RProg.runPure_lift (r : ROp) : RProg.runPure h s (RProg.lift r) = h r s := by
  simp only [RProg.lift, RProg.runPure]
  cases h r s <;> rfl

theorem RProg.runPure_bind (p : RProg α) (f : α → RProg β) :
    RProg.runPure h s (p >>= f) = (RProg.runPure h s p) >>= fun a => RProg.runPure h s (f a) := by
  induction p with
  | pure a => rfl
  | read r k ih =>
    show RProg.runPure h s (RProg.bind (.read r k) f) = _
    simp only [RProg.bind, RProg.runPure]
    cases h r s with
    | ok x => exact ih x
    | error e => rfl

theorem RProg.runPure_rbind (p : RProg α) (f : α → RProg β) :
    RProg.runPure h s (p.bind f) = (RProg.runPure h s p) >>= fun a => RProg.runPure h s (f a) :=
  RProg.runPure_bind h s p f

end

/-! ## Reads on a model state -/

/-- Folding a scan that only collects is the list of the scan. -/
theorem foldWithExit_collect (xs : List TripleRow) (acc : Array TripleRow) (st : ModelState) :
    (foldWithExit (m := SnapM) xs acc (fun acc r => pure (.yield (acc.push r)))) st =
      .ok (acc ++ xs.toArray) := by
  induction xs generalizing acc with
  | nil => simp [foldWithExit]; rfl
  | cons x xs ih =>
    simp only [foldWithExit]
    show (foldWithExit (m := SnapM) xs (acc.push x) _) st = _
    rw [ih]; simp

theorem scanAll_model (sp : ScanSpec) (st : ModelState) :
    (scanAll sp : SnapM (Array TripleRow)) st =
      if sp.valid then .ok (st.scanList sp).toArray else .error .invalidScan := by
  show (ModelState.scanM (m := SnapM) st sp #[] (fun acc r => pure (.yield (acc.push r)))) st = _
  unfold ModelState.scanM ModelState.scanList?
  by_cases hv : sp.valid = true
  · simp only [hv, if_true]
    rw [foldWithExit_collect]; simp
  · simp only [hv]; rfl

@[simp] theorem ROp.model_scan (sp : ScanSpec) (st : ModelState) :
    ROp.model (.scan sp) st = if sp.valid then .ok (st.scanList sp).toArray else .error .invalidScan := by
  unfold ROp.model
  have : (ROp.run (ROp.scan sp) : SnapM _) st = (scanAll sp : SnapM _) st := rfl
  rw [this, scanAll_model]
  by_cases hv : sp.valid = true <;> simp [hv]

@[simp] theorem ROp.model_triple (e : Int64) (st : ModelState) : ROp.model (.triple e) st = .ok (st.triple e) := rfl
@[simp] theorem ROp.model_counter (n : String) (st : ModelState) : ROp.model (.counter n) st = .ok (st.counter n) := rfl
@[simp] theorem ROp.model_txAtOrBefore (i : Int64) (st : ModelState) :
    ROp.model (.txAtOrBefore i) st = .ok (st.txAtOrBefore i) := rfl
@[simp] theorem ROp.model_volatileGet (s k : Int64) (st : ModelState) :
    ROp.model (.volatileGet s k) st = .ok (st.volatileGet s k) := rfl
@[simp] theorem ROp.model_lookupKey (k : TermKey) (st : ModelState) :
    ROp.model (.lookupKey k) st = .ok (modelLookupKey st k) := rfl
@[simp] theorem ROp.model_rowById (i : Nat) (st : ModelState) :
    ROp.model (.rowById i) st = .ok (modelRowById st i) := rfl

/-! ## Scans by the row predicate -/

theorem mem_scanList_iff {st : ModelState} {sp : ScanSpec} {r : TripleRow} :
    r ∈ st.scanList sp ↔ r ∈ st.triples ∧ sp.matches r = true := by
  simp [ModelState.scanList]

/-- The rows the walk families see for `x`: subject (`spo`) or object (`osp`) equal to `x`,
selected by the view. -/
theorem matches_walk_s (v : View) (x : Int64) (r : TripleRow) :
    ({ family := (walkFamilies v).1, pre := #[x], view := v } : ScanSpec).matches r = true ↔
      r.s = x ∧ v.admits r = true := by
  unfold walkFamilies
  by_cases hv : v.tx = .now
  · simp only [hv, beq_self_eq_true, if_true]
    simp [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, Family.rowFilter, Family.cols,
      Family.perm, Col.get, View.admits, TxSel.admits, hv]
    intros; assumption
  · have : (v.tx == .now) = false := by simpa using hv
    simp only [this]
    simp [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, Family.rowFilter, Family.cols, Family.perm,
      Col.get]

theorem matches_walk_o (v : View) (x : Int64) (r : TripleRow) :
    ({ family := (walkFamilies v).2, pre := #[x], view := v } : ScanSpec).matches r = true ↔
      r.o = x ∧ v.admits r = true := by
  unfold walkFamilies
  by_cases hv : v.tx = .now
  · simp only [hv, beq_self_eq_true, if_true]
    simp [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, Family.rowFilter, Family.cols,
      Family.perm, Col.get, View.admits, TxSel.admits, hv]
    intros; assumption
  · have : (v.tx == .now) = false := by simpa using hv
    simp only [this]
    simp [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, Family.rowFilter, Family.cols, Family.perm,
      Col.get]

theorem walkFamilies_valid (v : View) (x : Int64) :
    ({ family := (walkFamilies v).1, pre := #[x], view := v } : ScanSpec).valid = true ∧
    ({ family := (walkFamilies v).2, pre := #[x], view := v } : ScanSpec).valid = true := by
  unfold walkFamilies
  by_cases hv : v.tx = .now
  · simp [hv, ScanSpec.valid, Family.maxPrefix, Family.isLive]
  · have : (v.tx == .now) = false := by simpa using hv
    simp [this, ScanSpec.valid, Family.maxPrefix, Family.isLive]

/-- The neighbours of `x` in a view: the eids of the selected rows standing on `x`. -/
def nbrs (st : ModelState) (v : View) (x : Int64) : List Int64 :=
  sortDedup (((st.scanList { family := (walkFamilies v).1, pre := #[x], view := v }) ++
    (st.scanList { family := (walkFamilies v).2, pre := #[x], view := v })).map (·.eid))

theorem neighbors_model (st : ModelState) (v : View) (x : Int64) :
    (neighbors v x).onModel st = .ok (nbrs st v x) := by
  obtain ⟨h1, h2⟩ := walkFamilies_valid v x
  unfold neighbors RProg.onModel
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_scan, if_pos h1]
  simp only [bind, Except.bind]
  rw [RProg.runPure_rbind, RProg.runPure_lift, ROp.model_scan, if_pos h2]
  rfl

theorem mem_sortDedup {xs : List Int64} {y : Int64} : y ∈ sortDedup xs ↔ y ∈ xs := by
  unfold sortDedup
  rw [List.mem_eraseDups]
  exact (List.mergeSort_perm _ _).mem_iff

/-- `x` stands on `y` in a view: a selected row with eid `x` has `y` as subject or object. -/
def StandsOn (st : ModelState) (v : View) (x y : Int64) : Prop :=
  ∃ r ∈ st.triples, r.eid = x ∧ v.admits r = true ∧ (r.s = y ∨ r.o = y)

theorem mem_nbrs {st : ModelState} {v : View} {x y : Int64} : y ∈ nbrs st v x ↔ StandsOn st v y x := by
  unfold nbrs StandsOn
  rw [mem_sortDedup, List.mem_map]
  simp only [List.mem_append, mem_scanList_iff, matches_walk_s, matches_walk_o]
  constructor
  · rintro ⟨r, hr | hr, rfl⟩
    · exact ⟨r, hr.1, rfl, hr.2.2, Or.inl hr.2.1⟩
    · exact ⟨r, hr.1, rfl, hr.2.2, Or.inr hr.2.1⟩
  · rintro ⟨r, hm, rfl, ha, hs | ho⟩
    · exact ⟨r, Or.inl ⟨hm, hs, ha⟩, rfl⟩
    · exact ⟨r, Or.inr ⟨hm, ho, ha⟩, rfl⟩

end Tiramemsu.Engine
