/-
Temporal views and volatile state: views never read volatile state, so volatile writes change
no triple lookup, dependents read or event log entry on any view, and as-of and history values
never resolve to a volatile value; an instant resolves to the largest transaction at or before
it (or 0), monotonically, and the instant of a transaction resolves to that transaction; the
as-of view at `t` is the replay of the event log up to `t`.
Requirements: volatile-state ("Volatile values are not statements", "Volatile values resolve
only under now"), temporal-views ("As-of by instant", "As-of equals replay of the log").
-/
import TiramemsuProofs.Store.Views
import TiramemsuProofs.Store.Cascade
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec Tiramemsu.View

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The monad laws of read programs -/

theorem RProg.bind_pure' {α : Type} : ∀ (p : RProg α), RProg.bind p RProg.pure = p
  | .pure _ => rfl
  | .read r k => by simp only [RProg.bind]; congr 1; funext x; exact RProg.bind_pure' (k x)

theorem RProg.bind_assoc' {α β γ : Type} : ∀ (p : RProg α) (f : α → RProg β) (g : β → RProg γ),
    RProg.bind (RProg.bind p f) g = RProg.bind p fun a => RProg.bind (f a) g
  | .pure _, _, _ => rfl
  | .read r k, f, g => by simp only [RProg.bind]; congr 1; funext x; exact RProg.bind_assoc' (k x) f g

instance : LawfulMonad RProg := LawfulMonad.mk'
  (id_map := fun x => RProg.bind_pure' x)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => RProg.bind_assoc' x f g)

/-! ## Read programs that never read volatile state -/

/-- A read that is not a volatile lookup. -/
def NotVol (r : ROp) : Prop := ∀ s k, r ≠ .volatileGet s k

/-- Every read of the program is a non-volatile read. -/
inductive RNoVol : {α : Type} → RProg α → Prop
  | pure {α : Type} (a : α) : RNoVol (.pure a)
  | read {α : Type} (r : ROp) (k : r.Res → RProg α) : NotVol r → (∀ x, RNoVol (k x)) → RNoVol (.read r k)

theorem RNoVol.bind {α β : Type} {p : RProg α} {f : α → RProg β} (hp : RNoVol p) (hf : ∀ a, RNoVol (f a)) :
    RNoVol (p >>= f) := by
  show RNoVol (RProg.bind p f)
  induction hp with
  | pure a => exact hf a
  | read r k hr _ ih => exact RNoVol.read r _ hr fun x => ih x

theorem RNoVol.lift (r : ROp) (h : NotVol r) : RNoVol (RProg.lift r) := RNoVol.read r _ h fun x => RNoVol.pure x

theorem RNoVol.forIn_list {α β : Type} (xs : List α) (b : β) {f : α → β → RProg (ForInStep β)}
    (hf : ∀ a b, RNoVol (f a b)) : RNoVol (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact RNoVol.pure _
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine RNoVol.bind (hf x b) fun r => ?_
    cases r with
    | done b => exact RNoVol.pure _
    | yield b => exact ih b

theorem RNoVol.forIn_arr {α β : Type} (xs : Array α) (b : β) {f : α → β → RProg (ForInStep β)}
    (hf : ∀ a b, RNoVol (f a b)) : RNoVol (forIn xs b f) := by
  rw [← Array.forIn_toList]; exact RNoVol.forIn_list _ _ hf

theorem notVol_ne {r : ROp} (h : ∀ s k, r ≠ .volatileGet s k) : NotVol r := h

/-- A non-volatile read ignores the volatile table. -/
theorem model_notVol {r : ROp} (h : NotVol r) (st : ModelState) (w : List VolatileRow) :
    ROp.model r { st with volatile := w } = ROp.model r st := by
  cases r with
  | volatileGet s k => exact absurd rfl (h s k)
  | scan sp => rw [ROp.model_scan, ROp.model_scan]; rfl
  | _ => rfl

/-- A program that never reads volatile state gives the same result whatever the volatile table. -/
theorem onModel_noVol {α : Type} {p : RProg α} (h : RNoVol p) (st : ModelState) (w : List VolatileRow) :
    p.onModel { st with volatile := w } = p.onModel st := by
  induction h with
  | pure a => rfl
  | read r k hr _ ih =>
    unfold RProg.onModel at ih ⊢
    simp only [RProg.runPure]
    rw [model_notVol hr]
    cases ROp.model r st with
    | ok x => exact ih x
    | error e => rfl

macro "rnv_step" : tactic => `(tactic| first
  | apply RNoVol.bind
  | exact RNoVol.pure _ | apply RNoVol.pure
  | (apply RNoVol.lift; intro _ _ h; cases h)
  | apply RNoVol.forIn_list
  | apply RNoVol.forIn_arr
  | split
  | dsimp only
  | (refine fun _ => ?_)
  | assumption)

theorem rnv_scan (sp : ScanSpec) : RNoVol (scan sp) := by unfold scan; repeat rnv_step
theorem rnv_resolveInstant (ms : Int64) : RNoVol (resolveInstant ms) := by unfold resolveInstant; repeat rnv_step
theorem rnv_resolve (v : ViewSpec) : RNoVol (resolve v) := by
  unfold resolve; repeat (first | apply rnv_resolveInstant | rnv_step)
theorem rnv_triplesIn (v : View) (s p o : Option ObjectId) : RNoVol (triplesIn v s p o) := by
  unfold triplesIn; repeat (first | apply rnv_scan | rnv_step)
theorem rnv_triples (v : ViewSpec) (s p o : Option ObjectId) : RNoVol (triples v s p o) := by
  unfold triples; repeat (first | apply rnv_resolve | apply rnv_triplesIn | rnv_step)
theorem rnv_visible (v : View) (e : Int64) : RNoVol (visible v e) := by unfold visible; repeat rnv_step
theorem rnv_neighbors (v : View) (x : Int64) : RNoVol (neighbors v x) := by unfold neighbors; repeat rnv_step
theorem rnv_walkFuel : RNoVol walkFuel := by unfold walkFuel; repeat rnv_step
theorem rnv_walkLoop (v : View) (limit : Option Nat) :
    ∀ fuel order seen i, RNoVol (walkLoop (neighbors v) limit fuel order seen i)
  | 0, _, _, _ => RNoVol.pure _
  | fuel + 1, order, seen, i => by
    unfold walkLoop
    split
    · refine RNoVol.bind (rnv_neighbors v _) fun ns => ?_
      split
      · exact RNoVol.pure _
      · exact rnv_walkLoop v limit fuel _ _ _
    · exact RNoVol.pure _
theorem rnv_walk (v : View) (limit : Option Nat) (root : Int64) (fuel : Nat) :
    RNoVol (walk (neighbors v) limit root fuel) := by
  unfold walk; split
  · exact RNoVol.pure _
  · exact rnv_walkLoop v limit _ _ _ _
theorem rnv_dependentsIn (v : View) (root : Int64) : RNoVol (dependentsIn v root) := by
  unfold dependentsIn
  repeat (first | apply rnv_visible | apply rnv_walkFuel | apply rnv_walk | rnv_step)
theorem rnv_dependents (v : ViewSpec) (root : ObjectId) : RNoVol (dependents v root) := by
  unfold dependents; repeat (first | apply rnv_resolve | apply rnv_dependentsIn | rnv_step)
theorem rnv_eventsSince (since : Int64) : RNoVol (eventsSince since) := by
  unfold eventsSince; repeat (first | apply rnv_scan | rnv_step)

/-! ## Volatile values are not statements -/

/-- A volatile write changes only the volatile table: no statement is inserted or retracted. -/
theorem volPut_only {r : VolatileRow} {s s' : ModelStore} {u : Unit}
    (h : (Op.run (.volPut r) : ModelM Unit) s = .ok (u, s')) :
    ∃ w, s' = { s with current := { s.current with volatile := w } } := by
  have h' : (WriteStore.volatilePut r : ModelM Unit) s = .ok (u, s') := h
  rw [mvolPut] at h'
  obtain ⟨_, c, hc, rfl⟩ := data_exec rfl h'
  unfold WriteOp.step ModelState.volatilePut at hc
  cases hc
  exact ⟨_, rfl⟩

theorem volDel_only {a k : Int64} {s s' : ModelStore} {u : Unit}
    (h : (Op.run (.volDel a k) : ModelM Unit) s = .ok (u, s')) :
    ∃ w, s' = { s with current := { s.current with volatile := w } } := by
  have h' : (WriteStore.volatileDel a k : ModelM Unit) s = .ok (u, s') := h
  rw [mvolDel] at h'
  obtain ⟨_, c, hc, rfl⟩ := data_exec rfl h'
  unfold WriteOp.step ModelState.volatileDel at hc
  cases hc
  exact ⟨_, rfl⟩

/-- Setting or clearing a volatile value changes no statement and no triple lookup, dependents
read or event log on any view. -/
theorem volatile_not_statements {o : Op} (ho : (∃ r, o = .volPut r) ∨ (∃ a k, o = .volDel a k))
    {s s' : ModelStore} {u : o.Res} (h : (Op.run o : ModelM o.Res) s = .ok (u, s')) :
    s'.current.triples = s.current.triples ∧
    (∀ v sb pb ob, (triples v sb pb ob).onModel s'.current = (triples v sb pb ob).onModel s.current) ∧
    (∀ v root, (dependents v root).onModel s'.current = (dependents v root).onModel s.current) ∧
    (∀ since, (eventsSince since).onModel s'.current = (eventsSince since).onModel s.current) := by
  obtain ⟨w, hw⟩ : ∃ w, s' = { s with current := { s.current with volatile := w } } := by
    rcases ho with ⟨r, rfl⟩ | ⟨a, k, rfl⟩
    · exact volPut_only h
    · exact volDel_only h
  subst hw
  exact ⟨rfl, fun v sb pb ob => onModel_noVol (rnv_triples v sb pb ob) _ w,
    fun v root => onModel_noVol (rnv_dependents v root) _ w,
    fun since => onModel_noVol (rnv_eventsSince since) _ w⟩

/-! ## Volatile values resolve only under now -/

/-- Under as-of and history views, the values of `(s, key)` are the objects of the selected
statements, whatever the volatile table holds. -/
theorem values_not_now (v : ViewSpec) (hv : v.tx ≠ .now) (s key : ObjectId) (st : ModelState) :
    (values v s key).onModel st =
      ((triples v (some s) (some key) none).onModel st).map (·.map fun r => (⟨r.o⟩ : ObjectId)) := by
  unfold values RProg.onModel
  rw [RProg.runPure_bind]
  cases hq : RProg.runPure ROp.model st (triples v (some s) (some key) none) with
  | error e => rfl
  | ok rows =>
    simp only [bind, Except.bind, Except.map]
    have : (v.tx != .now) = true := by simpa using hv
    simp only [this, Bool.or_true, if_true]
    rfl

theorem values_not_now_volatile (v : ViewSpec) (hv : v.tx ≠ .now) (s key : ObjectId) (st : ModelState)
    (w : List VolatileRow) :
    (values v s key).onModel { st with volatile := w } = (values v s key).onModel st := by
  rw [values_not_now v hv, values_not_now v hv, onModel_noVol (rnv_triples _ _ _ _)]

/-! ## As-of by instant -/

theorem getLast_rel {α : Type} {R : α → α → Prop} {l : List α} (hp : l.Pairwise R) {x y : α}
    (hx : l.getLast? = some x) (hy : y ∈ l) : y = x ∨ R y x := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hx
  rcases List.mem_append.1 hy with h | h
  · exact Or.inr ((List.pairwise_append.1 hp).2.2 y h x (List.mem_singleton_self x))
  · exact Or.inl (List.mem_singleton.1 h)

theorem pairwise_trichotomy {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => by cases ha
  | c :: l, hp, a, b, ha, hb => by
    rcases List.pairwise_cons.1 hp with ⟨hc, hl⟩
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hc b hb'))
    · exact Or.inr (Or.inr (hc a ha'))
    · exact pairwise_trichotomy hl ha' hb'

/-- The step of `txAtOrBefore`. -/
def bestStep (i : Int64) (best : Option TxRow) (x : TxRow) : Option TxRow :=
  if x.instant.toInt ≤ i.toInt then
    match best with
    | none => some x
    | some b => if b.instant.toInt < x.instant.toInt then some x else best
  else best

theorem txAtOrBefore_eq (st : ModelState) (i : Int64) : st.txAtOrBefore i = st.txs.foldl (bestStep i) none := rfl

theorem fold_best (i : Int64) : ∀ (L : List TxRow) (best : Option TxRow),
    (∀ b, best = some b → ∀ x ∈ L, b.instant.toInt < x.instant.toInt) →
    L.Pairwise (fun a b => a.instant.toInt < b.instant.toInt) →
    L.foldl (bestStep i) best =
      match (L.filter fun x => decide (x.instant.toInt ≤ i.toInt)).getLast? with
      | none => best
      | some x => some x
  | [], best, _, _ => rfl
  | x :: L, best, hb, hp => by
    rcases List.pairwise_cons.1 hp with ⟨hx, hl⟩
    simp only [List.foldl_cons]
    by_cases hxi : x.instant.toInt ≤ i.toInt
    · have hstep : bestStep i best x = some x := by
        unfold bestStep
        rw [if_pos hxi]
        cases best with
        | none => rfl
        | some b =>
          show (if b.instant.toInt < x.instant.toInt then some x else some b) = some x
          rw [if_pos (hb b rfl x (List.mem_cons_self ..))]
      rw [hstep, fold_best i L (some x) (fun b hb' y hy => by cases hb'; exact hx y hy) hl]
      rw [List.filter_cons_of_pos (by simpa using hxi)]
      cases h : (L.filter fun x => decide (x.instant.toInt ≤ i.toInt)).getLast? with
      | none =>
        have : L.filter (fun x => decide (x.instant.toInt ≤ i.toInt)) = [] := by
          simpa using h
        rw [this]; rfl
      | some y =>
        rw [List.getLast?_cons, h]; rfl
    · have hstep : bestStep i best x = best := by unfold bestStep; rw [if_neg hxi]
      rw [hstep, fold_best i L best (fun b hb' y hy => hb b hb' y (List.mem_cons_of_mem _ hy)) hl]
      rw [List.filter_cons_of_neg (by simpa using hxi)]

theorem resolveInstant_model (st : ModelState) (ms : Int64) :
    (resolveInstant ms).onModel st = .ok (match st.txAtOrBefore ms with | some r => r.t | none => 0) := by
  unfold resolveInstant RProg.onModel
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_txAtOrBefore]
  cases st.txAtOrBefore ms <;> rfl

theorem wf_txs_t {st : ModelState} (hwf : WF st) :
    st.txs.Pairwise (fun a b => a.t.toInt < b.t.toInt) ∧ ∀ x ∈ st.txs, 1 ≤ x.t.toInt := by
  have h := hwf.txs
  constructor
  · have : (st.txs.map (·.t.toInt)).Pairwise (· < ·) := by
      rw [h, List.pairwise_map]
      exact List.pairwise_lt_range.imp fun hab => by omega
    exact List.pairwise_map.1 this
  · intro x hx
    have : x.t.toInt ∈ st.txs.map (·.t.toInt) := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [h] at this
    obtain ⟨k, _, hk⟩ := List.mem_map.1 this
    omega

/-- An instant resolves, within the snapshot, to the largest committed transaction whose
instant is at or before it, or to 0 when there is none. -/
theorem resolveInstant_spec {st : ModelState} (hwf : WF st) (ms : Int64) :
    ∃ t : Int64, (resolveInstant ms).onModel st = .ok t ∧
      ((t = 0 ∧ ∀ x ∈ st.txs, ms.toInt < x.instant.toInt) ∨
       (∃ x ∈ st.txs, x.t = t ∧ x.instant.toInt ≤ ms.toInt ∧
          ∀ y ∈ st.txs, y.instant.toInt ≤ ms.toInt → y.t.toInt ≤ t.toInt)) := by
  have hinst : st.txs.Pairwise (fun a b => a.instant.toInt < b.instant.toInt) := List.pairwise_map.1 hwf.inst
  have hf := fold_best ms st.txs none (fun b hb => by cases hb) hinst
  rw [resolveInstant_model, txAtOrBefore_eq, hf]
  cases hl : (st.txs.filter fun x => decide (x.instant.toInt ≤ ms.toInt)).getLast? with
  | none =>
    refine ⟨0, rfl, Or.inl ⟨rfl, fun x hx => ?_⟩⟩
    have : st.txs.filter (fun x => decide (x.instant.toInt ≤ ms.toInt)) = [] := by simpa using hl
    have := List.filter_eq_nil_iff.1 this x hx
    simp at this; omega
  | some x =>
    refine ⟨x.t, rfl, Or.inr ⟨x, ?_, rfl, ?_, fun y hy hyi => ?_⟩⟩
    · exact (List.mem_filter.1 (List.mem_of_getLast? hl)).1
    · simpa using (List.mem_filter.1 (List.mem_of_getLast? hl)).2
    · have hp := (wf_txs_t hwf).1.sublist (List.filter_sublist (p := fun x => decide (x.instant.toInt ≤ ms.toInt)))
      rcases getLast_rel hp hl (List.mem_filter.2 ⟨hy, by simpa using hyi⟩) with rfl | h
      · exact le_refl _
      · exact le_of_lt h

/-- Resolution is monotone in the instant. -/
theorem resolveInstant_mono {st : ModelState} (hwf : WF st) {ms1 ms2 t1 t2 : Int64} (hle : ms1.toInt ≤ ms2.toInt)
    (h1 : (resolveInstant ms1).onModel st = .ok t1) (h2 : (resolveInstant ms2).onModel st = .ok t2) :
    t1.toInt ≤ t2.toInt := by
  obtain ⟨u1, e1, c1⟩ := resolveInstant_spec hwf ms1
  obtain ⟨u2, e2, c2⟩ := resolveInstant_spec hwf ms2
  rw [h1] at e1; cases e1
  rw [h2] at e2; cases e2
  have hpos := (wf_txs_t hwf).2
  rcases c1 with ⟨rfl, _⟩ | ⟨x1, hx1, rfl, hi1, _⟩
  · rcases c2 with ⟨rfl, _⟩ | ⟨x2, hx2, rfl, _, _⟩
    · exact le_refl _
    · have := hpos x2 hx2; simp; omega
  · rcases c2 with ⟨_, hall⟩ | ⟨x2, _, rfl, _, hmax⟩
    · have := hall x1 hx1; omega
    · exact hmax x1 hx1 (le_trans hi1 hle)

/-- The instant of a committed transaction resolves to that transaction. -/
theorem resolveInstant_instant {st : ModelState} (hwf : WF st) {x : TxRow} (hx : x ∈ st.txs) :
    (resolveInstant x.instant).onModel st = .ok x.t := by
  obtain ⟨u, e, c⟩ := resolveInstant_spec hwf x.instant
  rw [e]
  rcases c with ⟨_, hall⟩ | ⟨y, hy, rfl, hyi, hmax⟩
  · have := hall x hx; omega
  · congr 1
    have h1 := hmax x hx (le_refl _)
    have hboth : st.txs.Pairwise (fun a b => a.t.toInt < b.t.toInt ∧ a.instant.toInt < b.instant.toInt) :=
      (wf_txs_t hwf).1.and (List.pairwise_map.1 hwf.inst)
    rcases pairwise_trichotomy hboth hy hx with rfl | h | h
    · rfl
    · exact Int64.toInt_inj.1 (by omega)
    · omega

/-- The as-of view at an instant is the as-of view at the transaction it resolves to. -/
theorem triples_asOf_instant (st : ModelState) (ms : Int64) (valid : ValidSel) (s p o : Option ObjectId) :
    (triples { tx := .asOf (.instant ms), valid } s p o).onModel st =
      (resolveInstant ms).onModel st >>= fun t => (triplesIn { tx := .asOf t, valid } s p o).onModel st := by
  unfold triples resolve RProg.onModel
  rw [RProg.runPure_bind]
  simp only []
  rw [RProg.runPure_bind]
  cases RProg.runPure ROp.model st (resolveInstant ms) <;> rfl

/-! ## As-of equals the replay of the log -/

/-- The log order as one integer key: time, then asserts before retracts, then eid. -/
def evKey (e : Event) : Int :=
  e.t.toInt * 2 ^ 66 + (if e.op = .assert then 0 else 2 ^ 65) + e.eid.raw.toInt

theorem eventLe_iff (a b : Event) : eventLe a b = true ↔ evKey a ≤ evKey b := by
  have a1 := a.t.le_toInt; have a2 := a.t.toInt_lt
  have b1 := b.t.le_toInt; have b2 := b.t.toInt_lt
  have c1 := a.eid.raw.le_toInt; have c2 := a.eid.raw.toInt_lt
  have d1 := b.eid.raw.le_toInt; have d2 := b.eid.raw.toInt_lt
  unfold eventLe evKey
  rcases a with ⟨ta, ea, oa, ka⟩
  rcases b with ⟨tb, eb, ob, kb⟩
  simp only at *
  by_cases ht : ta.toInt = tb.toInt
  · have hne : (ta.toInt != tb.toInt) = false := by simpa using ht
    rw [if_neg (by simp [hne])]
    cases oa <;> cases ob <;> simp <;> omega
  · have hne : (ta.toInt != tb.toInt) = true := by simpa using ht
    rw [if_pos hne]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have : ta.toInt + 1 ≤ tb.toInt := h
      have : (ta.toInt + 1) * 2 ^ 66 ≤ tb.toInt * 2 ^ 66 := Int.mul_le_mul_of_nonneg_right this (by norm_num)
      split_ifs <;> omega
    · intro h
      by_contra hlt
      have : tb.toInt + 1 ≤ ta.toInt := by omega
      have : (tb.toInt + 1) * 2 ^ 66 ≤ ta.toInt * 2 ^ 66 := Int.mul_le_mul_of_nonneg_right this (by norm_num)
      split_ifs at h <;> omega

theorem eventLe_trans (a b c : Event) (hab : eventLe a b = true) (hbc : eventLe b c = true) :
    eventLe a c = true := by
  rw [eventLe_iff] at *; omega

theorem eventLe_total (a b : Event) : (eventLe a b || eventLe b a) = true := by
  have h := le_total (evKey a) (evKey b)
  rw [← eventLe_iff, ← eventLe_iff] at h
  rcases h with h | h <;> simp [h]

/-- The log in its order, up to transaction `T`. -/
def logUpTo (st : ModelState) (T : Int64) : List Event :=
  ((eventsOf st.triples).mergeSort eventLe).filter fun e => decide (e.t.toInt ≤ T.toInt)

/-- Applying one log entry: an assert adds its statement, a retract removes it. -/
def applyEv (f : Int64 → Bool) (ev : Event) : Int64 → Bool :=
  fun y => if y = ev.eid.raw then ev.op == .assert else f y

/-- The statements present after replaying a log from the empty state. -/
def replay (L : List Event) : Int64 → Bool := L.foldl applyEv fun _ => false

theorem foldl_applyEv : ∀ (L : List Event) (f : Int64 → Bool) (y : Int64),
    L.foldl applyEv f y = match (L.filter fun ev => decide (ev.eid.raw = y)).getLast? with
      | none => f y
      | some ev => ev.op == .assert
  | [], f, y => rfl
  | x :: L, f, y => by
    simp only [List.foldl_cons]
    rw [foldl_applyEv L (applyEv f x) y]
    cases h : (L.filter fun ev => decide (ev.eid.raw = y)).getLast? with
    | none =>
      have hn : L.filter (fun ev => decide (ev.eid.raw = y)) = [] := by simpa using h
      by_cases hx : x.eid.raw = y
      · rw [List.filter_cons_of_pos (by simpa using hx), hn]
        simp [applyEv, hx]
      · rw [List.filter_cons_of_neg (by simpa using hx), hn]
        simp [applyEv, Ne.symm hx]
    | some ev =>
      by_cases hx : x.eid.raw = y
      · rw [List.filter_cons_of_pos (by simpa using hx), List.getLast?_cons, h]; rfl
      · rw [List.filter_cons_of_neg (by simpa using hx), h]

/-- The assert entry of a row. -/
def assertEv (r : TripleRow) : Event := { t := r.tAdd, eid := ⟨r.eid⟩, op := .assert, kind := none }

/-- The retract entry of a retracted row. -/
def retractEv (r : TripleRow) (t : Int64) : Event :=
  { t, eid := ⟨r.eid⟩, op := .retract, kind := r.retKind.bind RetKind.ofCode? }

theorem mem_eventsOf {rows : List TripleRow} {ev : Event} :
    ev ∈ eventsOf rows ↔ ∃ r ∈ rows, ev = assertEv r ∨ ∃ t, r.tRet = some t ∧ ev = retractEv r t := by
  unfold eventsOf
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, he⟩
    refine ⟨r, hr, ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact Or.inl rfl
    · cases ht : r.tRet with
      | none => rw [ht] at he; cases he
      | some t => rw [ht] at he; exact Or.inr ⟨t, rfl, List.mem_singleton.1 he⟩
  · rintro ⟨r, hr, rfl | ⟨t, ht, rfl⟩⟩
    · exact ⟨r, hr, List.mem_cons_self ..⟩
    · refine ⟨r, hr, List.mem_cons_of_mem _ ?_⟩
      rw [ht]; exact List.mem_singleton_self _

/-- Replaying the log up to `T` leaves exactly the statements asserted at or before `T` and
not retracted at or before `T`. -/
theorem replay_spec {st : ModelState} (hwf : WF st) (T e : Int64) :
    replay (logUpTo st T) e = true ↔
      ∃ r ∈ st.triples, r.eid = e ∧ r.tAdd.toInt ≤ T.toInt ∧
        (r.tRet = none ∨ ∃ x, r.tRet = some x ∧ T.toInt < x.toInt) := by
  have hsorted : ((eventsOf st.triples).mergeSort eventLe).Pairwise (fun a b => eventLe a b = true) :=
    List.pairwise_mergeSort eventLe_trans eventLe_total _
  have hmemL : ∀ ev, ev ∈ logUpTo st T ↔ ev ∈ eventsOf st.triples ∧ ev.t.toInt ≤ T.toInt := by
    intro ev
    unfold logUpTo
    rw [List.mem_filter, (List.mergeSort_perm _ _).mem_iff]
    simp
  set F := (logUpTo st T).filter fun ev => decide (ev.eid.raw = e) with hF
  have hFs : F.Pairwise (fun a b => eventLe a b = true) :=
    (hsorted.sublist List.filter_sublist).sublist List.filter_sublist
  have hmemF : ∀ ev, ev ∈ F ↔ ev ∈ eventsOf st.triples ∧ ev.t.toInt ≤ T.toInt ∧ ev.eid.raw = e := by
    intro ev; rw [hF, List.mem_filter, hmemL]; simp [and_assoc]
  -- the events of the statement with eid `e`
  have hrow : ∀ ev ∈ F, ∃ r ∈ st.triples, r.eid = e ∧
      (ev = assertEv r ∨ ∃ t, r.tRet = some t ∧ ev = retractEv r t) := by
    intro ev hev
    obtain ⟨hev, _, he⟩ := (hmemF ev).1 hev
    obtain ⟨r, hr, h⟩ := mem_eventsOf.1 hev
    refine ⟨r, hr, ?_, h⟩
    rcases h with rfl | ⟨t, _, rfl⟩ <;> exact he
  have huniq : ∀ r ∈ st.triples, ∀ r' ∈ st.triples, r.eid = r'.eid → r = r' := by
    intro r hr r' hr' h
    by_contra hne
    have : Std.Symm (fun a b : TripleRow => a.eid ≠ b.eid) := ⟨fun _ _ h => Ne.symm h⟩
    exact hwf.uniq.forall hr hr' hne h
  unfold replay
  rw [foldl_applyEv, ← hF]
  constructor
  · intro h
    cases hl : F.getLast? with
    | none => rw [hl] at h; cases h
    | some ev =>
      rw [hl] at h
      have hev := List.mem_of_getLast? hl
      obtain ⟨r, hr, hre, hk⟩ := hrow ev hev
      rcases hk with rfl | ⟨t, ht, rfl⟩
      · refine ⟨r, hr, hre, ((hmemF _).1 hev).2.1, ?_⟩
        cases hret : r.tRet with
        | none => exact Or.inl rfl
        | some x =>
          refine Or.inr ⟨x, rfl, ?_⟩
          by_contra hle
          have hin : retractEv r x ∈ F := (hmemF _).2
            ⟨mem_eventsOf.2 ⟨r, hr, Or.inr ⟨x, hret, rfl⟩⟩, by simp [retractEv]; omega, hre⟩
          rcases getLast_rel hFs hl hin with h' | h'
          · simp [retractEv, assertEv] at h'
          · have ok := hwf.rows r hr
            rcases ok.ret with ⟨hn, _⟩ | ⟨y, _, hy, _, hle', _⟩
            · rw [hret] at hn; cases hn
            · rw [hret] at hy; cases hy
              rw [eventLe_iff] at h'
              simp only [evKey, retractEv, assertEv] at h'
              have e1 : (2 : Int) ^ 65 > 0 := by norm_num
              simp at h'
              omega
      · simp [retractEv] at h
  · rintro ⟨r, hr, hre, hadd, hret⟩
    have hin : assertEv r ∈ F := (hmemF _).2 ⟨mem_eventsOf.2 ⟨r, hr, Or.inl rfl⟩, hadd, hre⟩
    cases hl : F.getLast? with
    | none => simp [List.getLast?_eq_none_iff.1 hl] at hin
    | some ev =>
      have hev := List.mem_of_getLast? hl
      obtain ⟨r', hr', hre', hk⟩ := hrow ev hev
      have := huniq r hr r' hr' (hre.trans hre'.symm)
      subst this
      rcases hk with rfl | ⟨t, ht, rfl⟩
      · rfl
      · exfalso
        have := ((hmemF _).1 hev).2.1
        simp only [retractEv] at this
        rcases hret with hn | ⟨x, hx, hlt⟩
        · rw [hn] at ht; cases ht
        · rw [hx] at ht; cases ht; omega

/-- As-of equals the replay of the log: the as-of view at `T` returns, ascending by eid and
masked, exactly the statements that replaying the event log entries with time `≤ T`, in log
order from the empty state, leaves present. -/
theorem asOf_eq_replay {st : ModelState} (hwf : WF st) (T : Int64) :
    ∃ L, (triplesIn { tx := .asOf T } none none none).onModel st = .ok L ∧ EidSorted L ∧
      (∀ x ∈ L, ∃ r ∈ st.triples, x = { r with tRet := none, retKind := none }) ∧
      ∀ e, e ∈ L.map (·.eid) ↔ replay (logUpTo st T) e = true := by
  obtain ⟨L, hL, hs, hm⟩ := triplesIn_rows hwf.uniq { tx := .asOf T } none none none
  refine ⟨L, hL, hs, fun x hx => ?_, fun e => ?_⟩
  · obtain ⟨r, hr, _, rfl⟩ := (hm x).1 hx
    exact ⟨r, hr, mask_asOf T r⟩
  · rw [replay_spec hwf, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨r, hr, hmt, rfl⟩ := (hm x).1 hx
      rw [matches_asOf] at hmt
      exact ⟨r, hr, (mask_eid _ r).symm, hmt⟩
    · rintro ⟨r, hr, rfl, hmt⟩
      exact ⟨mask _ r, (hm _).2 ⟨r, hr, (matches_asOf T r).2 hmt, rfl⟩, mask_eid _ r⟩

end Tiramemsu.Engine
