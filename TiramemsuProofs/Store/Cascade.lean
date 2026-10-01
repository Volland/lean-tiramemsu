/-
The cascade and the dependents read: the dependents of a statement on any view are, root first
and without duplicates, exactly the statements standing on it through a chain of visible
statements (empty when it is not visible); the engine's cascade set of a live statement is the
dependents read on the now view, failing with `CascadeLimitExceeded` exactly when that closure
is larger than `max_cascade`; and a retraction retracts exactly the cascade set at the current
transaction, the root with the operation's kind and the rest with `cascade` (explicit) or the
same kind.
Requirements: retraction-cascade ("Cascade equals the dependents closure", "Cascade order, kinds
and cycles", "Cascade size limit", "Dependents on any view").
-/
import TiramemsuProofs.Store.Footprint
import TiramemsuProofs.Store.Walk
import TiramemsuProofs.Store.Lifecycle
import Tiramemsu.Engine.Supersede
import Tiramemsu.Engine.Graph
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec Tiramemsu.View EngM

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Read-only engine steps -/

/-- One step of a footprint proof: through binds, branches, loops and the basic steps. -/
macro "eops_step" : tactic => `(tactic| first
  | apply EOps.bind
  | exact EOps.pure _ | apply EOps.pure | apply EOps.throw | apply EOps.fail | apply EOps.get
  | apply EOps.set | apply EOps.modify | apply EOps.modifyGet | apply EOps.report
  | apply EOps.ofExcept | apply EOps.codec
  | exact EOps.rd _ (isRead_read _)
  | exact EOps.reads isRead_read _
  | apply EOps.forIn_list
  | apply EOps.forIn_arr
  | apply EOps.mapM
  | split
  | (refine fun _ => ?_)
  | dsimp only
  | assumption
  | (intro))

theorem ero_sysLookup (i : String) : ERO (sysLookup i) := by unfold sysLookup; repeat eops_step
theorem ero_liveOfSP (s p : ObjectId) : ERO (liveOfSP s p) := by unfold liveOfSP; repeat eops_step
theorem ero_liveOfP (p : ObjectId) : ERO (liveOfP p) := by unfold liveOfP; repeat eops_step
theorem ero_liveOfS (p : ObjectId) : ERO (liveOfS p) := by unfold liveOfS; repeat eops_step
theorem ero_iriOf (x : ObjectId) : ERO (iriOf x) := by unfold iriOf; repeat eops_step
theorem ero_tagOf (x : ObjectId) (pos : Position) : ERO (tagOf x pos) := by unfold tagOf; repeat eops_step
theorem ero_originOk (x : ObjectId) : ERO (originOk x) := by unfold originOk; repeat eops_step
theorem ero_live (x : ObjectId) : ERO (live x) := by unfold live; repeat eops_step
theorem ero_isMembership (x : ObjectId) : ERO (isMembership x) := by
  unfold isMembership; repeat (first | apply ero_sysLookup | eops_step)
theorem ero_subjectTypeRows (x : ObjectId) : ERO (subjectTypeRows x) := by
  unfold subjectTypeRows; repeat (first | apply ero_sysLookup | apply ero_liveOfSP | eops_step)
theorem ero_tagsOf (x : List ObjectId) : ERO (tagsOf x) := by
  unfold tagsOf; repeat (first | apply ero_iriOf | eops_step)
theorem ero_subjectTypeViolations (x : ObjectId) (t : List Tag) : ERO (subjectTypeViolations x t) := by
  unfold subjectTypeViolations; repeat (first | apply ero_liveOfP | apply ero_tagOf | eops_step)
theorem ero_validateFlagRetraction (e : ObjectId) : ERO (validateFlagRetraction e) := by
  unfold validateFlagRetraction
  repeat (first | apply ero_sysLookup | apply ero_subjectTypeRows | apply ero_tagsOf | apply ero_subjectTypeViolations | eops_step)

/-! ## Statements on a model state -/

theorem triple_some {st : ModelState} {e : Int64} {r : TripleRow} (h : st.triple e = some r) :
    r ∈ st.triples ∧ r.eid = e := by
  unfold ModelState.triple at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem triple_of_mem {st : ModelState} (hu : st.triples.Pairwise fun a b => a.eid ≠ b.eid)
    {r : TripleRow} (hr : r ∈ st.triples) : st.triple r.eid = some r := by
  unfold ModelState.triple
  cases h : st.triples.find? (·.eid == r.eid) with
  | none => exact absurd (List.find?_eq_none.1 h r hr) (by simp)
  | some r' =>
    have hm := List.mem_of_find?_eq_some h
    have he : r'.eid = r.eid := by simpa using List.find?_some h
    by_contra hne
    have hne' : r' ≠ r := fun h' => hne (by rw [h'])
    have : Std.Symm (fun a b : TripleRow => a.eid ≠ b.eid) := ⟨fun _ _ h => Ne.symm h⟩
    exact (hu.forall hm hr hne') he

theorem triple_none {st : ModelState} {e : Int64} (h : st.triple e = none) : ∀ r ∈ st.triples, r.eid ≠ e := by
  unfold ModelState.triple at h
  intro r hr he
  have := List.find?_eq_none.1 h r hr
  simp [he] at this

/-- Statement ids are unique and issued below `next_stmt`. -/
structure Bounded (st : ModelState) : Prop where
  uniq : st.triples.Pairwise fun a b => a.eid ≠ b.eid
  rows : ∀ r ∈ st.triples, rawTag r.eid = 3 ∧ 0 ≤ eidCtr r.eid ∧ eidCtr r.eid < nextStmt st

theorem WF.bounded {st : ModelState} (h : WF st) : Bounded st :=
  ⟨h.uniq, fun r hr => let ok := h.rows r hr; ⟨ok.tag, ok.ctrLo, ok.ctrHi⟩⟩

theorem TxInv.bounded {s : ModelStore} (h : TxInv s) : Bounded s.current :=
  ⟨h.uniq, fun r hr => let ok := h.rows r hr; ⟨ok.tag, ok.ctrLo, ok.ctrHi⟩⟩

/-- There are at most `next_stmt` statements. -/
theorem eids_card {st : ModelState} (hb : Bounded st) :
    (st.triples.map (·.eid)).toFinset.card ≤ (nextStmt st).toNat := by
  have h := Finset.card_le_card_of_injOn (s := (st.triples.map (·.eid)).toFinset)
    (t := Finset.Ico (0 : Int) (nextStmt st)) eidCtr ?_ ?_
  · simpa using h
  · intro x hx
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨_, h1, h2⟩ := hb.rows r hr
    simp only [Finset.coe_Ico, Set.mem_Ico]
    exact ⟨h1, h2⟩
  · intro x hx y hy hxy
    simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_map] at hx hy
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨r', hr', rfl⟩ := hy
    have t1 := (hb.rows r hr).1
    have t2 := (hb.rows r' hr').1
    unfold rawTag at t1 t2
    unfold eidCtr at hxy
    apply Int64.toInt_inj.1
    omega

/-! ## The dependents read -/

theorem visible_model (st : ModelState) (v : View) (e : Int64) :
    (visible v e).onModel st = .ok (match st.triple e with | some r => v.admits r | none => false) := by
  unfold visible RProg.onModel
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_triple]
  cases st.triple e <;> rfl

theorem walkFuel_model (st : ModelState) :
    walkFuel.onModel st = .ok ((nextStmt st).toNat + 1) := by
  unfold walkFuel RProg.onModel
  rw [RProg.runPure_bind, RProg.runPure_lift, ROp.model_counter]
  rfl

theorem edge_nbrs (st : ModelState) (v : View) : Edge (nbrs st v) = StandsOn st v := by
  funext x y; exact propext mem_nbrs

/-- Everything that reaches a root other than the root is a stored statement. -/
theorem reach_mem {st : ModelState} {v : View} {root x : Int64} (h : Reach (nbrs st v) root x) :
    x = root ∨ x ∈ st.triples.map (·.eid) := by
  unfold Reach at h
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
  · exact Or.inl h
  · rw [edge_nbrs] at hc
    obtain ⟨r, hr, he, _⟩ := hc
    exact Or.inr (List.mem_map.2 ⟨r, hr, he⟩)

/-- The walk over the model's neighbours from a stored root, with the read fuel. -/
theorem walk_model_spec {st : ModelState} (hb : Bounded st) (v : View) {root : Int64}
    (hroot : root ∈ st.triples.map (·.eid)) :
    ∃ o : List Int64, o.Nodup ∧ o.head? = some root ∧
      (∀ x, x ∈ o ↔ Relation.ReflTransGen (StandsOn st v) x root) ∧
      ∀ limit, (walk (neighbors v) limit root ((nextStmt st).toNat + 1)).onModel st =
        .ok (if limit.any (· < o.length) then .exceeded else .done o.toArray) := by
  obtain ⟨o, hnd, hhd, hmem, hw⟩ := walk_spec (nbrs st v) root ((nextStmt st).toNat + 1)
    (st.triples.map (·.eid)) (fun x hx => by rcases reach_mem hx with rfl | h; exact hroot; exact h)
    (by have := eids_card hb; omega)
  refine ⟨o, hnd, hhd, fun x => by rw [hmem x]; unfold Reach; rw [edge_nbrs], fun limit => ?_⟩
  unfold RProg.onModel
  rw [walk_runPure ROp.model st (neighbors v) (nbrs st v) (fun x => neighbors_model st v x), hw]

/-- Dependents on any view: empty when the root is not visible; otherwise, root first and
without duplicates, exactly the statements standing on the root through a chain of
statements visible in the view. -/
theorem dependentsIn_spec {st : ModelState} (hb : Bounded st) (v : View) (root : Int64) :
    ∃ o, (dependentsIn v root).onModel st = .ok o ∧
      ((∃ r ∈ st.triples, r.eid = root ∧ v.admits r = true) →
        o.Nodup ∧ o.head? = some root ∧ ∀ x, x ∈ o ↔ Relation.ReflTransGen (StandsOn st v) x root) ∧
      ((¬ ∃ r ∈ st.triples, r.eid = root ∧ v.admits r = true) → o = []) := by
  by_cases hvis : ∃ r ∈ st.triples, r.eid = root ∧ v.admits r = true
  · obtain ⟨r, hr, he, ha⟩ := hvis
    obtain ⟨o, hnd, hhd, hmem, hw⟩ := walk_model_spec hb v (root := root) (List.mem_map.2 ⟨r, hr, he⟩)
    refine ⟨o, ?_, fun _ => ⟨hnd, hhd, hmem⟩, fun h => absurd ⟨r, hr, he, ha⟩ h⟩
    have ht := triple_of_mem hb.uniq hr
    rw [he] at ht
    unfold dependentsIn RProg.onModel
    rw [RProg.runPure_bind]
    have := visible_model st v root
    unfold RProg.onModel at this
    rw [this, ht]
    simp only [ha, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false]
    rw [RProg.runPure_rbind]
    have hf := walkFuel_model st
    unfold RProg.onModel at hf
    rw [hf]
    simp only [bind, Except.bind]
    rw [RProg.runPure_rbind]
    have hw := hw none
    unfold RProg.onModel at hw
    rw [hw]
    simp only [Option.any_none, Bool.false_eq_true, if_false]
    rfl
  · refine ⟨[], ?_, fun h => absurd h hvis, fun _ => rfl⟩
    unfold dependentsIn RProg.onModel
    rw [RProg.runPure_bind]
    have := visible_model st v root
    unfold RProg.onModel at this
    rw [this]
    cases ht : st.triple root with
    | none => rfl
    | some r =>
      obtain ⟨hr, he⟩ := triple_some ht
      have : v.admits r = false := by
        cases h : v.admits r
        · rfl
        · exact absurd ⟨r, hr, he, h⟩ hvis
      simp only [this]; rfl

/-! ## Engine computations on the model -/

theorem runModel_bind {α β : Type} : ∀ (p : SProg α) (f : α → SProg β) (s : ModelStore),
    SProg.runModel (p >>= f) s = match SProg.runModel p s with
      | .ok (a, s') => SProg.runModel (f a) s'
      | .error e => .error e
  | .pure a, f, s => rfl
  | .op o k, f, s => by
    show SProg.runModel (SProg.op o fun x => SProg.bind (k x) f) s = _
    simp only [SProg.runModel]
    cases (Op.run o : ModelM o.Res) s with
    | ok p => rcases p with ⟨x, s'⟩; exact runModel_bind (k x) f s'
    | error e => rfl

theorem runModel_toS {α : Type} : ∀ (p : RProg α) (s : ModelStore),
    SProg.runModel p.toS s = match p.onModel s.current with
      | .ok a => .ok (a, s)
      | .error e => .error e
  | .pure a, s => rfl
  | .read r k, s => by
    simp only [RProg.toS, SProg.runModel, RProg.onModel, RProg.runPure]
    rw [show (Op.run (.read r) : ModelM _) = (ROp.run r : ModelM _) from rfl, read_model]
    cases ROp.model r s.current with
    | ok x => exact runModel_toS (k x) s
    | error e => rfl

theorem erun_bind {α β : Type} (x : EngM α) (f : α → EngM β) (ctx : TxCtx) (s : ModelStore) :
    erun (x >>= f) ctx s = match erun x ctx s with
      | .ok (.ok (a, c), s') => erun (f a) c s'
      | .ok (.error e, s') => .ok (.error e, s')
      | .error e => .error e := by
  unfold erun
  show SProg.runModel (SProg.bind ((x.run ctx).run) _) s = _
  rw [show ∀ (p : SProg (Except Error (α × TxCtx))) g, SProg.bind p g = p >>= g from fun _ _ => rfl,
    runModel_bind]
  rcases SProg.runModel ((x.run ctx).run) s with e | ⟨r, s'⟩
  · rfl
  · rcases r with e | ⟨a, c⟩ <;> rfl

@[simp] theorem erun_pure {α : Type} (a : α) (ctx : TxCtx) (s : ModelStore) :
    erun (pure a : EngM α) ctx s = .ok (.ok (a, ctx), s) := rfl

@[simp] theorem erun_throw {α : Type} (e : Error) (ctx : TxCtx) (s : ModelStore) :
    erun (throw e : EngM α) ctx s = .ok (.error e, s) := rfl

@[simp] theorem erun_fail {α : Type} (e : Error) (ctx : TxCtx) (s : ModelStore) :
    erun (EngM.fail e : EngM α) ctx s = .ok (.error e, s) := rfl

@[simp] theorem erun_get (ctx : TxCtx) (s : ModelStore) :
    erun (get : EngM TxCtx) ctx s = .ok (.ok (ctx, ctx), s) := rfl

theorem erun_reads {α : Type} (p : RProg α) (ctx : TxCtx) (s : ModelStore) :
    erun (EngM.reads p) ctx s = match p.onModel s.current with
      | .ok a => .ok (.ok (a, ctx), s)
      | .error e => .error e := by
  unfold erun EngM.reads
  show SProg.runModel ((p.toS >>= fun a => pure (Except.ok a)) >>= _) s = _
  rw [runModel_bind, runModel_bind, runModel_toS]
  cases p.onModel s.current <;> rfl

theorem erun_rd (r : ROp) (ctx : TxCtx) (s : ModelStore) :
    erun (EngM.rd r) ctx s = match ROp.model r s.current with
      | .ok a => .ok (.ok (a, ctx), s)
      | .error e => .error e := by
  have : erun (EngM.rd r) ctx s = erun (EngM.reads (RProg.lift r)) ctx s := rfl
  rw [this, erun_reads]
  simp only [RProg.onModel, RProg.lift, RProg.runPure]
  cases ROp.model r s.current <;> rfl

/-! ## The cascade set -/

/-- The cascade set of a stored statement: the now-view dependents closure, root first and
without duplicates; the engine returns it, unchanged store and context, when it has at most
`max_cascade` members and fails with `CascadeLimitExceeded root max_cascade` exactly when it
has more. -/
theorem cascadeSet_spec {s : ModelStore} (hb : Bounded s.current) (ctx : TxCtx) {root : ObjectId}
    (hroot : root.raw ∈ s.current.triples.map (·.eid)) :
    ∃ o : List Int64, o.Nodup ∧ o.head? = some root.raw ∧
      (∀ x, x ∈ o ↔ Relation.ReflTransGen (StandsOn s.current {}) x root.raw) ∧
      erun (cascadeSet root) ctx s =
        .ok ((if ctx.opts.maxCascade < o.length then .error (.cascadeLimitExceeded root ctx.opts.maxCascade)
              else .ok (o.map (⟨·⟩), ctx)), s) := by
  obtain ⟨o, hnd, hhd, hmem, hw⟩ := walk_model_spec hb {} hroot
  refine ⟨o, hnd, hhd, hmem, ?_⟩
  unfold cascadeSet
  rw [erun_bind, erun_get]
  simp only []
  rw [erun_bind, erun_reads, walkFuel_model]
  simp only []
  rw [erun_bind, erun_reads, hw]
  simp only [Option.any_some, decide_eq_true_eq]
  by_cases hl : ctx.opts.maxCascade < o.length
  · simp only [hl, if_true]; rfl
  · simp only [hl, if_false]; rfl

theorem admits_now (r : TripleRow) : View.admits {} r = true ↔ r.tRet = none := by
  simp [View.admits, TxSel.admits, ValidSel.admits, Option.isNone_iff_eq_none]

/-- The dependents read on a visible root is the completed walk. -/
theorem dependentsIn_visible {st : ModelState} (hb : Bounded st) {v : View} {r : TripleRow}
    (hr : r ∈ st.triples) (ha : v.admits r = true) {o : List Int64}
    (hw : (walk (neighbors v) none r.eid ((nextStmt st).toNat + 1)).onModel st = .ok (.done o.toArray)) :
    (dependentsIn v r.eid).onModel st = .ok o := by
  have ht := triple_of_mem hb.uniq hr
  unfold dependentsIn RProg.onModel
  rw [RProg.runPure_bind]
  have := visible_model st v r.eid
  unfold RProg.onModel at this
  rw [this, ht]
  simp only [ha, bind, Except.bind, Bool.not_true, Bool.false_eq_true, if_false]
  rw [RProg.runPure_rbind]
  have hf := walkFuel_model st
  unfold RProg.onModel at hf
  rw [hf]
  simp only [bind, Except.bind]
  rw [RProg.runPure_rbind]
  unfold RProg.onModel at hw
  rw [hw]
  rfl

/-- Under the now view, the dependents of a live statement are its cascade set, as lists: the
cascade returns exactly the dependents read unless it is longer than `max_cascade`. -/
theorem cascadeSet_eq_dependents {s : ModelStore} (hb : Bounded s.current) (ctx : TxCtx) {root : ObjectId}
    {r : TripleRow} (hr : r ∈ s.current.triples) (he : r.eid = root.raw) (hlive : r.tRet = none) :
    ∃ o, (dependentsIn {} root.raw).onModel s.current = .ok o ∧
      erun (cascadeSet root) ctx s =
        .ok ((if ctx.opts.maxCascade < o.length then .error (.cascadeLimitExceeded root ctx.opts.maxCascade)
              else .ok (o.map (⟨·⟩), ctx)), s) := by
  obtain ⟨o, -, -, -, hw⟩ := walk_model_spec hb {} (root := root.raw) (List.mem_map.2 ⟨r, hr, he⟩)
  refine ⟨o, ?_, ?_⟩
  · rw [← he]
    apply dependentsIn_visible hb hr ((admits_now r).2 hlive)
    rw [he]; simpa using hw none
  · unfold cascadeSet
    rw [erun_bind, erun_get]
    simp only []
    rw [erun_bind, erun_reads, walkFuel_model]
    simp only []
    rw [erun_bind, erun_reads, hw]
    simp only [Option.any_some, decide_eq_true_eq]
    by_cases hl : ctx.opts.maxCascade < o.length
    · simp only [hl, if_true]; rfl
    · simp only [hl, if_false]; rfl

/-! ## Retraction of the cascade set -/

theorem erun_op (o : Op) (ctx : TxCtx) (s : ModelStore) :
    erun (EngM.op o) ctx s = match (Op.run o : ModelM o.Res) s with
      | .ok (x, s') => .ok (.ok (x, ctx), s')
      | .error e => .error e := by
  unfold erun EngM.op
  show SProg.runModel ((SProg.lift o >>= fun a => pure (Except.ok a)) >>= _) s = _
  rw [runModel_bind, runModel_bind]
  simp only [SProg.lift, SProg.runModel]
  cases (Op.run o : ModelM o.Res) s with
  | ok p => rcases p with ⟨x, s'⟩; rfl
  | error e => rfl

/-- The store with one statement retracted. -/
def retractIn (s : ModelStore) (e t k : Int64) : ModelStore :=
  { s with current := { s.current with triples := s.current.triples.map (Store.retractRow e t k) } }

/-- Retracting a live statement retracts it at `last_t + 1` and changes nothing else. -/
theorem retractRow_live {s : ModelStore} (hu : s.current.triples.Pairwise fun a b => a.eid ≠ b.eid)
    {e : ObjectId} {k : RetKind} {c c' : TxCtx} {d : Bool} {s' : ModelStore}
    (h : erun (EngM.retractRow e k) c s = .ok (.ok (d, c'), s'))
    {r : TripleRow} (hr : r ∈ s.current.triples) (he : r.eid = e.raw) (hl : r.tRet = none) :
    ∃ lastT, s.committed.counter "last_t" = some lastT ∧ s' = retractIn s e.raw (lastT + 1) k.code := by
  unfold EngM.retractRow at h
  rw [erun_bind, erun_op, show (Op.run (.retract e.raw k) : ModelM Bool) = retractRun e.raw k from rfl] at h
  cases hr1 : (retractRun e.raw k : ModelM Bool) s with
  | error x => rw [hr1] at h; cases h
  | ok p =>
    rcases p with ⟨b, s1⟩
    rw [hr1] at h
    simp only [] at h
    obtain ⟨lastT, hlt, -, -, hcase⟩ := retract_spec' hr1
    have ht := triple_of_mem hu hr
    rw [he] at ht
    rcases hcase with ⟨-, -, hnot⟩ | ⟨-, -, r', ht', -, hs1⟩
    · have := hnot r ht; rw [hl] at this; cases this
    · refine ⟨lastT, hlt, ?_⟩
      have hro := ERO.store ?_ h
      · rw [hro, hs1]; rfl
      · repeat (first | apply ero_isMembership | eops_step)

/-- The kind a member of a cascade gets. -/
def cascadeKind (kind : RetKind) (root e : Int64) : RetKind :=
  if e = root then kind else if kind != .explicit then kind else .cascade

/-- The rows after retracting the members of `L` at `t`, each with its cascade kind. -/
def retractSet (L : List Int64) (t : Int64) (kind : RetKind) (root : Int64) (x : TripleRow) : TripleRow :=
  if x.eid ∈ L then { x with tRet := some t, retKind := some (cascadeKind kind root x.eid).code } else x

theorem map_retractSet_cons {e t : Int64} {kind : RetKind} {root : Int64} {L : List Int64} (he : e ∉ L)
    (rows : List TripleRow) :
    (rows.map (Store.retractRow e t (cascadeKind kind root e).code)).map (retractSet L t kind root) =
      rows.map (retractSet (e :: L) t kind root) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, retractSet, Store.retractRow, List.mem_cons]
  by_cases hx : x.eid = e
  · subst hx; simp [he]
  · have : (x.eid == e) = false := by simpa using hx
    simp only [this, hx, false_or, Bool.false_eq_true, if_false]

theorem retractIn_uniq {s : ModelStore} (hu : s.current.triples.Pairwise fun a b => a.eid ≠ b.eid) (e t k : Int64) :
    (retractIn s e t k).current.triples.Pairwise fun a b => a.eid ≠ b.eid := by
  unfold retractIn
  simp only [List.pairwise_map]
  refine hu.imp fun {a b} h => ?_
  simp only [Store.retractRow]
  split <;> split <;> exact h

theorem retractIn_live {s : ModelStore} {e t k x : Int64} (hx : x ≠ e)
    (h : ∃ r ∈ s.current.triples, r.eid = x ∧ r.tRet = none) :
    ∃ r ∈ (retractIn s e t k).current.triples, r.eid = x ∧ r.tRet = none := by
  obtain ⟨r, hr, he, hl⟩ := h
  refine ⟨r, ?_, he, hl⟩
  unfold retractIn
  simp only [List.mem_map]
  refine ⟨r, hr, ?_⟩
  simp only [Store.retractRow]
  have : (r.eid == e) = false := by simpa [he] using hx
  simp [this]

theorem cascadeKind_step {kind : RetKind} {root e : Int64} {first : Bool} {L : List Int64}
    (h1 : first = true → (e :: L).head? = some root) (h2 : first = false → root ∉ e :: L) :
    (if (first || kind != .explicit) = true then kind else .cascade) = cascadeKind kind root e := by
  unfold cascadeKind
  cases first
  · have : e ≠ root := fun h => h2 rfl (by rw [h]; exact List.mem_cons_self ..)
    simp [this]
  · have : e = root := by simpa using h1 rfl
    simp [this]

theorem retractSet_nil (t : Int64) (kind : RetKind) (root : Int64) (rows : List TripleRow) :
    rows.map (retractSet [] t kind root) = rows := by
  conv_rhs => rw [← List.map_id rows]
  apply List.map_congr_left
  intro x _
  simp [retractSet]

/-- The retraction loop: retracts the members of a list of distinct live statements, each with
its cascade kind, at `last_t + 1`. -/
theorem loop_retract {f : ObjectId → Bool → EngM (ForInStep Bool)} {kind : RetKind} {root : Int64}
    (hf : ∀ (e : ObjectId) (first : Bool) (c : TxCtx) (s : ModelStore) (st : ForInStep Bool) (c' : TxCtx)
      (s' : ModelStore), (s.current.triples.Pairwise fun a b => a.eid ≠ b.eid) →
      (∃ r ∈ s.current.triples, r.eid = e.raw ∧ r.tRet = none) →
      erun (f e first) c s = .ok (.ok (st, c'), s') →
      st = .yield false ∧ ∃ lt, s.committed.counter "last_t" = some lt ∧
        s' = retractIn s e.raw (lt + 1) (if (first || kind != .explicit) = true then kind else .cascade).code) :
    ∀ (L : List Int64) (first : Bool) (c : TxCtx) (s : ModelStore) (b : Bool) (c' : TxCtx) (s' : ModelStore),
      L.Nodup → (s.current.triples.Pairwise fun a b => a.eid ≠ b.eid) →
      (∀ e ∈ L, ∃ r ∈ s.current.triples, r.eid = e ∧ r.tRet = none) →
      (first = true → L.head? = some root) → (first = false → root ∉ L) →
      erun (forIn (L.map (⟨·⟩ : Int64 → ObjectId)) first f) c s = .ok (.ok (b, c'), s') →
      ∃ lt, (L ≠ [] → s.committed.counter "last_t" = some lt) ∧
        s' = { s with current := { s.current with triples := s.current.triples.map (retractSet L (lt + 1) kind root) } }
  | [], first, c, s, b, c', s', _, _, _, _, _, h => by
    simp only [List.map_nil, List.forIn_nil, erun_pure] at h
    cases h
    refine ⟨0, fun h => absurd rfl h, ?_⟩
    rw [retractSet_nil]
  | e :: L, first, c, s, b, c', s', hnd, hu, hlive, h1, h2, h => by
    rw [List.map_cons, List.forIn_cons, erun_bind] at h
    obtain ⟨he, hnd'⟩ := List.nodup_cons.1 hnd
    cases hs : erun (f ⟨e⟩ first) c s with
    | error x => rw [hs] at h; cases h
    | ok p =>
      rcases p with ⟨r1, s1⟩
      rcases r1 with x | ⟨st, c1⟩
      · rw [hs] at h; cases h
      · rw [hs] at h
        obtain ⟨hst, lt, hlt, hs1⟩ := hf ⟨e⟩ first c s st c1 s1 hu (hlive e (List.mem_cons_self ..)) hs
        subst hst
        simp only [] at h
        rw [cascadeKind_step h1 h2] at hs1
        have hu1 : s1.current.triples.Pairwise fun a b => a.eid ≠ b.eid := by rw [hs1]; exact retractIn_uniq hu _ _ _
        have hlive1 : ∀ x ∈ L, ∃ r ∈ s1.current.triples, r.eid = x ∧ r.tRet = none := by
          intro x hx
          rw [hs1]
          exact retractIn_live (fun h => he (by have h' : x = e := h; rw [← h']; exact hx)) (hlive x (List.mem_cons_of_mem _ hx))
        have hroot : root ∉ L := by
          cases first
          · exact fun h => h2 rfl (List.mem_cons_of_mem _ h)
          · have : e = root := by simpa using h1 rfl
            subst this; exact he
        obtain ⟨lt', hlt', hs'⟩ := loop_retract hf L false c1 s1 b c' s' hnd' hu1 hlive1 (fun h => by cases h) (fun _ => hroot) h
        refine ⟨lt, fun _ => hlt, ?_⟩
        have hrest : s1.current.triples.map (retractSet L (lt' + 1) kind root) =
            s1.current.triples.map (retractSet L (lt + 1) kind root) := by
          by_cases hL : L = []
          · subst hL; rw [retractSet_nil, retractSet_nil]
          · have h3 := hlt' hL
            rw [hs1] at h3
            have h4 : s.committed.counter "last_t" = some lt' := h3
            rw [hlt] at h4; cases h4; rfl
        rw [hs', hrest, hs1]
        unfold retractIn
        simp only []
        rw [map_retractSet_cons he]

/-! ## Steps that keep the transaction context -/

/-- A computation that returns the context it was given. -/
def KeepsCtx {α : Type} (x : EngM α) : Prop :=
  ∀ ctx s r c s', erun x ctx s = .ok (.ok (r, c), s') → c = ctx

theorem KeepsCtx.bind {α β : Type} {x : EngM α} {f : α → EngM β} (hx : KeepsCtx x) (hf : ∀ a, KeepsCtx (f a)) :
    KeepsCtx (x >>= f) := by
  intro ctx s r c s' h
  rw [erun_bind] at h
  cases h1 : erun x ctx s with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rcases p with ⟨q, s1⟩
    rcases q with e | ⟨a, c1⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      exact (hf a c1 s1 r c s' h).trans (hx ctx s a c1 s1 h1)

theorem KeepsCtx.pure {α : Type} (a : α) : KeepsCtx (pure a : EngM α) := by
  intro ctx s r c s' h; cases h; rfl
theorem KeepsCtx.throw {α : Type} (e : Error) : KeepsCtx (throw e : EngM α) := by
  intro ctx s r c s' h; cases h
theorem KeepsCtx.fail {α : Type} (e : Error) : KeepsCtx (EngM.fail e : EngM α) := by
  intro ctx s r c s' h; cases h
theorem KeepsCtx.get : KeepsCtx (get : EngM TxCtx) := by
  intro ctx s r c s' h; cases h; rfl
theorem KeepsCtx.reads {α : Type} (p : RProg α) : KeepsCtx (EngM.reads p) := by
  intro ctx s r c s' h
  rw [erun_reads] at h
  cases hp : p.onModel s.current <;> rw [hp] at h <;> cases h; rfl
theorem KeepsCtx.op (o : Op) : KeepsCtx (EngM.op o) := by
  intro ctx s r c s' h
  rw [erun_op] at h
  cases hp : (Op.run o : ModelM o.Res) s with
  | ok p => rcases p with ⟨x, s1⟩; rw [hp] at h; cases h; rfl
  | error e => rw [hp] at h; cases h
theorem KeepsCtx.rd (r : ROp) : KeepsCtx (EngM.rd r) := KeepsCtx.op _
theorem KeepsCtx.ofExcept {α : Type} (e : Except Error α) : KeepsCtx (EngM.ofExcept e) := by
  cases e
  · exact KeepsCtx.throw _
  · exact KeepsCtx.pure _
theorem KeepsCtx.codec {α : Type} (pos : Position) (e : Except CodecError α) : KeepsCtx (EngM.codec pos e) := by
  cases e
  · exact KeepsCtx.throw _
  · exact KeepsCtx.pure _
theorem KeepsCtx.forIn_list {α β : Type} (xs : List α) (b : β) {f : α → β → EngM (ForInStep β)}
    (hf : ∀ a b, KeepsCtx (f a b)) : KeepsCtx (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact KeepsCtx.pure _
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine KeepsCtx.bind (hf x b) fun r => ?_
    cases r with
    | done b => exact KeepsCtx.pure _
    | yield b => exact ih b
theorem KeepsCtx.forIn_arr {α β : Type} (xs : Array α) (b : β) {f : α → β → EngM (ForInStep β)}
    (hf : ∀ a b, KeepsCtx (f a b)) : KeepsCtx (forIn xs b f) := by
  rw [← Array.forIn_toList]; exact KeepsCtx.forIn_list _ _ hf
theorem KeepsCtx.mapM {α β : Type} (xs : List α) {f : α → EngM β} (hf : ∀ a, KeepsCtx (f a)) :
    KeepsCtx (xs.mapM f) := by
  induction xs with
  | nil => exact KeepsCtx.pure _
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact KeepsCtx.bind (hf x) fun _ => KeepsCtx.bind ih fun _ => KeepsCtx.pure _

macro "kc_step" : tactic => `(tactic| first
  | apply KeepsCtx.bind
  | exact KeepsCtx.pure _ | apply KeepsCtx.pure | apply KeepsCtx.throw | apply KeepsCtx.fail
  | apply KeepsCtx.get | apply KeepsCtx.ofExcept | apply KeepsCtx.codec
  | exact KeepsCtx.rd _ | exact KeepsCtx.op _ | exact KeepsCtx.reads _
  | apply KeepsCtx.forIn_list | apply KeepsCtx.forIn_arr | apply KeepsCtx.mapM
  | split
  | dsimp only
  | (refine fun _ => ?_)
  | assumption)

theorem kc_sysLookup (i : String) : KeepsCtx (sysLookup i) := by unfold sysLookup; repeat kc_step
theorem kc_liveOfSP (s p : ObjectId) : KeepsCtx (liveOfSP s p) := by unfold liveOfSP; repeat kc_step
theorem kc_liveOfP (p : ObjectId) : KeepsCtx (liveOfP p) := by unfold liveOfP; repeat kc_step
theorem kc_iriOf (x : ObjectId) : KeepsCtx (iriOf x) := by unfold iriOf; repeat kc_step
theorem kc_tagOf (x : ObjectId) (pos : Position) : KeepsCtx (tagOf x pos) := by unfold tagOf; repeat kc_step
theorem kc_originOk (x : ObjectId) : KeepsCtx (originOk x) := by unfold originOk; repeat kc_step
theorem kc_subjectTypeRows (x : ObjectId) : KeepsCtx (subjectTypeRows x) := by
  unfold subjectTypeRows; repeat (first | apply kc_sysLookup | apply kc_liveOfSP | kc_step)
theorem kc_tagsOf (x : List ObjectId) : KeepsCtx (tagsOf x) := by
  unfold tagsOf; repeat (first | apply kc_iriOf | kc_step)
theorem kc_subjectTypeViolations (x : ObjectId) (t : List Tag) : KeepsCtx (subjectTypeViolations x t) := by
  unfold subjectTypeViolations; repeat (first | apply kc_liveOfP | apply kc_tagOf | kc_step)
theorem kc_validateFlagRetraction (e : ObjectId) : KeepsCtx (validateFlagRetraction e) := by
  unfold validateFlagRetraction
  repeat (first | apply kc_sysLookup | apply kc_subjectTypeRows | apply kc_tagsOf | apply kc_subjectTypeViolations | kc_step)

theorem ctx_originOk (x : ObjectId) {ctx : TxCtx} {s : ModelStore} {a : Unit} {c : TxCtx}
    (h : erun (originOk x) ctx s = .ok (.ok (a, c), s)) : c = ctx := kc_originOk x ctx s a c s h
theorem ctx_validateFlagRetraction (x : ObjectId) {ctx : TxCtx} {s : ModelStore} {a : Unit} {c : TxCtx}
    (h : erun (validateFlagRetraction x) ctx s = .ok (.ok (a, c), s)) : c = ctx :=
  kc_validateFlagRetraction x ctx s a c s h

theorem ero_bind {α β : Type} {x : EngM α} (hx : ERO x) {f : α → EngM β} {ctx : TxCtx} {s : ModelStore}
    {r : β × TxCtx} {s' : ModelStore} (h : erun (x >>= f) ctx s = .ok (.ok r, s')) :
    ∃ a c, erun x ctx s = .ok (.ok (a, c), s) ∧ erun (f a) c s = .ok (.ok r, s') := by
  rw [erun_bind] at h
  cases hx' : erun x ctx s with
  | error e => rw [hx'] at h; cases h
  | ok p =>
    rcases p with ⟨q, s1⟩
    have := ERO.store hx hx'
    subst this
    rcases q with e | ⟨a, c⟩
    · rw [hx'] at h; cases h
    · rw [hx'] at h; exact ⟨a, c, rfl, h⟩

theorem erun_live (e : ObjectId) (ctx : TxCtx) (s : ModelStore) :
    erun (live e) ctx s = .ok (.ok ((s.current.triple e.raw).map (·.tRet.isNone), ctx), s) := by
  unfold live
  rw [erun_bind, erun_rd]
  rfl

/-- A retraction of `root` with `kind`: when the root is not live, nothing changes and the
result is `false`; otherwise the result is `true`, the cascade set (the now-view dependents
closure of the root, root first, without duplicates) has at most `max_cascade` members, and
exactly its members are retracted at the current transaction (`last_t + 1`), the root with
`kind` and the others with `cascade` for an explicit retraction and `kind` otherwise; every
other row, and everything else in the store, is unchanged. -/
theorem retractRoot_spec {s : ModelStore} (hb : Bounded s.current) {root : ObjectId} {kind : RetKind}
    {ctx ctx' : TxCtx} {b : Bool} {s' : ModelStore}
    (h : erun (retractRoot root kind) ctx s = .ok (.ok (b, ctx'), s')) :
    (b = false ∧ s' = s ∧ ¬ ∃ r ∈ s.current.triples, r.eid = root.raw ∧ r.tRet = none) ∨
    (b = true ∧ ∃ (lastT : Int64) (o : List Int64), s.committed.counter "last_t" = some lastT ∧
      o.Nodup ∧ o.head? = some root.raw ∧
      (∀ x, x ∈ o ↔ Relation.ReflTransGen (StandsOn s.current {}) x root.raw) ∧
      o.length ≤ ctx.opts.maxCascade ∧
      s' = { s with current := { s.current with
        triples := s.current.triples.map (retractSet o (lastT + 1) kind root.raw) } }) := by
  unfold retractRoot at h
  obtain ⟨_, c0, hc0, h⟩ := ero_bind (ero_originOk root) h
  obtain ⟨lv, c1, hlv, h⟩ := ero_bind (ero_live root) h
  rw [erun_live] at hlv
  cases hlv
  by_cases hl : ((s.current.triple root.raw).map (·.tRet.isNone) != some true) = true
  · rw [if_pos hl] at h
    simp only [erun_pure] at h
    cases h
    refine Or.inl ⟨rfl, rfl, ?_⟩
    rintro ⟨r, hr, he, hn⟩
    rw [← he, triple_of_mem hb.uniq hr] at hl
    simp [hn] at hl
  · rw [if_neg hl] at h
    have hlive : ∃ r ∈ s.current.triples, r.eid = root.raw ∧ r.tRet = none := by
      cases ht : s.current.triple root.raw with
      | none => rw [ht] at hl; simp at hl
      | some r =>
        rw [ht] at hl
        obtain ⟨hr, he⟩ := triple_some ht
        refine ⟨r, hr, he, ?_⟩
        cases hr' : r.tRet
        · rfl
        · simp [hr'] at hl
    obtain ⟨_, c2, hc2, h⟩ := ero_bind (ero_validateFlagRetraction root) h
    obtain ⟨r0, hr0, he0, hn0⟩ := hlive
    obtain ⟨o, hnd, hhd, hmem, hcs⟩ := cascadeSet_spec hb c2 (root := root) (List.mem_map.2 ⟨r0, hr0, he0⟩)
    rw [erun_bind, hcs] at h
    by_cases hlim : c2.opts.maxCascade < o.length
    · rw [if_pos hlim] at h; cases h
    · rw [if_neg hlim] at h
      simp only [] at h
      rw [erun_bind] at h
      cases hloop : erun (forIn (o.map (⟨·⟩ : Int64 → ObjectId)) true _) c2 s with
      | error x => rw [hloop] at h; cases h
      | ok p =>
        rcases p with ⟨q, s2⟩
        rcases q with x | ⟨u, c3⟩
        · rw [hloop] at h; cases h
        · rw [hloop] at h
          simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          have hall : ∀ e ∈ o, ∃ r ∈ s.current.triples, r.eid = e ∧ r.tRet = none := by
            intro e he
            rcases Relation.ReflTransGen.cases_head ((hmem e).1 he) with h' | ⟨c, hc, _⟩
            · exact ⟨r0, hr0, he0.trans h'.symm, hn0⟩
            · obtain ⟨r, hr, hre, ha, _⟩ := hc
              exact ⟨r, hr, hre, (admits_now r).1 ha⟩
          have hf : ∀ (e : ObjectId) (first : Bool) (c : TxCtx) (s : ModelStore) (st : ForInStep Bool)
              (c' : TxCtx) (s' : ModelStore), (s.current.triples.Pairwise fun a b => a.eid ≠ b.eid) →
              (∃ r ∈ s.current.triples, r.eid = e.raw ∧ r.tRet = none) →
              erun ((fun e first => EngM.retractRow e (if (first || kind != .explicit) = true then kind else .cascade) >>=
                fun _ => (pure (ForInStep.yield false) : EngM (ForInStep Bool))) e first) c s = .ok (.ok (st, c'), s') →
              st = .yield false ∧ ∃ lt, s.committed.counter "last_t" = some lt ∧
                s' = retractIn s e.raw (lt + 1) (if (first || kind != .explicit) = true then kind else .cascade).code := by
            intro e first c s st c' s' hu hl hr
            dsimp only at hr
            rw [erun_bind] at hr
            cases hrr : erun (EngM.retractRow e (if (first || kind != .explicit) = true then kind else .cascade)) c s with
            | error x => rw [hrr] at hr; cases hr
            | ok p =>
              rcases p with ⟨q, s1⟩
              rcases q with x | ⟨d, c1⟩
              · rw [hrr] at hr; cases hr
              · rw [hrr] at hr
                simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at hr
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
                obtain ⟨r, hr', he', hn'⟩ := hl
                exact ⟨rfl, retractRow_live hu hrr hr' he' hn'⟩
          obtain ⟨lt, hlt, hs2⟩ := loop_retract (kind := kind) (root := root.raw) hf o true c2 s u _ _ hnd
            hb.uniq hall (fun _ => hhd) (fun h => by cases h) hloop
          have hne : o ≠ [] := by intro h; rw [h] at hhd; cases hhd
          refine Or.inr ⟨rfl, lt, o, hlt hne, hnd, hhd, hmem, ?_, hs2⟩
          have e0 := ctx_originOk root hc0
          have e2 := ctx_validateFlagRetraction root hc2
          rw [e2, e0] at hlim
          omega

end Tiramemsu.Engine
