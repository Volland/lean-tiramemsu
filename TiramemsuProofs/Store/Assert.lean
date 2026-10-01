/-
Assert is idempotent. A successful assert either returns `Existing e`, where `e` is the
smallest eid of a live statement with the same subject, predicate and object whose interval
overlaps the requested one, and changes no statement row; or finds no such statement and
returns `New e`, appending exactly one live row `(e, s, p, o, valid)` at the current
transaction (other rows may only be retracted, by cardinality-one replacement). Asserting
the same statement twice in a row: the second assert returns `Existing` with the first's eid
and changes no row.
Requirement: memory-verbs / "Assert is idempotent".
-/
import TiramemsuProofs.Store.Effects
import TiramemsuProofs.Store.Interval
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec Tiramemsu.View EngM

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Peeling steps off an engine run -/

theorem light_peel {α β : Type} {x : EngM α} {f : α → EngM β} {s0 s : ModelStore} {ctx : TxCtx}
    {r : β × TxCtx} {s' : ModelStore} (hs : SameRows s0 s) (h : erun (x >>= f) ctx s = .ok (.ok r, s'))
    (hx : LightE x) :
    ∃ a c s1, erun x ctx s = .ok (.ok (a, c), s1) ∧ SameRows s0 s1 ∧ erun (f a) c s1 = .ok (.ok r, s') := by
  rw [erun_bind] at h
  cases h1 : erun x ctx s with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rcases p with ⟨q, s1⟩
    rcases q with e | ⟨a, c⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      have h2 := LightE.rows hx h1
      exact ⟨a, c, s1, rfl, ⟨h2.1.trans hs.1, h2.2.trans hs.2⟩, h⟩

theorem noIns_peel {α β : Type} {x : EngM α} {f : α → EngM β} {s : ModelStore} {ctx : TxCtx}
    {r : β × TxCtx} {s' : ModelStore} (h : erun (x >>= f) ctx s = .ok (.ok r, s')) (hx : NoInsE x) :
    ∃ a c s1, erun x ctx s = .ok (.ok (a, c), s1) ∧ NoInsRel s s1 ∧ erun (f a) c s1 = .ok (.ok r, s') := by
  rw [erun_bind] at h
  cases h1 : erun x ctx s with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rcases p with ⟨q, s1⟩
    rcases q with e | ⟨a, c⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      exact ⟨a, c, s1, rfl, NoInsE.rows hx h1, h⟩

/-! ## Candidates of an assert -/

/-- A live statement with the triple whose interval overlaps `v`. -/
def Cand (s p o : ObjectId) (v : Valid) (r : TripleRow) : Prop :=
  r.s = s.raw ∧ r.p = p.raw ∧ r.o = o.raw ∧ r.tRet = none ∧ Valid.overlaps ⟨r.vFrom, r.vTo⟩ v = true

/-- `e` is the smallest eid of a candidate. -/
def MinCand (st : ModelState) (s p o : ObjectId) (v : Valid) (e : Int64) : Prop :=
  ∃ r ∈ st.triples, Cand s p o v r ∧ r.eid = e ∧ ∀ r' ∈ st.triples, Cand s p o v r' → e.toInt ≤ r'.eid.toInt

theorem matches_liveSpo3 (a b c : Int64) (r : TripleRow) :
    ({ family := .liveSpo, pre := #[a, b, c] } : ScanSpec).matches r = true ↔
      r.s = a ∧ r.p = b ∧ r.o = c ∧ r.tRet = none := by
  simp [ScanSpec.matches, ScanSpec.prefixOk, ScanSpec.boundsOk, Family.rowFilter, Family.cols, Family.perm,
    Col.get, View.admits, TxSel.admits, ValidSel.admits, ScanSpec.boundCol, Option.isNone_iff_eq_none]
  tauto

theorem eidSorted_head_min {L : List TripleRow} (hs : EidSorted L) {x : TripleRow} (hx : L.head? = some x) :
    ∀ y ∈ L, x.eid.toInt ≤ y.eid.toInt := by
  cases L with
  | nil => cases hx
  | cons a L =>
    cases hx
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact le_refl _
    · exact le_of_lt ((List.pairwise_cons.1 hs).1 y hy)

/-- The overlap lookup of an assert: `none` when there is no candidate, otherwise the smallest
candidate eid; it reads only. -/
theorem findOverlapping_spec {st : ModelStore} (hu : Uniq st) (s p o : ObjectId) (v : Valid) (ctx : TxCtx) :
    ∃ res, erun (findOverlapping s p o v) ctx st = .ok (.ok (res, ctx), st) ∧
      ((res = none ∧ ∀ r ∈ st.current.triples, ¬ Cand s p o v r) ∨
       (∃ e, res = some ⟨e⟩ ∧ MinCand st.current s p o v e)) := by
  have hval : ({ family := .liveSpo, pre := #[s.raw, p.raw, o.raw] } : ScanSpec).valid = true := by
    simp [ScanSpec.valid, Family.maxPrefix, Family.isLive]
  set L := View.byEid ((st.current.scanList { family := .liveSpo, pre := #[s.raw, p.raw, o.raw] }).filter
    fun r => Valid.overlaps ⟨r.vFrom, r.vTo⟩ v) with hL
  have hmem : ∀ r, r ∈ L ↔ r ∈ st.current.triples ∧ Cand s p o v r := by
    intro r
    rw [hL, (byEid_perm _).mem_iff, List.mem_filter, mem_scanList_iff, matches_liveSpo3]
    unfold Cand; tauto
  have hsort : EidSorted L := byEid_sorted
    ((scanList_pairwise_eid _ hu).sublist List.filter_sublist)
  refine ⟨L.head?.map (⟨·.eid⟩), ?_, ?_⟩
  · unfold findOverlapping
    rw [erun_bind, erun_rd, ROp.model_scan, if_pos hval]
    simp only []
    rw [erun_pure, hL]
    simp [EngM.byEid]
  · cases hh : L.head? with
    | none =>
      refine Or.inl ⟨rfl, fun r hr hc => ?_⟩
      have := (hmem r).2 ⟨hr, hc⟩
      rw [List.head?_eq_none_iff.1 hh] at this; cases this
    | some x =>
      have hx := (hmem x).1 (List.mem_of_head? hh)
      refine Or.inr ⟨x.eid, rfl, x, hx.1, hx.2, rfl, fun r' hr' hc' => ?_⟩
      exact eidSorted_head_min hsort hh r' ((hmem r').2 ⟨hr', hc'⟩)

/-! ## The insert step -/

/-- The row an insert of `(eid, s, p, o, valid)` at transaction `t` stores. -/
def newRowAt (eid s p o : ObjectId) (valid : Valid) (t : Int64) : TripleRow :=
  { eid := eid.raw, s := s.raw, p := p.raw, o := o.raw, tAdd := t, vFrom := valid.vFrom, vTo := valid.vTo }

theorem erun_insert {nr : NewRow} {c c' : TxCtx} {st st' : ModelStore} {u : Unit}
    (h : erun (EngM.op (.insert nr)) c st = .ok (.ok (u, c'), st')) :
    ∃ lastT, st.committed.counter "last_t" = some lastT ∧
      st.current.triples.any (·.eid == nr.eid) = false ∧ c' = c ∧
      st' = { st with current := { st.current with triples := st.current.triples ++
        [{ eid := nr.eid, s := nr.s, p := nr.p, o := nr.o, tAdd := lastT + 1, vFrom := nr.vFrom, vTo := nr.vTo }] } } := by
  rw [erun_op] at h
  cases hi : (Op.run (.insert nr) : ModelM Unit) st with
  | error e => rw [hi] at h; cases h
  | ok q =>
    rcases q with ⟨u1, s1⟩
    rw [hi] at h
    cases h
    obtain ⟨lastT, _, _, hlt, _, _, _, _, _, _, hany, rfl⟩ := insert_spec (r := nr) hi
    exact ⟨lastT, hlt, hany, rfl, rfl⟩

theorem insertRow_spec {eid sx px ox : ObjectId} {valid : Valid} {c c' : TxCtx} {st st' : ModelStore} {u : Unit}
    (h : erun (insertRow eid sx px ox valid) c st = .ok (.ok (u, c'), st')) :
    ∃ lastT, st.committed.counter "last_t" = some lastT ∧
      st.current.triples.any (·.eid == eid.raw) = false ∧ st'.committed = st.committed ∧
      st'.current.triples = st.current.triples ++ [newRowAt eid sx px ox valid (lastT + 1)] := by
  unfold insertRow at h
  rw [erun_bind] at h
  split at h
  · rename_i a c1 s1 hi
    obtain ⟨lastT, hlt, hany, -, rfl⟩ := erun_insert hi
    have hl := LightE.rows ?_ h
    · refine ⟨lastT, hlt, hany, hl.2, ?_⟩
      rw [hl.1]; rfl
    · repeat fp_step
  · cases h
  · cases h

theorem SameRows.refl (s : ModelStore) : SameRows s s := ⟨rfl, rfl⟩

theorem erun_fail_bind {α β : Type} (e : Error) (f : α → EngM β) (ctx : TxCtx) (s : ModelStore) :
    erun (EngM.fail e >>= f) ctx s = .ok (.error e, s) := by
  rw [erun_bind, erun_fail]

/-! ## The pipeline with idempotency -/

/-- The conclusion about an idempotent write. -/
def WriteOutcome (s0 s' : ModelStore) (sx px ox : ObjectId) (valid : Valid) (r : Asserted) : Prop :=
  (∃ e, r = .existing ⟨e⟩ ∧ SameRows s0 s' ∧ MinCand s0.current sx px ox valid e) ∨
  (∃ e : ObjectId, r = .new e ∧ (∀ x ∈ s0.current.triples, ¬ Cand sx px ox valid x) ∧
    ∃ lastT pre, s0.committed.counter "last_t" = some lastT ∧
      List.Forall₂ (RetStep (lastT + 1)) s0.current.triples pre ∧
      pre.any (·.eid == e.raw) = false ∧ s'.committed = s0.committed ∧
      s'.current.triples = pre ++ [newRowAt e sx px ox valid (lastT + 1)])

theorem write_core {s0 s s' : ModelStore} (hu : Uniq s0) (hs : SameRows s0 s) {sx px ox : ObjectId}
    {valid : Valid} {b : Bool} {c c' : TxCtx} {r : Asserted}
    (h : erun (findOverlapping sx px ox valid >>= fun d => match d with
      | some e => pure (Asserted.existing e)
      | _ => (uniqueAndCardinality sx px ox valid b >>= fun _ => allocEid >>= fun eid =>
          if (sx == eid || ox == eid) = true then
            ((EngM.fail (.selfReference eid) : EngM Unit) >>= fun _ => insertRow eid sx px ox valid >>= fun _ =>
              pure (Asserted.new eid))
          else (insertRow eid sx px ox valid >>= fun _ => pure (Asserted.new eid)))) c s =
        .ok (.ok (r, c'), s')) :
    WriteOutcome s0 s' sx px ox valid r := by
  have hu' : Uniq s := by unfold Uniq; rw [hs.1]; exact hu
  obtain ⟨fo, c5, s5, hfo, -, h⟩ := light_peel hs h (light_findOverlapping _ _ _ _)
  obtain ⟨res, hres, hspec⟩ := findOverlapping_spec hu' sx px ox valid c
  rw [hres] at hfo
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfo
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfo
  rcases hspec with ⟨rfl, hnone⟩ | ⟨e, rfl, hmin⟩
  · simp only [] at h
    obtain ⟨_, c6, s6, -, hrel, h⟩ := noIns_peel h (noIns_uniqueAndCardinality _ _ _ _ _)
    obtain ⟨eid, c7, s7, -, hs7, h⟩ := light_peel (SameRows.refl s6) h light_allocEid
    split at h
    · rw [erun_fail_bind] at h; cases h
    · rw [erun_bind] at h
      split at h
      · rename_i u c8 s8 hins
        obtain ⟨lastT, hlt, hany, hc8, hrows⟩ := insertRow_spec hins
        simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨⟨hc6, hf⟩, -⟩ := hrel hu'
        have hcom : s7.committed = s0.committed := hs7.2.trans (hc6.trans hs.2)
        have ht : tOf s = lastT + 1 := by
          unfold tOf; rw [hs.2, ← hcom, hlt]; rfl
        refine Or.inr ⟨eid, rfl, fun x hx => hnone x (by rw [hs.1]; exact hx), lastT, s6.current.triples,
          by rw [← hcom]; exact hlt, ?_, by rw [← hs7.1]; exact hany, hc8.trans hcom, by rw [hrows, hs7.1]⟩
        rw [← ht, ← hs.1]; exact hf
      · cases h
      · cases h
  · simp only [] at h
    simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine Or.inl ⟨e, rfl, hs, ?_⟩
    obtain ⟨x, hx, hc, he, hm⟩ := hmin
    exact ⟨x, by rw [← hs.1]; exact hx, hc, he, fun r' hr' hc' => hm r' (by rw [hs.1]; exact hr') hc'⟩

/-- The idempotent write: `Existing e` with `e` the smallest candidate and no row changed, or no
candidate and exactly one new live row appended (other rows unchanged or retracted at the
current transaction); a `New` result also means the interval was valid. -/
theorem write_spec {s0 s' : ModelStore} (hu : Uniq s0) {sx px ox : ObjectId} {valid : Valid} {w : Writer}
    {ctx c' : TxCtx} {r : Asserted} (h : erun (write sx px ox valid true w) ctx s0 = .ok (.ok (r, c'), s')) :
    WriteOutcome s0 s' sx px ox valid r ∧ Valid.check valid = .ok () := by
  unfold write at h
  dsimp only at h
  obtain ⟨_, _, _, -, hs, h⟩ := light_peel (SameRows.refl s0) h (light_checkPositions _ _ _)
  obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_iriOf _)
  split at h
  · obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_tagOf _ _)
    obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (EOps.ofExcept _)
    obtain ⟨vu, _, _, hvc, hs, h⟩ := light_peel hs h (EOps.ofExcept _)
    have hvalid : Valid.check valid = .ok () := by
      cases hv : Valid.check valid with
      | error e => rw [hv] at hvc; simp [EngM.ofExcept] at hvc
      | ok u => rfl
    refine ⟨?_, hvalid⟩
    split at h
    · obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_validateFlag _ _ _ _)
      obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_validateSchemaChange _ _ _ _)
      rw [if_pos rfl] at h
      exact write_core hu hs h
    · obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_checkValueType _ _)
      obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_checkSubjectType _ _)
      rw [if_pos rfl] at h
      exact write_core hu hs h
  · obtain ⟨vu, _, _, hvc, hs, h⟩ := light_peel hs h (EOps.ofExcept _)
    have hvalid : Valid.check valid = .ok () := by
      cases hv : Valid.check valid with
      | error e => rw [hv] at hvc; simp [EngM.ofExcept] at hvc
      | ok u => rfl
    refine ⟨?_, hvalid⟩
    split at h
    · obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_validateFlag _ _ _ _)
      obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_validateSchemaChange _ _ _ _)
      rw [if_pos rfl] at h
      exact write_core hu hs h
    · obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_checkValueType _ _)
      obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_checkSubjectType _ _)
      rw [if_pos rfl] at h
      exact write_core hu hs h

/-! ## Assert -/

theorem overlaps_self {v : Valid} (h : v.nonempty = true) : Valid.overlaps v v = true := by
  rcases v with ⟨f, t⟩
  cases f <;> cases t <;> simp_all [Valid.overlaps, Valid.nonempty]

theorem erun_report (f : TxReport → TxReport) (ctx : TxCtx) (s : ModelStore) :
    erun (EngM.report f) ctx s = .ok (.ok ((), { ctx with report := f ctx.report }), s) := rfl

theorem idIn_val {x y : ObjectId} {c c' : TxCtx} {st st' : ModelStore}
    (h : erun (idIn x) c st = .ok (.ok (y, c'), st')) : y = x ∧ SameRows st st' := by
  unfold idIn at h
  obtain ⟨_, _, _, -, hs, h⟩ := light_peel (SameRows.refl st) h (light_tagOf _ _)
  obtain ⟨_, _, _, -, hs, h⟩ := light_peel hs h (light_originOk _)
  simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  exact ⟨rfl, hs⟩

theorem WriteOutcome.of_same {s0 s1 s' : ModelStore} (hs : SameRows s0 s1) {sx px ox : ObjectId} {valid : Valid}
    {r : Asserted} (h : WriteOutcome s1 s' sx px ox valid r) : WriteOutcome s0 s' sx px ox valid r := by
  have e1 : s1.current.triples = s0.current.triples := hs.1
  have e2 : s1.committed = s0.committed := hs.2
  rcases h with ⟨e, rfl, hs', hmin⟩ | ⟨e, rfl, hnone, lastT, pre, hlt, hf, hany, hc, hrows⟩
  · refine Or.inl ⟨e, rfl, ⟨hs'.1.trans e1, hs'.2.trans e2⟩, ?_⟩
    unfold MinCand at hmin ⊢; rw [← e1]; exact hmin
  · refine Or.inr ⟨e, rfl, by rw [← e1]; exact hnone, lastT, pre, by rw [← e2]; exact hlt, by rw [← e1]; exact hf,
      hany, hc.trans e2, hrows⟩

/-- An assert (returning on an existing match, the default) either returns `Existing e` with `e`
the smallest eid of a live statement with the same triple and an overlapping interval and
changes no row, or finds none and returns `New e`, appending exactly the live row
`(e, s, p, o, valid)` at the current transaction while other rows stay or are retracted then. -/
theorem assert_spec {s0 s' : ModelStore} (hu : Uniq s0) {sx px ox : ObjectId} {opts : AssertOpts}
    (hopt : opts.onExisting ≠ .confirm) {ctx c' : TxCtx} {r : Asserted}
    (h : erun (assertStmt sx px ox opts) ctx s0 = .ok (.ok (r, c'), s')) :
    WriteOutcome s0 s' sx px ox opts.valid r ∧ Valid.check opts.valid = .ok () := by
  unfold assertStmt at h
  obtain ⟨y1, _, s1, h1, -, h⟩ := light_peel (x := idIn sx) (SameRows.refl s0) h (light_idIn _)
  obtain ⟨hy1, hs1⟩ := idIn_val h1
  rw [hy1] at h
  obtain ⟨y2, _, s2, h2, -, h⟩ := light_peel (x := idIn px) (SameRows.refl s1) h (light_idIn _)
  obtain ⟨hy2, hs2⟩ := idIn_val h2
  rw [hy2] at h
  obtain ⟨y3, _, s3, h3, -, h⟩ := light_peel (x := idIn ox) (SameRows.refl s2) h (light_idIn _)
  obtain ⟨hy3, hs3⟩ := idIn_val h3
  rw [hy3] at h
  have hs : SameRows s0 s3 := ⟨hs3.1.trans (hs2.1.trans hs1.1), hs3.2.trans (hs2.2.trans hs1.2)⟩
  have hu3 : Uniq s3 := by unfold Uniq; rw [hs.1]; exact hu
  rw [erun_bind] at h
  split at h
  · rename_i r1 c4 s4 hw
    obtain ⟨hout, hvalid⟩ := write_spec hu3 hw
    refine ⟨?_, hvalid⟩
    have hout0 := WriteOutcome.of_same hs hout
    -- what follows the write changes no row
    have hl : SameRows s4 s' := by
      refine LightE.rows (x := (fun r => _) r1) ?_ h
      dsimp only
      split
      · have : (opts.onExisting == .confirm) = false := by simpa using hopt
        simp only [this, Bool.false_eq_true, if_false]
        repeat fp_step
      · repeat fp_step
    have hres : r = r1 := by
      revert h
      split
      · have : (opts.onExisting == .confirm) = false := by simpa using hopt
        simp only [this, Bool.false_eq_true, if_false]
        intro h
        rw [erun_bind, erun_report] at h
        simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact h.1.1.symm
      · intro h; simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1.1.symm
    subst hres
    rcases hout0 with ⟨e, rfl, hs', hmin⟩ | ⟨e, rfl, hnone, lastT, pre, hlt, hf, hany, hc, hrows⟩
    · exact Or.inl ⟨e, rfl, ⟨hl.1.trans hs'.1, hl.2.trans hs'.2⟩, hmin⟩
    · exact Or.inr ⟨e, rfl, hnone, lastT, pre, hlt, hf, hany, hl.2.trans hc, hl.1.trans hrows⟩
  · cases h
  · cases h

theorem minCand_unique {st : ModelState} {sx px ox : ObjectId} {v : Valid} {e1 e2 : Int64}
    (h1 : MinCand st sx px ox v e1) (h2 : MinCand st sx px ox v e2) : e1 = e2 := by
  obtain ⟨r1, hr1, hc1, rfl, hm1⟩ := h1
  obtain ⟨r2, hr2, hc2, rfl, hm2⟩ := h2
  have := hm1 r2 hr2 hc2
  have := hm2 r1 hr1 hc1
  exact Int64.toInt_inj.1 (by omega)

theorem WriteOutcome.uniq {s0 s' : ModelStore} (hu : Uniq s0) {sx px ox : ObjectId} {valid : Valid} {r : Asserted}
    (h : WriteOutcome s0 s' sx px ox valid r) : Uniq s' := by
  rcases h with ⟨e, rfl, hs, -⟩ | ⟨e, rfl, -, lastT, pre, -, hf, hany, -, hrows⟩
  · unfold Uniq; rw [hs.1]; exact hu
  · unfold Uniq; rw [hrows]
    have hpre : pre.Pairwise fun a b => a.eid ≠ b.eid := uniq_of_eids (forall₂_retStep_eid hf) hu
    refine List.pairwise_append.2 ⟨hpre, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    intro he
    have : pre.any (·.eid == e.raw) = true := List.any_eq_true.2 ⟨a, ha, by simp [he, newRowAt]⟩
    rw [hany] at this; cases this

/-- Assert is idempotent: asserting the same statement twice in a row, the second assert
returns `Existing` with the first's eid and changes no statement row. -/
theorem assert_twice {s0 s1 s2 : ModelStore} (hu : Uniq s0) {sx px ox : ObjectId} {opts : AssertOpts}
    (hopt : opts.onExisting ≠ .confirm) {ctx c1 c2 : TxCtx} {r1 r2 : Asserted}
    (h1 : erun (assertStmt sx px ox opts) ctx s0 = .ok (.ok (r1, c1), s1))
    (h2 : erun (assertStmt sx px ox opts) c1 s1 = .ok (.ok (r2, c2), s2)) :
    r2 = .existing r1.eid ∧ SameRows s1 s2 := by
  obtain ⟨o1, hv⟩ := assert_spec hu hopt h1
  have hu1 := o1.uniq hu
  obtain ⟨o2, -⟩ := assert_spec hu1 hopt h2
  rcases o1 with ⟨e1, rfl, hs1, hmin1⟩ | ⟨e1, rfl, hnone1, lastT, pre, hlt, hf, hany, hc, hrows⟩
  · have hmin1' : MinCand s1.current sx px ox opts.valid e1 := by unfold MinCand; rw [hs1.1]; exact hmin1
    rcases o2 with ⟨e2, rfl, hs2, hmin2⟩ | ⟨e2, rfl, hnone2, -⟩
    · rw [minCand_unique hmin1' hmin2]; exact ⟨rfl, hs2⟩
    · obtain ⟨x, hx, hcx, -⟩ := hmin1'
      exact absurd hcx (hnone2 x hx)
  · -- the new row is the only candidate
    have hne : opts.valid.nonempty = true := (Valid.check_ok_iff _).1 hv
    have hcand : Cand sx px ox opts.valid (newRowAt e1 sx px ox opts.valid (lastT + 1)) :=
      ⟨rfl, rfl, rfl, rfl, overlaps_self hne⟩
    have hmem : newRowAt e1 sx px ox opts.valid (lastT + 1) ∈ s1.current.triples := by
      rw [hrows]; exact List.mem_append_right _ (List.mem_singleton_self _)
    have honly : ∀ x ∈ s1.current.triples, Cand sx px ox opts.valid x →
        x = newRowAt e1 sx px ox opts.valid (lastT + 1) := by
      intro x hx hcx
      rw [hrows] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exfalso
        obtain ⟨y, hy, hrel⟩ := forall₂_mem_right hf x hx
        rcases hrel with rfl | ⟨_, k, rfl⟩
        · exact hnone1 x hy hcx
        · exact absurd hcx.2.2.2.1 (by simp)
      · exact List.mem_singleton.1 hx
    rcases o2 with ⟨e2, rfl, hs2, hmin2⟩ | ⟨e2, rfl, hnone2, -⟩
    · obtain ⟨x, hx, hcx, hxe, -⟩ := hmin2
      have := honly x hx hcx
      subst this
      refine ⟨?_, hs2⟩
      rw [← hxe]; rfl
    · exact absurd hcand (hnone2 _ hmem)

end Tiramemsu.Engine
