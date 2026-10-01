/-
Properties of `ModelStore`.
Requirements: store-contract / "The model store is exact and ordered" and
"Model writes are atomic and never overwrite".
-/
import Tiramemsu.Store.Model
import TiramemsuProofs.Store.Order

namespace Tiramemsu.Store

--# @lat: [[verification#Proven Store Properties]]

/-! ## Scans: exactness, duplicate-freedom, order, validity, fold -/

/-- A scan returns exactly the rows of the state that match it. -/
theorem scanList_mem {st : ModelState} {sp : ScanSpec} {r : TripleRow} :
    r ∈ st.scanList sp ↔ r ∈ st.triples ∧ sp.Matches r := by
  simp [ModelState.scanList, ScanSpec.Matches]

theorem scanList_perm (st : ModelState) (sp : ScanSpec) :
    (st.scanList sp).Perm (st.triples.filter sp.matches) :=
  List.mergeSort_perm _ _

theorem scanList_pairwise_eid {st : ModelState} (sp : ScanSpec) (hwf : st.WF) :
    (st.scanList sp).Pairwise fun a b => a.eid ≠ b.eid :=
  ((scanList_perm st sp).pairwise_iff fun h => Ne.symm h).2 (hwf.filter _)

/-- On a well-formed state, a scan is strictly increasing in the family's key order. -/
theorem scanList_sorted {st : ModelState} (sp : ScanSpec) (hwf : st.WF) :
    (st.scanList sp).Pairwise (keyLt sp.family) := by
  have h₁ : (st.scanList sp).Pairwise fun a b => keyLe sp.family a b = true :=
    List.pairwise_mergeSort (keyLe_trans _) (keyLe_total _) _
  exact (h₁.and (scanList_pairwise_eid sp hwf)).imp fun ⟨h, h'⟩ => keyLt_of_keyLe _ h h'

/-- On a well-formed state, a scan returns each row once. -/
theorem scanList_nodup {st : ModelState} (sp : ScanSpec) (hwf : st.WF) :
    (st.scanList sp).Nodup :=
  (scanList_sorted sp hwf).imp fun h e => by subst e; exact keyLt_irrefl _ _ h

/-- A valid scan succeeds with the ordered rows. -/
theorem scanList?_valid {st : ModelState} {sp : ScanSpec} (hv : sp.Valid) :
    st.scanList? sp = .ok (st.scanList sp) := by
  simp [ModelState.scanList?, show sp.valid = true from hv]

/-- An invalid scan fails with an invalid-scan error. -/
theorem scan_invalid {st : ModelState} {sp : ScanSpec} (hv : ¬ sp.Valid) :
    st.scanList? sp = .error .invalidScan := by
  simp [ModelState.scanList?, show sp.valid = false by simpa [ScanSpec.Valid] using hv]

/-- The monadic scan of the model is the ordered fold over the scan's rows. -/
theorem scan_fold {β : Type} (s : ModelStore) {sp : ScanSpec} (hv : sp.Valid) (init : β)
    (f : β → TripleRow → ModelM (ForInStep β)) :
    (ReadStore.scan sp init f : ModelM β) s = foldWithExit (s.current.scanList sp) init f s := by
  show (s.current.scanM sp init f) s = _
  simp [ModelState.scanM, scanList?_valid hv]

/-- An invalid scan of the model fails before calling the callback. -/
theorem scan_fold_invalid {β : Type} (s : ModelStore) {sp : ScanSpec} (hv : ¬ sp.Valid)
    (init : β) (f : β → TripleRow → ModelM (ForInStep β)) :
    (ReadStore.scan sp init f : ModelM β) s = .error .invalidScan := by
  show (s.current.scanM sp init f) s = _
  simp [ModelState.scanM, scan_invalid hv]
  rfl

/-! ## Well-formedness of every operation -/

/-- Every state of the store (committed, current, savepoints) is well-formed. -/
def ModelStore.WF (s : ModelStore) : Prop :=
  s.committed.WF ∧ s.current.WF ∧ ∀ p ∈ s.sps, p.2.WF

theorem retractRow_eid (e t k : Int64) (x : TripleRow) : (retractRow e t k x).eid = x.eid := by
  unfold retractRow; split <;> rfl

theorem triple_eq_some {st : ModelState} {e : Int64} {r : TripleRow} (h : st.triple e = some r) :
    r ∈ st.triples ∧ r.eid = e := by
  unfold ModelState.triple at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- A data write is its data step on the current state, inside a transaction. -/
theorem run_data {op : WriteOp} (hd : op.isData = true) (s : ModelStore) :
    op.run s = if s.inTx then (op.step s.current).map (fun c => { s with current := c })
      else .error (.misuse "write outside a transaction") := by
  cases op <;> simp [WriteOp.isData] at hd <;>
  · simp only [WriteOp.run]
    split
    · split <;> simp_all [Except.map]
    · rfl

theorem run_data_ok {op : WriteOp} (hd : op.isData = true) {s s' : ModelStore}
    (h : op.run s = .ok s') : s.inTx = true ∧ ∃ c, op.step s.current = .ok c ∧ s' = { s with current := c } := by
  rw [run_data hd] at h
  by_cases htx : s.inTx = true
  · simp only [htx, ↓reduceIte] at h
    cases hs : op.step s.current with
    | error e => rw [hs] at h; cases h
    | ok c =>
      rw [hs] at h; cases h
      refine ⟨htx, c, rfl, ?_⟩
      cases s; simp_all
  · simp [htx] at h

theorem insertTriple_ok {r : TripleRow} {st c : ModelState} (h : st.insertTriple r = .ok c) :
    st.triples.any (·.eid == r.eid) = false ∧ c = { st with triples := st.triples ++ [r] } := by
  unfold ModelState.insertTriple at h
  by_cases hany : st.triples.any (·.eid == r.eid) = true
  · simp [hany] at h
  · simp only [hany] at h
    cases h
    exact ⟨by simpa using hany, rfl⟩

theorem retract_ok {e t k : Int64} {st c : ModelState} (h : st.retract e t k = .ok c) :
    (∃ r, st.triple e = some r ∧ r.tRet = none) ∧
      c = { st with triples := st.triples.map (retractRow e t k) } := by
  unfold ModelState.retract at h
  cases hr : st.triple e with
  | none => rw [hr] at h; cases h
  | some r =>
    rw [hr] at h
    by_cases hret : r.tRet.isSome = true
    · simp [hret] at h
    · simp only [hret] at h
      cases h
      exact ⟨⟨r, rfl, by simpa using hret⟩, rfl⟩

theorem insertTerm_ok {r : TermRow} {st c : ModelState} (h : st.insertTerm r = .ok c) :
    c = { st with terms := st.terms ++ [{ r with num := normalizeNum r.num }] } := by
  unfold ModelState.insertTerm at h
  by_cases h₁ : st.terms.any (·.id == r.id) = true
  · simp [h₁] at h
  · by_cases h₂ : st.terms.any (termKeyEq { r with num := normalizeNum r.num }) = true
    · simp only [h₁, h₂, ↓reduceIte] at h; cases h
    · simp only [h₁, h₂] at h
      cases h
      rfl

theorem insertTx_ok {r : TxRow} {st c : ModelState} (h : st.insertTx r = .ok c) :
    c = { st with txs := st.txs ++ [r] } := by
  unfold ModelState.insertTx at h
  by_cases h₁ : st.txs.any (·.t == r.t) = true
  · simp [h₁] at h
  · by_cases h₂ : st.txs.any (·.instant == r.instant) = true
    · simp only [h₁, h₂, ↓reduceIte] at h; cases h
    · simp only [h₁, h₂] at h
      cases h
      rfl

theorem step_wf {op : WriteOp} {st st' : ModelState} (h : op.step st = .ok st') (hwf : st.WF) :
    st'.WF := by
  cases op with
  | insertTriple r =>
    obtain ⟨hany, rfl⟩ := insertTriple_ok h
    simp only [ModelState.WF, List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
      true_and]
    refine ⟨hwf, fun a ha b hb => ?_⟩
    subst hb
    intro e
    have : st.triples.any (·.eid == b.eid) = true := List.any_eq_true.2 ⟨a, ha, by simp [e]⟩
    rw [this] at hany; cases hany
  | retract e t k =>
    obtain ⟨_, rfl⟩ := retract_ok h
    simp only [ModelState.WF, List.pairwise_map, retractRow_eid]
    exact hwf
  | insertTerm r => rw [insertTerm_ok h]; exact hwf
  | insertTx r => rw [insertTx_ok h]; exact hwf
  | setCounter => simp only [WriteOp.step, ModelState.setCounter, Except.ok.injEq] at h; subst h; exact hwf
  | volatilePut => simp only [WriteOp.step, ModelState.volatilePut, Except.ok.injEq] at h; subst h; exact hwf
  | volatileDel => simp only [WriteOp.step, ModelState.volatileDel, Except.ok.injEq] at h; subst h; exact hwf
  | addPredMulti => simp only [WriteOp.step, ModelState.addPredMulti, Except.ok.injEq] at h; subst h; exact hwf
  | _ => simp only [WriteOp.step, Except.ok.injEq] at h; subst h; exact hwf

theorem spRollback_spec {n : String} :
    ∀ {l : List (String × ModelState)} {c : ModelState} {l' : List (String × ModelState)},
      spRollback n l = some (c, l') → (n, c) ∈ l ∧ l'.IsSuffix l ∧ l'.head? = some (n, c)
  | [], _, _, h => by simp [spRollback] at h
  | (m, d) :: rest, c, l', h => by
    simp only [spRollback] at h
    split at h
    · rename_i hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : m = n := by simpa using hm
      subst this
      exact ⟨List.mem_cons_self .., List.suffix_refl _, rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := spRollback_spec h
      exact ⟨List.mem_cons_of_mem _ h₁, h₂.trans (List.suffix_cons _ _), h₃⟩

theorem spRelease_suffix {n : String} :
    ∀ {l l' : List (String × ModelState)}, spRelease n l = some l' → l'.IsSuffix l ∧ l'.length < l.length
  | [], _, h => by simp [spRelease] at h
  | (m, d) :: rest, l', h => by
    simp only [spRelease] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨List.suffix_cons _ _, by simp⟩
    · obtain ⟨h₁, h₂⟩ := spRelease_suffix h
      exact ⟨h₁.trans (List.suffix_cons _ _), by simp; omega⟩

/-- Every operation preserves uniqueness of statement ids in every state of the store. -/
theorem op_wf (op : WriteOp) {s s' : ModelStore} (hwf : s.WF) (h : op.run s = .ok s') : s'.WF := by
  obtain ⟨hc, hcur, hsp⟩ := hwf
  cases op with
  | begin =>
    simp only [WriteOp.run] at h; split at h
    · cases h
    · cases h; exact ⟨hc, hc, by simp⟩
  | commit =>
    simp only [WriteOp.run] at h; split at h
    · cases h; exact ⟨hcur, hcur, by simp⟩
    · cases h
  | rollback =>
    simp only [WriteOp.run] at h; split at h
    · cases h; exact ⟨hc, hc, by simp⟩
    · cases h
  | savepoint n =>
    simp only [WriteOp.run] at h; split at h
    · cases h
      refine ⟨hc, hcur, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨hcur, hsp⟩
    · cases h
  | rollbackTo n =>
    simp only [WriteOp.run] at h; split at h
    · split at h
      · rename_i c sps hr
        cases h
        obtain ⟨h₁, h₂, _⟩ := spRollback_spec hr
        exact ⟨hc, hsp _ h₁, fun p hp => hsp p (h₂.subset hp)⟩
      · cases h
    · cases h
  | release n =>
    simp only [WriteOp.run] at h; split at h
    · split at h
      · rename_i sps hr
        cases h
        exact ⟨hc, hcur, fun p hp => hsp p ((spRelease_suffix hr).1.subset hp)⟩
      · cases h
    · cases h
  | insertTriple r | retract e t k | insertTerm r | insertTx r | setCounter n v | volatilePut r
  | volatileDel a b | addPredMulti p =>
    obtain ⟨_, c, hstep, rfl⟩ := run_data_ok rfl h
    exact ⟨hc, step_wf hstep hcur, hsp⟩

/-! ## Failure leaves the state unchanged -/

/-- A failing operation inside `tryCatch` leaves the store exactly as it was. -/
theorem op_error_unchanged (op : WriteOp) {s : ModelStore} {e : StoreError}
    (h : op.run s = .error e) :
    (tryCatch op.exec (fun _ => pure ()) : ModelM Unit) s = .ok ((), s) := by
  show tryCatchThe StoreError (op.exec s) (fun e => (pure () : ModelM Unit) s) = _
  simp [WriteOp.exec, h]
  rfl

/-- A data write outside a transaction is misuse. -/
theorem write_outside_tx (op : WriteOp) {s : ModelStore} (hd : op.isData = true)
    (h : s.inTx = false) : ∃ w, op.run s = .error (.misuse w) := by
  cases op <;> simp [WriteOp.isData] at hd <;> simp [WriteOp.run, h]

/-- A nested begin is misuse. -/
theorem begin_nested {s : ModelStore} (h : s.inTx = true) :
    ∃ w, WriteOp.begin.run s = .error (.misuse w) := by
  simp [WriteOp.run, h]

/-! ## Appends never overwrite -/

/-- A successful triple append keeps every row and adds exactly the new one, whose id was free. -/
theorem insertTriple_spec {r : TripleRow} {s s' : ModelStore}
    (h : (WriteOp.insertTriple r).run s = .ok s') :
    s'.current = { s.current with triples := s.current.triples ++ [r] } ∧
      (∀ x ∈ s.current.triples, x.eid ≠ r.eid) ∧ s'.committed = s.committed ∧ s'.sps = s.sps := by
  obtain ⟨_, c, hstep, rfl⟩ := run_data_ok rfl h
  obtain ⟨hany, rfl⟩ := insertTriple_ok hstep
  refine ⟨rfl, fun x hx e => ?_, rfl, rfl⟩
  have : s.current.triples.any (·.eid == r.eid) = true := List.any_eq_true.2 ⟨x, hx, by simp [e]⟩
  rw [this] at hany; cases hany

/-- Appending a triple whose id exists (live or retracted) fails with `idReused`. -/
theorem insertTriple_reused {r x : TripleRow} {s : ModelStore} (htx : s.inTx = true)
    (hx : x ∈ s.current.triples) (he : x.eid = r.eid) :
    (WriteOp.insertTriple r).run s = .error (.violation .idReused) := by
  have : s.current.triples.any (·.eid == r.eid) = true :=
    List.any_eq_true.2 ⟨x, hx, by simp [he]⟩
  simp [WriteOp.run, WriteOp.step, ModelState.insertTriple, htx, this]

/-- A successful term append adds exactly the normalized row. -/
theorem insertTerm_spec {r : TermRow} {s s' : ModelStore}
    (h : (WriteOp.insertTerm r).run s = .ok s') :
    s'.current = { s.current with terms := s.current.terms ++ [{ r with num := normalizeNum r.num }] } ∧
      s'.committed = s.committed ∧ s'.sps = s.sps := by
  obtain ⟨_, c, hstep, rfl⟩ := run_data_ok rfl h
  exact ⟨insertTerm_ok hstep, rfl, rfl⟩

/-- A successful transaction append adds exactly the new row. -/
theorem insertTx_spec {r : TxRow} {s s' : ModelStore}
    (h : (WriteOp.insertTx r).run s = .ok s') :
    s'.current = { s.current with txs := s.current.txs ++ [r] } ∧
      s'.committed = s.committed ∧ s'.sps = s.sps := by
  obtain ⟨_, c, hstep, rfl⟩ := run_data_ok rfl h
  exact ⟨insertTx_ok hstep, rfl, rfl⟩

/-- Old rows are kept by every append. -/
theorem insert_no_loss {r : TripleRow} {s s' : ModelStore}
    (h : (WriteOp.insertTriple r).run s = .ok s') :
    (∀ x ∈ s.current.triples, x ∈ s'.current.triples) ∧
      s'.current.triples.length = s.current.triples.length + 1 := by
  rw [(insertTriple_spec h).1]
  exact ⟨fun x hx => List.mem_append_left _ hx, by simp⟩

/-! ## The single retraction update -/

/-- Retraction changes only `t_ret` and `ret_kind` of the rows with that id. -/
theorem retractRow_spec (e t k : Int64) (x : TripleRow) :
    (retractRow e t k x).eid = x.eid ∧ (retractRow e t k x).s = x.s ∧
    (retractRow e t k x).p = x.p ∧ (retractRow e t k x).o = x.o ∧
    (retractRow e t k x).tAdd = x.tAdd ∧ (retractRow e t k x).vFrom = x.vFrom ∧
    (retractRow e t k x).vTo = x.vTo ∧
    (x.eid = e → (retractRow e t k x).tRet = some t ∧ (retractRow e t k x).retKind = some k) ∧
    (x.eid ≠ e → retractRow e t k x = x) := by
  unfold retractRow
  split
  · rename_i h; simp at h; simp [h]
  · rename_i h; simp at h; simp [h]

/-- A retraction succeeds exactly when a live row with that id exists (inside a transaction),
and then it rewrites only that row's `t_ret` and `ret_kind`. -/
theorem retract_spec {e t k : Int64} {s s' : ModelStore}
    (h : (WriteOp.retract e t k).run s = .ok s') :
    (∃ r, s.current.triple e = some r ∧ r.tRet = none) ∧
      s'.current = { s.current with triples := s.current.triples.map (retractRow e t k) } ∧
      s'.committed = s.committed ∧ s'.sps = s.sps := by
  obtain ⟨_, c, hstep, rfl⟩ := run_data_ok rfl h
  obtain ⟨hr, rfl⟩ := retract_ok hstep
  exact ⟨hr, rfl, rfl, rfl⟩

theorem retract_notFound {e t k : Int64} {s : ModelStore} (htx : s.inTx = true)
    (h : s.current.triple e = none) :
    (WriteOp.retract e t k).run s = .error .notFound := by
  simp [WriteOp.run, WriteOp.step, ModelState.retract, htx, h]

theorem retract_once {e t k : Int64} {s : ModelStore} {r : TripleRow} (htx : s.inTx = true)
    (h : s.current.triple e = some r) (hret : r.tRet.isSome = true) :
    (WriteOp.retract e t k).run s = .error (.violation .retractOnce) := by
  simp [WriteOp.run, WriteOp.step, ModelState.retract, htx, h, hret]

/-! ## Transactions and savepoints -/

/-- Commit publishes the current state and closes the transaction and every savepoint. -/
theorem commit_publishes {s s' : ModelStore} (h : WriteOp.commit.run s = .ok s') :
    s'.committed = s.current ∧ s'.current = s.current ∧ s'.inTx = false ∧ s'.sps = [] := by
  simp only [WriteOp.run] at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- Rollback restores the committed state. -/
theorem rollback_spec {s s' : ModelStore} (h : WriteOp.rollback.run s = .ok s') :
    s'.current = s.committed ∧ s'.committed = s.committed ∧ s'.inTx = false ∧ s'.sps = [] := by
  simp only [WriteOp.run] at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- Data writes keep the transaction flag, the savepoint stack and the committed state. -/
theorem data_keeps {op : WriteOp} (hd : op.isData = true) {s s' : ModelStore}
    (h : op.run s = .ok s') : s'.inTx = s.inTx ∧ s'.sps = s.sps ∧ s'.committed = s.committed := by
  obtain ⟨_, c, _, rfl⟩ := run_data_ok hd h
  exact ⟨rfl, rfl, rfl⟩

/-- Only commit changes the committed state. -/
theorem run_committed {op : WriteOp} (hop : op ≠ .commit) {s s' : ModelStore}
    (h : op.run s = .ok s') : s'.committed = s.committed := by
  cases op with
  | commit => exact absurd rfl hop
  | begin | rollback | savepoint _ =>
    simp only [WriteOp.run] at h; split at h
    all_goals (cases h; try rfl)
  | rollbackTo _ | release _ =>
    simp only [WriteOp.run] at h; split at h
    · split at h
      all_goals (cases h; try rfl)
    · cases h
  | insertTriple _ | retract _ _ _ | insertTerm _ | insertTx _ | setCounter _ _ | volatilePut _
  | volatileDel _ _ | addPredMulti _ => exact (data_keeps rfl h).2.2

theorem runAll_append {xs ys : List WriteOp} {s s' : ModelStore}
    (h : WriteOp.runAll (xs ++ ys) s = .ok s') :
    ∃ s₁, WriteOp.runAll xs s = .ok s₁ ∧ WriteOp.runAll ys s₁ = .ok s' := by
  induction xs generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons op ops ih =>
    simp only [List.cons_append, WriteOp.runAll] at h ⊢
    split at h
    · exact ih h
    · cases h

theorem runAll_committed {ops : List WriteOp} (hops : WriteOp.commit ∉ ops) {s s' : ModelStore}
    (h : WriteOp.runAll ops s = .ok s') : s'.committed = s.committed := by
  induction ops generalizing s with
  | nil => cases h; rfl
  | cons op ops ih =>
    simp only [WriteOp.runAll] at h
    split at h
    · rename_i s₁ h₁
      have hop : op ≠ .commit := fun e => hops (e ▸ List.mem_cons_self ..)
      rw [ih (fun hm => hops (List.mem_cons_of_mem _ hm)) h, run_committed hop h₁]
    · cases h

theorem runAll_data {ops : List WriteOp} (hops : ∀ op ∈ ops, op.isData = true) {s s' : ModelStore}
    (h : WriteOp.runAll ops s = .ok s') :
    s'.inTx = s.inTx ∧ s'.sps = s.sps ∧ s'.committed = s.committed := by
  induction ops generalizing s with
  | nil => cases h; exact ⟨rfl, rfl, rfl⟩
  | cons op ops ih =>
    simp only [WriteOp.runAll] at h
    split at h
    · rename_i s₁ h₁
      obtain ⟨a, b, c⟩ := ih (fun o ho => hops o (List.mem_cons_of_mem _ ho)) h
      obtain ⟨a', b', c'⟩ := data_keeps (hops op (List.mem_cons_self ..)) h₁
      exact ⟨a.trans a', b.trans b', c.trans c'⟩
    · cases h

/-- Begin, any operations except commit, then rollback: the store ends at the committed state
it started from. -/
theorem rollback_restores {ops : List WriteOp} (hops : WriteOp.commit ∉ ops) {s s' : ModelStore}
    (h : WriteOp.runAll (.begin :: ops ++ [.rollback]) s = .ok s') :
    s'.current = s.committed ∧ s'.committed = s.committed := by
  obtain ⟨s₁, h₁, h₂⟩ := runAll_append (xs := .begin :: ops) (ys := [.rollback]) h
  have hc₁ : s₁.committed = s.committed :=
    runAll_committed (ops := .begin :: ops)
      (fun hm => by
        rcases List.mem_cons.1 hm with e | e
        · cases e
        · exact hops e) h₁
  simp only [WriteOp.runAll] at h₂
  split at h₂
  · rename_i s₂ hr
    cases h₂
    obtain ⟨a, b, _⟩ := rollback_spec hr
    exact ⟨a.trans hc₁, b.trans hc₁⟩
  · cases h₂

/-- Savepoint, data writes, then rollback to it: the current state is the one at the savepoint,
and the savepoint stays open on top of the stack. -/
theorem rollbackTo_restores {n : String} {ops : List WriteOp}
    (hops : ∀ op ∈ ops, op.isData = true) {s s' : ModelStore}
    (h : WriteOp.runAll (.savepoint n :: ops ++ [.rollbackTo n]) s = .ok s') :
    s'.current = s.current ∧ s'.sps = (n, s.current) :: s.sps ∧ s'.inTx = true ∧
      s'.committed = s.committed := by
  obtain ⟨s₁, h₁, h₂⟩ := runAll_append (xs := .savepoint n :: ops) (ys := [.rollbackTo n]) h
  simp only [WriteOp.runAll] at h₁
  split at h₁
  · rename_i s₀ h₀
    simp only [WriteOp.run] at h₀
    split at h₀
    · rename_i htx
      cases h₀
      obtain ⟨hi, hs, hc⟩ := runAll_data hops h₁
      simp only [WriteOp.runAll, WriteOp.run, hi, htx, hs, spRollback, beq_self_eq_true,
        ite_true] at h₂
      cases h₂
      exact ⟨rfl, rfl, by simp, hc⟩
    · cases h₀
  · cases h₁

/-- Release keeps the writes and closes the named savepoint and every newer one. -/
theorem release_keeps {n : String} {s s' : ModelStore} (h : (WriteOp.release n).run s = .ok s') :
    s'.current = s.current ∧ s'.committed = s.committed ∧ s'.sps.IsSuffix s.sps ∧
      s'.sps.length < s.sps.length := by
  simp only [WriteOp.run] at h
  split at h
  · split at h
    · rename_i sps hr
      cases h
      exact ⟨rfl, rfl, spRelease_suffix hr⟩
    · cases h
  · cases h

end Tiramemsu.Store
