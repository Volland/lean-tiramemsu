/-
The headline theorems of the statement lifecycle, the transaction log and speculation, over
`Model.transact`, `Model.dryRun` and `Model.speculate` for every body, every clock reading and
every option set.
Requirements: statement-lifecycle (all five), transaction-log (gap-free numbers, strictly
increasing instants, every committed transaction recorded), speculative-transactions (pure,
burned, dry run).
-/
import TiramemsuProofs.Store.Speculation
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Burning keeps the invariant -/

theorem burnSt_none : ∀ (st : ModelState) (c1 : List (String × Int64)) (m : String),
    st.counter m = none → (burnSt st c1).counter m = none
  | st, [], m, h => h
  | st, (n, v) :: rest, m, h => by
    rw [burnSt_cons]
    apply burnSt_none
    rw [stepB_counter]
    by_cases hm : m = n
    · subst hm; simp [h]
    · simp [hm, h]

theorem ctr_burnSt_mono (st : ModelState) (c1 : List (String × Int64)) (m : String) :
    ctr st m ≤ ctr (burnSt st c1) m := by
  unfold ctr
  cases hc : st.counter m with
  | none => rw [burnSt_none st c1 m hc]
  | some cur =>
    obtain ⟨cur', h', hle⟩ := burnSt_mono st c1 m cur hc
    rw [h']; exact hle

theorem burnSt_wf_extends {st : ModelState} (hwf : WF st) (c1 : List (String × Int64))
    (hn : ∀ p ∈ c1, p.1 ∈ idCounterNames) :
    WF (burnSt st c1) ∧ Extends st (burnSt st c1) := by
  obtain ⟨ht, hte, htx, _, _⟩ := burnSt_frame st c1
  have hnot : ∀ m, m ∉ idCounterNames → (burnSt st c1).counter m = st.counter m := by
    intro m hm; apply burnSt_other; intro h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact hm (hn p hp)
  have hlt : lastT (burnSt st c1) = lastT st := by
    unfold lastT ctr; rw [hnot _ (by decide)]
  have hli : lastInstant (burnSt st c1) = lastInstant st := by
    unfold lastInstant ctr; rw [hnot _ (by decide)]
  have hmono : ∀ m, ctr st m ≤ ctr (burnSt st c1) m := ctr_burnSt_mono st c1
  have hns : nextStmt st ≤ nextStmt (burnSt st c1) := hmono "next_stmt"
  refine ⟨⟨by rw [ht]; exact hwf.uniq, ?_, by rw [hlt]; exact hwf.lastTLo, by rw [hlt]; exact hwf.lastTHi,
    le_trans hwf.nextLo hns, by rw [htx, hlt]; exact hwf.txs, by rw [htx]; exact hwf.inst, ?_⟩,
    ⟨⟨st.triples, [], by rw [ht]; simp, List.forall₂_same.2 fun r _ => RowExt.refl _ r, by simp⟩,
      by rw [hte], by rw [htx], fun m _ => hmono m, by rw [hlt]⟩⟩
  · intro r hr; rw [ht] at hr; rw [hlt]; exact (hwf.rows r hr).mono le_rfl hns
  · intro r hr; rw [htx] at hr; rw [hli]; exact hwf.lastInst r hr

/-! ## Never forget, for every body -/

/-- Never forget: after any transaction (any body, clock reading and options), the store is
well-formed and extends the previous one — every statement kept with its content, retracted only
by this transaction if it was live, terms and transaction rows kept, id counters not lowered,
no statement referencing itself. -/
theorem transact_wf_extends {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState)
    (hwf : WF st) : WF (Model.transact now opts prog st).2 ∧ Extends st (Model.transact now opts prog st).2 := by
  show WF (Model.transactE now opts prog.run st).2 ∧ Extends st (Model.transactE now opts prog.run st).2
  rcases transact_spec now opts prog.run st hwf with ⟨e, h⟩ | ⟨a, rep, st', h, w, x, _⟩
  · rw [h]; exact ⟨hwf, Extends.refl st⟩
  · rw [h]; exact ⟨w, x⟩

theorem transactE_wf_extends {α : Type} (now : Int) (opts : TxOptions) (body : EngM α) (st : ModelState)
    (hwf : WF st) : WF (Model.transactE now opts body st).2 ∧ Extends st (Model.transactE now opts body st).2 := by
  rcases transact_spec now opts body st hwf with ⟨e, h⟩ | ⟨a, rep, st', h, w, x, _⟩
  · rw [h]; exact ⟨hwf, Extends.refl st⟩
  · rw [h]; exact ⟨w, x⟩

/-- The state after a speculative core: unchanged, or with burned id counters. -/
theorem speculative_state {α β : Type} (now : Int) (opts : TxOptions) (body : EngM α)
    (G : TxCtx → α → ModelState → Except StoreError (Except Error β))
    (after : TxCtx → α → ModelM (Except Error β))
    (hafter : ∀ ctx a s, after ctx a s = match G ctx a s.current with
      | .ok x => .ok (x, s)
      | .error e => .error e)
    (st : ModelState) (hwf : WF st) :
    (Model.onState (speculativeCore (pure now) opts body after) st).2 = st ∨
    ∃ σ, TxInv σ ∧ σ.committed = st ∧
      (Model.onState (speculativeCore (pure now) opts body after) st).2 = burnSt st (idsOf σ.current) := by
  rcases speculative_spec now opts body G after hafter st hwf with ⟨e, h⟩ | ⟨c0, σ, res, r, _, hi, hc, _, h, _⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact Or.inr ⟨σ, hi, hc, rfl⟩

/-- The dry run's follow-up on the model. -/
def dryG {α : Type} (ctx : TxCtx) (a : α) (_ : ModelState) : Except StoreError (Except Error (α × TxReport)) :=
  .ok (.ok (a, ctx.report.finish))

/-- The speculation's follow-up on the model: the query on a now view of the state. -/
def specG {α β : Type} (validAt : Option Int64) (q : ReadProg β) (_ : TxCtx) (_ : α) (st : ModelState) :
    Except StoreError (Except Error β) :=
  (ReadProg.run (specView validAt) q).onModel st

theorem dryG_after {α : Type} (ctx : TxCtx) (a : α) (s : ModelStore) :
    ((fun ctx a => pure (.ok (a, ctx.report.finish))) ctx a : ModelM (Except Error (α × TxReport))) s =
      match dryG ctx a s.current with
      | .ok x => .ok (x, s)
      | .error e => .error e := rfl

theorem specG_after {α β : Type} (validAt : Option Int64) (q : ReadProg β) (ctx : TxCtx) (a : α) (s : ModelStore) :
    ((fun _ _ => runReads (ReadProg.run (specView validAt) q)) ctx a :
      ModelM (Except Error β)) s =
      match specG validAt q ctx a s.current with
      | .ok x => .ok (x, s)
      | .error e => .error e := by
  show (RProg.interp ROp.run _ : ModelM _) s = _
  rw [runReads_model]; unfold specG
  cases RProg.onModel s.current _ <;> rfl

theorem dryRun_wf_extends {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState)
    (hwf : WF st) : WF (Model.dryRun now opts prog st).2 ∧ Extends st (Model.dryRun now opts prog st).2 := by
  show WF (Model.onState (dryRunCore (pure now) opts prog.run) st).2 ∧
    Extends st (Model.onState (dryRunCore (pure now) opts prog.run) st).2
  unfold dryRunCore
  rcases speculative_state now opts prog.run dryG _ dryG_after st hwf with h | ⟨σ, _, _, h⟩
  · rw [h]; exact ⟨hwf, Extends.refl st⟩
  · rw [h]; exact burnSt_wf_extends hwf _ (idsOf_names _)

theorem speculate_eq {α β : Type} (now : Int) (prog : TxProg α) (validAt : Option Int64) (q : ReadProg β)
    (st : ModelState) :
    Model.speculate now prog validAt q st = Model.onState (speculativeCore (pure now) {} prog.run
      (fun _ _ => runReads (ReadProg.run (specView validAt) q))) st :=
  rfl

theorem speculate_wf_extends {α β : Type} (now : Int) (prog : TxProg α) (validAt : Option Int64)
    (q : ReadProg β) (st : ModelState) (hwf : WF st) :
    WF (Model.speculate now prog validAt q st).2 ∧ Extends st (Model.speculate now prog validAt q st).2 := by
  rw [speculate_eq]
  rcases speculative_state now {} prog.run (specG validAt q) _ (specG_after validAt q) st hwf with h | ⟨σ, _, _, h⟩
  · rw [h]; exact ⟨hwf, Extends.refl st⟩
  · rw [h]; exact burnSt_wf_extends hwf _ (idsOf_names _)

/-! ## Corollaries: the lifecycle of one statement -/

/-- Every statement of `a` is in `b` with its content; its retraction is unchanged, or it was
live and is now retracted after `a`'s last transaction. -/
theorem extends_row {a b : ModelState} (h : Extends a b) {r : TripleRow} (hr : r ∈ a.triples) :
    ∃ r' ∈ b.triples, RowExt (lastT a) r r' := by
  obtain ⟨pre, new, hb, f, _⟩ := h.rows
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hl := f.length_eq
  have := (List.forall₂_iff_get.1 f).2 i hi (by omega)
  exact ⟨pre[i], by rw [hb]; exact List.mem_append_left _ (List.getElem_mem _), by simpa using this⟩

/-- Content is immutable and a retraction is permanent across a transaction; a statement live
before is either still live or retracted by this very transaction (`t_ret = last_t + 1`) with a
kind in 0–3. -/
theorem transact_retraction {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState)
    (hwf : WF st) {r : TripleRow} (hr : r ∈ st.triples) :
    ∃ r' ∈ (Model.transact now opts prog st).2.triples,
      r'.eid = r.eid ∧ r'.s = r.s ∧ r'.p = r.p ∧ r'.o = r.o ∧ r'.tAdd = r.tAdd ∧ r'.vFrom = r.vFrom ∧
      r'.vTo = r.vTo ∧
      (∀ x, r.tRet = some x → r'.tRet = some x ∧ r'.retKind = r.retKind) ∧
      (r.tRet = none → r'.tRet = none ∨
        ∃ x k, r'.tRet = some x ∧ x.toInt = lastT st + 1 ∧ r'.retKind = some k ∧ 0 ≤ k.toInt ∧ k.toInt ≤ 3) := by
  obtain ⟨w, ext⟩ := transact_wf_extends now opts prog st hwf
  obtain ⟨r', hr', h⟩ := extends_row ext hr
  refine ⟨r', hr', h.eid, h.s, h.p, h.o, h.tAdd, h.vFrom, h.vTo, ?_, ?_⟩
  · intro x hx
    rcases h.ret with ⟨e1, e2⟩ | ⟨hn, _⟩
    · exact ⟨e1.trans hx, e2⟩
    · rw [hx] at hn; cases hn
  · intro hn
    rcases h.ret with ⟨e1, _⟩ | ⟨_, x, hx, hlt⟩
    · exact Or.inl (e1.trans hn)
    · have ok := w.rows r' hr'
      rcases ok.ret with ⟨h1, _⟩ | ⟨y, k, hy, hk, _, hle, k0, k3⟩
      · rw [hx] at h1; cases h1
      · rw [hx] at hy; cases hy
        -- `t_ret` is after the old last transaction and at most the new one, which is one more
        have hT : lastT (Model.transact now opts prog st).2 ≤ lastT st + 1 := by
          rcases transact_spec now opts prog.run st hwf with ⟨e, hh⟩ | ⟨a, rep, st', hh, _, _, _, hl, _⟩
          · show lastT (Model.transactE now opts prog.run st).2 ≤ _; rw [hh]; simp only; omega
          · show lastT (Model.transactE now opts prog.run st).2 ≤ _; rw [hh]; simp only; omega
        exact Or.inr ⟨x, k, hx, by omega, hk, k0, k3⟩

/-- No stored statement references itself. -/
theorem wf_no_self_reference {st : ModelState} (hwf : WF st) :
    ∀ r ∈ st.triples, r.s ≠ r.eid ∧ r.o ≠ r.eid :=
  fun r hr => ⟨(hwf.rows r hr).noSelfS, (hwf.rows r hr).noSelfO⟩

/-- Every statement of a well-formed store has an eid counter below `next_stmt`. -/
theorem wf_eid_below {st : ModelState} (hwf : WF st) : ∀ r ∈ st.triples, eidCtr r.eid < nextStmt st :=
  fun r hr => (hwf.rows r hr).ctrHi

/-- Eids are never reused: a statement new after a transaction has an eid counter at or above the
old `next_stmt`, above every eid counter issued before; `next_stmt` never goes down. -/
theorem forall₂_eids {T : Int} : ∀ {l m : List TripleRow}, List.Forall₂ (RowExt T) l m →
    m.map (·.eid) = l.map (·.eid)
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h r => by simp [h.eid, forall₂_eids r]

theorem extends_new_eids {a b : ModelState} (hwf : WF a) (h : Extends a b) :
    nextStmt a ≤ nextStmt b ∧
    ∃ pre new, b.triples = pre ++ new ∧ pre.map (·.eid) = a.triples.map (·.eid) ∧
      ∀ r ∈ new, ∀ x ∈ a.triples, eidCtr x.eid < eidCtr r.eid := by
  obtain ⟨pre, new, hb, f, nw⟩ := h.rows
  refine ⟨h.ids "next_stmt" (by simp [idNames]), pre, new, hb, ?_, ?_⟩
  · exact forall₂_eids f
  · intro r hr x hx
    exact lt_of_lt_of_le (wf_eid_below hwf x hx) (nw r hr).1

/-! ## The transaction log -/

/-- Gap-free numbers and a row for every commit: a committed transaction (any body, including
one that does nothing) appends exactly one `tx` row, numbered `last_t + 1`, with instant
`max(now, last_instant + 1)`; a failed one changes nothing. -/
theorem transact_txlog {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState)
    (hwf : WF st) :
    (∃ e, Model.transact now opts prog st = (.error e, st)) ∨
    (∃ a rep st', Model.transact now opts prog st = (.ok (a, rep), st') ∧
      st'.txs = st.txs ++ [⟨Int64.ofInt (lastT st + 1), Int64.ofInt (nextInstant (lastInstant st) now)⟩] ∧
      rep.t.toInt = lastT st + 1 ∧ rep.instant.toInt = nextInstant (lastInstant st) now ∧
      lastT st' = lastT st + 1) := by
  rcases transact_spec now opts prog.run st hwf with ⟨e, h⟩ | ⟨a, rep, st', h, _, _, ht, hl, hr, hi⟩
  · exact Or.inl ⟨e, h⟩
  · exact Or.inr ⟨a, rep, st', h, ht, hr, hi, hl⟩

/-- On a well-formed store the transaction numbers are exactly `1 … last_t`. -/
theorem wf_tx_numbers {st : ModelState} (hwf : WF st) :
    st.txs.map (·.t.toInt) = List.map (fun i : Nat => (i : Int) + 1) (List.range (lastT st).toNat) := hwf.txs

/-- On a well-formed store instants strictly increase with `t`, whatever the clock read. -/
theorem wf_instants_increasing {st : ModelState} (hwf : WF st) :
    (st.txs.map (·.instant.toInt)).Pairwise (· < ·) := hwf.inst

/-- Dry runs and speculation consume no number and record no row. -/
theorem dryRun_no_tx {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState)
    (hwf : WF st) : (Model.dryRun now opts prog st).2.txs = st.txs ∧
      lastT (Model.dryRun now opts prog st).2 = lastT st := by
  rcases speculative_state now opts prog.run dryG _ dryG_after st hwf with h | ⟨σ, _, _, h⟩
  · show (Model.onState (dryRunCore (pure now) opts prog.run) st).2.txs = _ ∧
      lastT (Model.onState (dryRunCore (pure now) opts prog.run) st).2 = _
    unfold dryRunCore; rw [h]; exact ⟨rfl, rfl⟩
  · show (Model.onState (dryRunCore (pure now) opts prog.run) st).2.txs = _ ∧
      lastT (Model.onState (dryRunCore (pure now) opts prog.run) st).2 = _
    unfold dryRunCore; rw [h]
    refine ⟨(burnSt_frame st _).2.2.1, ?_⟩
    unfold lastT ctr
    rw [burnSt_other]
    intro hm
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
    have := idsOf_names _ p hp
    rw [hpe] at this
    simp [idCounterNames] at this

theorem speculate_no_tx {α β : Type} (now : Int) (prog : TxProg α) (validAt : Option Int64) (q : ReadProg β)
    (st : ModelState) (hwf : WF st) : (Model.speculate now prog validAt q st).2.txs = st.txs := by
  rw [speculate_eq]
  rcases speculative_state now {} prog.run (specG validAt q) _ (specG_after validAt q) st hwf with h | ⟨σ, _, _, h⟩
  · rw [h]
  · rw [h]; exact (burnSt_frame st _).2.2.1

/-! ## Speculation -/

/-- Speculation is observationally pure: afterwards every statement, term, transaction row,
volatile value and `pred_multi` row is as before, and every counter other than the id counters
too; the id counters are not lowered. -/
theorem speculate_pure {α β : Type} (now : Int) (prog : TxProg α) (validAt : Option Int64) (q : ReadProg β)
    (st : ModelState) (hwf : WF st) :
    let st' := (Model.speculate now prog validAt q st).2
    st'.triples = st.triples ∧ st'.terms = st.terms ∧ st'.txs = st.txs ∧ st'.volatile = st.volatile ∧
    st'.predMulti = st.predMulti ∧ (∀ n, n ∉ idCounterNames → st'.counter n = st.counter n) ∧
    (∀ n, ctr st n ≤ ctr st' n) := by
  intro st'
  rcases speculative_state now {} prog.run (specG validAt q) _ (specG_after validAt q) st hwf with h | ⟨σ, _, _, h⟩
  · have : st' = st := by
      show (Model.speculate now prog validAt q st).2 = st
      rw [speculate_eq]; exact h
    rw [this]; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ => le_refl _⟩
  · have : st' = burnSt st (idsOf σ.current) := by
      show (Model.speculate now prog validAt q st).2 = _
      rw [speculate_eq]; exact h
    rw [this]
    obtain ⟨a, b, c, d, e⟩ := burnSt_frame st (idsOf σ.current)
    refine ⟨a, b, c, d, e, ?_, ?_⟩
    · intro n hn
      apply burnSt_other
      intro hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      exact hn (idsOf_names _ p hp)
    · intro n; exact ctr_burnSt_mono st _ n

/-- A dry run returns exactly what a commit from the same state and clock reading returns —
the same value and report, including the would-be number and instant — or the same error. -/
theorem dryRun_eq_transact {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState)
    (hwf : WF st) : (Model.dryRun now opts prog st).1 = (Model.transact now opts prog st).1 := by
  show (Model.onState (dryRunCore (pure now) opts prog.run) st).1 = (Model.transactE now opts prog.run st).1
  rw [transact_result now opts prog.run st hwf]
  unfold dryRunCore
  rw [speculative_result now opts prog.run dryG _ dryG_after st hwf]
  unfold expectedSpec expected
  cases countersOf st with
  | none => rfl
  | some c0 =>
    simp only
    split
    · rfl
    · split
      · rfl
      · cases st.insertTx (txRowOf c0 now) with
        | error e => rfl
        | ok c =>
          simp only
          cases SProg.runModel ((prog.run.run (ctx0Of c0 now opts)).run) (startOf st c0 now) with
          | error e => rfl
          | ok p =>
            rcases p with ⟨res, σ⟩
            cases res with
            | error e => rfl
            | ok q => rcases q with ⟨a, ctx⟩; rfl

theorem countersOf_some {st : ModelState} {c0 : Counters} (h : countersOf st = some c0) :
    ∀ n ∈ idCounterNames, ∃ v, st.counter n = some v := by
  obtain ⟨h1, h2, h3, h4, _⟩ := countersOf_spec h
  intro n hn
  simp only [idCounterNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨_, h1⟩
  · exact ⟨_, h2⟩
  · exact ⟨_, h3⟩
  · exact ⟨_, h4⟩

/-- Ids allocated in a speculation are burned: unless the speculation did nothing (it failed
before or at its body's storage), there is a speculative state `σ` — the state its query sees,
whose result is the value returned — such that afterwards every id counter is at least `σ`'s,
so every statement eid, node, blank node and term id `σ` issued is below the counters and is
never issued again. -/
theorem speculate_burns {α β : Type} (now : Int) (prog : TxProg α) (validAt : Option Int64) (q : ReadProg β)
    (st : ModelState) (hwf : WF st) :
    (Model.speculate now prog validAt q st).2 = st ∨
    ∃ σ, TxInv σ ∧ σ.committed = st ∧
      (∀ x ∈ σ.current.triples, eidCtr x.eid < nextStmt (Model.speculate now prog validAt q st).2) ∧
      (∀ n ∈ idCounterNames, ∀ v, σ.current.counter n = some v →
        v.toInt ≤ ctr (Model.speculate now prog validAt q st).2 n) ∧
      ((∃ e, (Model.speculate now prog validAt q st).1 = .error e) ∨
       (Model.speculate now prog validAt q st).1 =
         match (ReadProg.run (specView validAt) q).onModel σ.current with
         | .ok r => r
         | .error e => .error (.store e)) := by
  rw [speculate_eq]
  rcases speculative_spec now {} prog.run (specG validAt q) _ (specG_after validAt q) st hwf with
    ⟨e, h⟩ | ⟨c0, σ, res, r, hc, hi, hσc, hr, h, hres⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]
    have hburn : ∀ n ∈ idCounterNames, ∀ v, σ.current.counter n = some v →
        v.toInt ≤ ctr (burnSt st (idsOf σ.current)) n := by
      intro n hn v hv
      obtain ⟨cur, hcur⟩ := countersOf_some hc n hn
      obtain ⟨cur', h', hle⟩ := burnSt_ge st _ n v cur (idsOf_mem _ hn hv) hcur
      unfold ctr; rw [h']; exact hle
    refine Or.inr ⟨σ, hi, hσc, ?_, hburn, ?_⟩
    · intro x hx
      have hlt := (hi.rows x hx).ctrHi
      obtain ⟨v, hv⟩ : ∃ v, σ.current.counter "next_stmt" = some v := by
        obtain ⟨cur, hcur⟩ := countersOf_some hc "next_stmt" (by simp [idCounterNames])
        rw [← hσc] at hcur
        exact hi.present _ _ hcur
      have := hburn "next_stmt" (by simp [idCounterNames]) v hv
      unfold nextStmt; unfold nextStmt at hlt; unfold ctr at hlt; rw [hv] at hlt
      simp only [Option.getD_some] at hlt
      exact lt_of_lt_of_le hlt this
    · cases res with
      | error e => exact Or.inl ⟨e, hres⟩
      | ok p =>
        rcases p with ⟨a, ctx⟩
        right
        show r = _
        unfold specG at hres
        simp only at hres
        rw [hres]

end Tiramemsu.Engine
