/-
Transactions on the model: a commit, for every body and every clock reading, keeps the store
well-formed and extends it, adds exactly one `tx` row with the next number and instant, and a
failure leaves the store as it was.
Requirements: statement-lifecycle (never forget), transaction-log (gap-free numbers, strictly
increasing instants, every committed transaction recorded).
-/
import TiramemsuProofs.Store.TxInv
import TiramemsuProofs.Store.Interval
import Tiramemsu.Model.Run
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The generic cores on the model -/

theorem interp_model {α : Type} : ∀ (p : SProg α) (s : ModelStore),
    (SProg.interp Op.run p : ModelM α) s = SProg.runModel p s
  | .pure a, s => rfl
  | .op o k, s => by
    simp only [SProg.interp, SProg.runModel]
    rw [mbind]
    cases (Op.run o : ModelM o.Res) s with
    | ok p => rcases p with ⟨x, s'⟩; exact interp_model (k x) s'
    | error e => rfl

theorem mtry {α : Type} (x : ModelM α) (h : StoreError → ModelM α) (s : ModelStore) :
    (tryCatchThe StoreError x h) s = match x s with | .ok p => .ok p | .error e => h e s := by
  show (tryCatch (x s) fun e => h e s) = _
  cases x s <;> rfl

/-- The model writer right after `begin` on a committed state. -/
def begun (st : ModelState) : ModelStore := { committed := st, current := st, inTx := true, sps := [] }

theorem begin_model (st : ModelState) :
    (WriteStore.begin : ModelM Unit) (ModelStore.ofState st) = .ok ((), begun st) := rfl

theorem tryBegin_model (st : ModelState) :
    (tryBegin : ModelM (Option StoreError)) (ModelStore.ofState st) = .ok (none, begun st) := rfl

theorem rollbackQuiet_model {s : ModelStore} (h : s.inTx = true) :
    (rollbackQuiet : ModelM Unit) s =
      .ok ((), { committed := s.committed, current := s.committed, inTx := false, sps := [] }) := by
  unfold rollbackQuiet
  rw [mtry]
  have hr : (WriteStore.rollback : ModelM Unit) s = WriteOp.rollback.exec s := rfl
  rw [hr, mexec]
  simp [WriteOp.run, h]

/-- The counters a transaction loads. -/
def countersOf (st : ModelState) : Option Counters := do
  pure ⟨← st.counter "next_term", ← st.counter "next_node", ← st.counter "next_bnode",
    ← st.counter "next_stmt", ← st.counter "last_t", ← st.counter "last_instant",
    ← st.counter "multi_version"⟩

theorem loadCounters_model (s : ModelStore) :
    (loadCounters : ModelM (Except Error Counters)) s =
      .ok (match countersOf s.current with
        | some c => .ok c
        | none => .error (.invalidTerm .value "meta table is missing counters"), s) := by
  unfold loadCounters countersOf
  simp only [mbind, mcounter]
  cases s.current.counter "next_term" <;> cases s.current.counter "next_node" <;>
    cases s.current.counter "next_bnode" <;> cases s.current.counter "next_stmt" <;>
    cases s.current.counter "last_t" <;> cases s.current.counter "last_instant" <;>
    cases s.current.counter "multi_version" <;> rfl

/-- The `tx` row a transaction inserts. -/
def txRowOf (c0 : Counters) (now : Int) : TxRow :=
  ⟨Int64.ofInt (c0.lastT.toInt + 1), Int64.ofInt (nextInstant c0.lastInstant.toInt now)⟩

/-- The context a body starts with. -/
def ctx0Of (c0 : Counters) (now : Int) (opts : TxOptions) : TxCtx :=
  { t := Int64.ofInt (c0.lastT.toInt + 1), instant := Int64.ofInt (nextInstant c0.lastInstant.toInt now), opts,
    report := { t := Int64.ofInt (c0.lastT.toInt + 1), instant := Int64.ofInt (nextInstant c0.lastInstant.toInt now) } }

theorem beginBody_model (now : Int) (opts : TxOptions) (c0 : Counters) (s : ModelStore) (htx : s.inTx = true) :
    (beginBody (pure now) opts c0 : ModelM (Except Error TxCtx)) s =
      if ¬(0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)) then
        .ok (.error (.idSpaceExhausted .tx), s)
      else if inInt64 (nextInstant c0.lastInstant.toInt now) = false then
        .error (StoreError.misuse s!"instant {nextInstant c0.lastInstant.toInt now} is outside the 64-bit range")
      else match s.current.insertTx (txRowOf c0 now) with
        | .ok c => .ok (.ok (ctx0Of c0 now opts), { s with current := c })
        | .error e => .error e := by
  unfold beginBody
  by_cases h1 : 0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)
  · rw [if_neg (by simp [h1]), if_neg (by simp [h1]), mbind, mpure]
    simp only
    by_cases h2 : inInt64 (nextInstant c0.lastInstant.toInt now) = true
    · rw [if_neg (by simp [h2]), if_neg (by simp [h2]), mbind]
      have hins : (WriteStore.insertTx (txRowOf c0 now) : ModelM Unit) s = (WriteOp.insertTx (txRowOf c0 now)).exec s := rfl
      erw [hins, mexec]
      simp only [WriteOp.run, htx, if_true, WriteOp.step]
      cases s.current.insertTx (txRowOf c0 now) <;> rfl
    · rw [if_pos (by simpa using h2), if_pos (by simpa using h2), mbind]
      rfl
  · rw [if_pos (by simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; exact h1), if_pos h1]
    rfl

/-! ## Commit -/

/-- A counter set on a model state. -/
def setC (st : ModelState) (n : String) (v : Int64) : ModelState :=
  { st with counters :=
      if st.counters.any (·.1 == n) then st.counters.map fun kv => if kv.1 == n then (kv.1, v) else kv
      else st.counters ++ [(n, v)] }

theorem setCounter_eq (st : ModelState) (n : String) (v : Int64) : st.setCounter n v = .ok (setC st n v) := rfl

theorem setCounter_model {s : ModelStore} (htx : s.inTx = true) (n : String) (v : Int64) :
    (WriteStore.setCounter n v : ModelM Unit) s = .ok ((), { s with current := setC s.current n v }) := by
  rw [msetCounter, mexec]; simp [WriteOp.run, htx, WriteOp.step, setCounter_eq]

theorem commit_model {s : ModelStore} (htx : s.inTx = true) :
    (WriteStore.commit : ModelM Unit) s =
      .ok ((), { committed := s.current, current := s.current, inTx := false, sps := [] }) := by
  have : (WriteStore.commit : ModelM Unit) s = WriteOp.commit.exec s := rfl
  rw [this, mexec]; simp [WriteOp.run, htx]

theorem counter_setC (st : ModelState) (n m : String) (v : Int64) :
    (setC st n v).counter m = if m = n then some v else st.counter m :=
  counter_setCounter st n m v _ (setCounter_eq st n v)

theorem countersOf_spec {st : ModelState} {c0 : Counters} (h : countersOf st = some c0) :
    st.counter "next_term" = some c0.nextTerm ∧ st.counter "next_node" = some c0.nextNode ∧
    st.counter "next_bnode" = some c0.nextBNode ∧ st.counter "next_stmt" = some c0.nextStmt ∧
    st.counter "last_t" = some c0.lastT ∧ st.counter "last_instant" = some c0.lastInstant ∧
    st.counter "multi_version" = some c0.multiVersion := by
  unfold countersOf at h
  cases h1 : st.counter "next_term" <;> cases h2 : st.counter "next_node" <;>
    cases h3 : st.counter "next_bnode" <;> cases h4 : st.counter "next_stmt" <;>
    cases h5 : st.counter "last_t" <;> cases h6 : st.counter "last_instant" <;>
    cases h7 : st.counter "multi_version" <;> simp [h1, h2, h3, h4, h5, h6, h7] at h
  subst h; simp

theorem inInt64_toInt {x : Int} (h : inInt64 x = true) : (Int64.ofInt x).toInt = x := by
  simp only [inInt64, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Int64.toInt_ofInt_of_le h.1 h.2

/-- The invariant holds once the `tx` row is in. -/
theorem init_inv {st : ModelState} (hwf : WF st) {c0 : Counters} (hc : countersOf st = some c0) {now : Int}
    (hinst : inInt64 (nextInstant c0.lastInstant.toInt now) = true) :
    TxInv { committed := st, current := { st with txs := st.txs ++ [txRowOf c0 now] }, inTx := true, sps := [] } := by
  obtain ⟨_, _, _, _, h5, h6, _⟩ := countersOf_spec hc
  have hT : lastT st = c0.lastT.toInt := ctr_of_some h5
  have hI : lastInstant st = c0.lastInstant.toInt := ctr_of_some h6
  refine ⟨rfl, hwf, rfl, rfl, ⟨Int64.ofInt (nextInstant c0.lastInstant.toInt now), ?_, ?_⟩,
    ⟨⟨st.triples, [], by simp, List.forall₂_same.2 fun r _ => RowExt.refl _ r, by simp⟩,
      List.prefix_refl _, List.prefix_append _ _, fun _ _ => le_refl _, le_refl _⟩, ?_, hwf.uniq,
    fun n v h => ⟨v, h⟩⟩
  · show st.txs ++ [txRowOf c0 now] = _; rw [hT]; rfl
  · rw [inInt64_toInt hinst, hI]; exact lt_nextInstant _ _
  · intro r hr; exact (hwf.rows r hr).mono (by show lastT st ≤ lastT st + 1; omega) le_rfl

/-- The commit of a body that ended in the invariant: well-formed, extending, one `tx` row. -/
theorem commit_inv {s : ModelStore} (hi : TxInv s) {c0 : Counters} (hc : countersOf s.committed = some c0)
    {now : Int} (hr : 0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int))
    (hinst : inInt64 (nextInstant c0.lastInstant.toInt now) = true)
    (htxs : s.current.txs = s.committed.txs ++ [txRowOf c0 now]) :
    let c := setC (setC s.current "last_t" (Int64.ofInt (c0.lastT.toInt + 1))) "last_instant"
      (Int64.ofInt (nextInstant c0.lastInstant.toInt now))
    WF c ∧ Extends s.committed c ∧ c.txs = s.committed.txs ++ [txRowOf c0 now] ∧
      lastT c = lastT s.committed + 1 := by
  intro c
  obtain ⟨_, _, _, _, h5, h6, _⟩ := countersOf_spec hc
  have hT : lastT s.committed = c0.lastT.toInt := ctr_of_some h5
  have hI : lastInstant s.committed = c0.lastInstant.toInt := ctr_of_some h6
  have hct : ∀ m, m ≠ "last_t" → m ≠ "last_instant" → c.counter m = s.current.counter m := by
    intro m h1 h2; simp [c, counter_setC, h1, h2]
  have hlt : lastT c = c0.lastT.toInt + 1 := by
    show ((c.counter "last_t").getD 0).toInt = _
    rw [counter_setC, if_neg (by decide), counter_setC, if_pos rfl, Option.getD_some]
    have : (counterMax : Int) < 2 ^ 63 := by unfold counterMax; norm_num
    exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  have hli : lastInstant c = nextInstant c0.lastInstant.toInt now := by
    show ((c.counter "last_instant").getD 0).toInt = _
    rw [counter_setC, if_pos rfl, Option.getD_some]
    exact inInt64_toInt hinst
  have hns : nextStmt c = nextStmt s.current := by
    show ctr c "next_stmt" = ctr s.current "next_stmt"
    unfold ctr; rw [hct _ (by decide) (by decide)]
  have htr : c.triples = s.current.triples := rfl
  have htx : c.txs = s.committed.txs ++ [txRowOf c0 now] := htxs
  have hwf := hi.wf
  have hids : ∀ n ∈ idNames, ctr c n = ctr s.current n := by
    intro n hn
    simp [idNames] at hn
    unfold ctr
    rcases hn with rfl | rfl | rfl | rfl <;> rw [hct _ (by decide) (by decide)]
  refine ⟨⟨hi.uniq, ?_, by rw [hlt]; omega, by rw [hlt]; exact hr.2, ?_, ?_, ?_, ?_⟩, ?_, htx, by rw [hlt, hT]⟩
  · intro r hrm; rw [hlt, hns, ← hT]; exact hi.rows r hrm
  · rw [hns]
    have := hi.ext.ids "next_stmt" (by simp [idNames])
    have := hwf.nextLo
    unfold nextStmt at *; omega
  · rw [htx, List.map_append, hlt, hwf.txs, hT]
    have h0 : 0 ≤ c0.lastT.toInt := by rw [← hT]; exact hwf.lastTLo
    simp only [List.map_cons, List.map_nil, txRowOf]
    have : (counterMax : Int) < 2 ^ 63 := by unfold counterMax; norm_num
    rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
    rw [show (c0.lastT.toInt + 1).toNat = c0.lastT.toInt.toNat + 1 by omega, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    congr 2
    omega
  · rw [htx, List.map_append, List.pairwise_append]
    refine ⟨hwf.inst, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton, txRowOf] at hb
    subst hb
    rw [inInt64_toInt hinst]
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 ha
    have := hwf.lastInst r hr'
    have := lt_nextInstant c0.lastInstant.toInt now
    rw [hI] at *; omega
  · intro r hrm
    rw [hli]
    rw [htx] at hrm
    rcases List.mem_append.1 hrm with hrm | hrm
    · have := hwf.lastInst r hrm
      have := lt_nextInstant c0.lastInstant.toInt now
      rw [hI] at *; omega
    · rw [List.mem_singleton] at hrm; subst hrm
      simp only [txRowOf]; rw [inInt64_toInt hinst]
  · obtain ⟨pre, new, hb, f, nw⟩ := hi.ext.rows
    exact ⟨⟨pre, new, by rw [htr, hb], f, nw⟩, hi.ext.terms, by rw [htx]; exact List.prefix_append _ _,
      fun n hn => by rw [hids n hn]; exact hi.ext.ids n hn, by rw [hlt, ← hT]; omega⟩

theorem transact_spec {α : Type} (now : Int) (opts : TxOptions) (body : EngM α) (st : ModelState)
    (hwf : WF st) :
    (∃ e, Model.transactE now opts body st = (.error e, st)) ∨
    (∃ a rep st', Model.transactE now opts body st = (.ok (a, rep), st') ∧ WF st' ∧ Extends st st' ∧
      st'.txs = st.txs ++ [⟨Int64.ofInt (lastT st + 1), Int64.ofInt (nextInstant (lastInstant st) now)⟩] ∧
      lastT st' = lastT st + 1 ∧ rep.t.toInt = lastT st + 1 ∧
      rep.instant.toInt = nextInstant (lastInstant st) now) := by
  unfold Model.transactE Model.onState transactCore
  rw [mbind, tryBegin_model]
  simp only
  rw [mtry, mbind, loadCounters_model]
  simp only [begun]
  cases hc : countersOf st with
  | none =>
    simp only
    rw [mbind, rollbackQuiet_model rfl]
    exact Or.inl ⟨_, rfl⟩
  | some c0 =>
    simp only
    rw [mbind, beginBody_model now opts c0 _ rfl]
    by_cases h1 : 0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)
    swap
    · rw [if_pos h1]; simp only; rw [mbind, rollbackQuiet_model rfl]; exact Or.inl ⟨_, rfl⟩
    rw [if_neg (not_not.2 h1)]
    by_cases h2 : inInt64 (nextInstant c0.lastInstant.toInt now) = true
    swap
    · rw [if_pos (by simpa using h2)]; simp only; rw [mbind, rollbackQuiet_model rfl]; exact Or.inl ⟨_, rfl⟩
    rw [if_neg (by simp [h2])]
    simp only
    cases hins : st.insertTx (txRowOf c0 now) with
    | error e => simp only; rw [mbind, rollbackQuiet_model rfl]; exact Or.inl ⟨_, rfl⟩
    | ok c =>
      have hc' := insertTx_ok hins
      subst hc'
      simp only
      rw [mbind]
      unfold runBody
      rw [interp_model]
      have hinv := init_inv hwf hc h2
      cases hr : SProg.runModel ((body.run (ctx0Of c0 now opts)).run)
          { committed := st, current := { st with txs := st.txs ++ [txRowOf c0 now] }, inTx := true, sps := [] } with
      | error e => simp only; rw [mbind, rollbackQuiet_model rfl]; exact Or.inl ⟨_, rfl⟩
      | ok p =>
        rcases p with ⟨res, s3⟩
        obtain ⟨hi3, fr⟩ := inv_prog _ hinv hr
        simp only
        cases res with
        | error e =>
          simp only
          rw [mbind, rollbackQuiet_model hi3.inTx]
          exact Or.inl ⟨e, congrArg (Prod.mk (Except.error e)) fr.1⟩
        | ok q =>
          rcases q with ⟨a, ctx⟩
          simp only
          rw [mbind, setCounter_model hi3.inTx]
          simp only
          rw [mbind, setCounter_model (s := { s3 with current := setC s3.current "last_t" (ctx0Of c0 now opts).t })
            hi3.inTx]
          simp only
          rw [mbind, commit_model
            (s := { s3 with current := (setC (setC s3.current "last_t" (ctx0Of c0 now opts).t) "last_instant" (ctx0Of c0 now opts).instant) })
            hi3.inTx]
          simp only
          have hcc : countersOf s3.committed = some c0 := by rw [fr.1]; exact hc
          have htxs : s3.current.txs = s3.committed.txs ++ [txRowOf c0 now] := by rw [fr.2.2.2, fr.1]
          obtain ⟨w, e, t, l⟩ := commit_inv hi3 hcc h1 h2 htxs
          obtain ⟨_, _, _, _, h5, h6, _⟩ := countersOf_spec hc
          have hT : lastT st = c0.lastT.toInt := ctr_of_some h5
          have hI : lastInstant st = c0.lastInstant.toInt := ctr_of_some h6
          have hcst : s3.committed = st := fr.1
          rw [hcst] at e t l
          refine Or.inr ⟨a, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact w
          · exact e
          · exact t.trans (by rw [hT, hI]; rfl)
          · exact l
          · show (Int64.ofInt (c0.lastT.toInt + 1)).toInt = _
            have : (counterMax : Int) < 2 ^ 63 := by unfold counterMax; norm_num
            rw [Int64.toInt_ofInt_of_le (by omega) (by omega), hT]
          · show (Int64.ofInt (nextInstant c0.lastInstant.toInt now)).toInt = _
            rw [inInt64_toInt h2, hI]

end Tiramemsu.Engine
