/-
Dry runs and speculation on the model: the body runs exactly as in a commit; afterwards the
store differs from before only in raised id counters; the query sees the speculative state; every
id that state allocated is below the raised counters; a dry run returns what a commit returns.
Requirements: speculative-transactions / "Speculation is observationally pure", "Ids allocated in
speculation are burned", "Dry run returns the would-be report".
-/
import TiramemsuProofs.Store.Oblivious
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Savepoints and burns on the model -/

theorem savepoint_model {s : ModelStore} (htx : s.inTx = true) (n : String) :
    (WriteStore.savepoint n : ModelM Unit) s = .ok ((), { s with sps := (n, s.current) :: s.sps }) := by
  have : (WriteStore.savepoint n : ModelM Unit) s = (WriteOp.savepoint n).exec s := rfl
  rw [this, mexec]; simp [WriteOp.run, htx]

theorem rollbackTo_model {s : ModelStore} (htx : s.inTx = true) {c : ModelState} (hs : s.sps = [("spec", c)]) :
    (WriteStore.rollbackTo "spec" : ModelM Unit) s = .ok ((), { s with current := c }) := by
  have : (WriteStore.rollbackTo "spec" : ModelM Unit) s = (WriteOp.rollbackTo "spec").exec s := rfl
  rw [this, mexec]
  simp [WriteOp.run, htx, hs, spRollback]

theorem release_model {s : ModelStore} (htx : s.inTx = true) {c : ModelState} (hs : s.sps = [("spec", c)]) :
    (WriteStore.release "spec" : ModelM Unit) s = .ok ((), { s with sps := [] }) := by
  have : (WriteStore.release "spec" : ModelM Unit) s = (WriteOp.release "spec").exec s := rfl
  rw [this, mexec]
  simp [WriteOp.run, htx, hs, spRelease]

/-- The id counters read before a speculative rollback. -/
def idsOf (st : ModelState) : List (String × Int64) :=
  [("next_term", st.counter "next_term"), ("next_node", st.counter "next_node"),
   ("next_bnode", st.counter "next_bnode"), ("next_stmt", st.counter "next_stmt")].filterMap
    fun (n, v) => v.map (n, ·)

theorem readIdCounters_model (s : ModelStore) :
    (readIdCounters : ModelM (List (String × Int64))) s = .ok (idsOf s.current, s) := by
  unfold readIdCounters
  simp only [mbind, mcounter, mpure]
  rfl

/-- Raising counters, one after another. -/
def burnSt (st : ModelState) : List (String × Int64) → ModelState
  | [] => st
  | (n, v) :: rest => burnSt (match st.counter n with
      | some cur => if cur.toInt < v.toInt then setC st n v else st
      | none => st) rest

theorem burnIds_model : ∀ (c1 : List (String × Int64)) {s : ModelStore}, s.inTx = true →
    (burnIds c1 : ModelM Unit) s = .ok ((), { s with current := burnSt s.current c1 })
  | [], s, _ => rfl
  | (n, v) :: rest, s, htx => by
    unfold burnIds
    rw [mbind, mcounter]
    simp only
    cases hc : s.current.counter n with
    | none =>
      simp only
      rw [burnIds_model rest htx]
      simp [burnSt, hc]
    | some cur =>
      simp only
      by_cases hlt : cur.toInt < v.toInt
      · rw [if_pos hlt, mbind, setCounter_model htx]
        simp only
        rw [burnIds_model rest (s := { s with current := setC s.current n v }) htx]
        simp [burnSt, hc, hlt]
      · rw [if_neg hlt]
        rw [burnIds_model rest htx]
        simp [burnSt, hc, hlt]

/-- Burning changes nothing but counters. -/
theorem burnSt_frame : ∀ (st : ModelState) (c1 : List (String × Int64)),
    (burnSt st c1).triples = st.triples ∧ (burnSt st c1).terms = st.terms ∧ (burnSt st c1).txs = st.txs ∧
    (burnSt st c1).volatile = st.volatile ∧ (burnSt st c1).predMulti = st.predMulti
  | st, [] => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | st, (n, v) :: rest => by
    simp only [burnSt]
    obtain ⟨a, b, c, d, e⟩ := burnSt_frame (match st.counter n with
      | some cur => if cur.toInt < v.toInt then setC st n v else st
      | none => st) rest
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_, e.trans ?_⟩ <;>
      (cases st.counter n with
       | none => rfl
       | some cur => by_cases h : cur.toInt < v.toInt <;> simp [h, setC])

/-- One burn step. -/
def stepB (st : ModelState) (n : String) (v : Int64) : ModelState :=
  match st.counter n with
  | some cur => if cur.toInt < v.toInt then setC st n v else st
  | none => st

theorem burnSt_cons (st : ModelState) (n : String) (v : Int64) (rest : List (String × Int64)) :
    burnSt st ((n, v) :: rest) = burnSt (stepB st n v) rest := rfl

theorem stepB_counter (st : ModelState) (n : String) (v : Int64) (m : String) :
    (stepB st n v).counter m = if m = n then (st.counter n).map (fun cur => if cur.toInt < v.toInt then v else cur)
      else st.counter m := by
  unfold stepB
  cases hc : st.counter n with
  | none => by_cases h : m = n <;> simp [h, hc]
  | some cur =>
    by_cases hlt : cur.toInt < v.toInt
    · simp only [hlt, if_true, counter_setC]
      by_cases h : m = n <;> simp [h, hc, hlt]
    · simp only [hlt, if_false]
      by_cases h : m = n
      · subst h; simp [hc, hlt]
      · simp [h]

theorem burnSt_other : ∀ (st : ModelState) (c1 : List (String × Int64)) (m : String),
    m ∉ c1.map (·.1) → (burnSt st c1).counter m = st.counter m
  | st, [], m, _ => rfl
  | st, (n, v) :: rest, m, hm => by
    rw [burnSt_cons, burnSt_other _ rest m (fun h => hm (List.mem_cons_of_mem _ h)), stepB_counter]
    have : m ≠ n := fun h => hm (by simp [h])
    simp [this]

theorem burnSt_mono : ∀ (st : ModelState) (c1 : List (String × Int64)) (m : String) (cur : Int64),
    st.counter m = some cur → ∃ cur', (burnSt st c1).counter m = some cur' ∧ cur.toInt ≤ cur'.toInt
  | st, [], m, cur, h => ⟨cur, h, le_refl _⟩
  | st, (n, v) :: rest, m, cur, h => by
    rw [burnSt_cons]
    have h1 : ∃ c2, (stepB st n v).counter m = some c2 ∧ cur.toInt ≤ c2.toInt := by
      rw [stepB_counter]
      by_cases hm : m = n
      · subst hm; rw [if_pos rfl, h]
        by_cases hlt : cur.toInt < v.toInt
        · exact ⟨v, by simp [hlt], le_of_lt hlt⟩
        · exact ⟨cur, by simp [hlt], le_refl _⟩
      · rw [if_neg hm]; exact ⟨cur, h, le_refl _⟩
    obtain ⟨c2, hc2, hle⟩ := h1
    obtain ⟨c3, hc3, hle'⟩ := burnSt_mono _ rest m c2 hc2
    exact ⟨c3, hc3, le_trans hle hle'⟩

theorem burnSt_ge : ∀ (st : ModelState) (c1 : List (String × Int64)) (m : String) (w cur : Int64),
    (m, w) ∈ c1 → st.counter m = some cur → ∃ cur', (burnSt st c1).counter m = some cur' ∧ w.toInt ≤ cur'.toInt
  | st, [], m, w, cur, hw, _ => by cases hw
  | st, (n, v) :: rest, m, w, cur, hw, h => by
    rw [burnSt_cons]
    rcases List.mem_cons.1 hw with hw | hw
    · obtain ⟨h1, h2⟩ := Prod.mk.inj hw
      subst h1; subst h2
      have h1 : ∃ c2, (stepB st m w).counter m = some c2 ∧ w.toInt ≤ c2.toInt := by
        rw [stepB_counter, if_pos rfl, h]
        by_cases hlt : cur.toInt < w.toInt
        · exact ⟨w, by simp [hlt], le_refl _⟩
        · exact ⟨cur, by simp [hlt], by omega⟩
      obtain ⟨c2, hc2, hle⟩ := h1
      obtain ⟨c3, hc3, hle'⟩ := burnSt_mono _ rest m c2 hc2
      exact ⟨c3, hc3, le_trans hle hle'⟩
    · have h1 : ∃ c2, (stepB st n v).counter m = some c2 := by
        rw [stepB_counter]
        by_cases hm : m = n
        · subst hm; rw [if_pos rfl, h]; exact ⟨_, rfl⟩
        · rw [if_neg hm]; exact ⟨cur, h⟩
      obtain ⟨c2, hc2⟩ := h1
      exact burnSt_ge _ rest m w c2 hw hc2

theorem idsOf_names (st : ModelState) : ∀ p ∈ idsOf st, p.1 ∈ idCounterNames := by
  intro p hp
  simp only [idsOf, List.mem_filterMap] at hp
  obtain ⟨⟨n, v⟩, hn, hv⟩ := hp
  cases v <;> simp at hv
  subst hv
  simp at hn
  rcases hn with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [idCounterNames]

theorem idsOf_mem (st : ModelState) {n : String} (hn : n ∈ idCounterNames) {v : Int64}
    (h : st.counter n = some v) : (n, v) ∈ idsOf st := by
  simp only [idCounterNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  simp only [idsOf, List.mem_filterMap]
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨("next_term", st.counter "next_term"), by simp, by simp [h]⟩
  · exact ⟨("next_node", st.counter "next_node"), by simp, by simp [h]⟩
  · exact ⟨("next_bnode", st.counter "next_bnode"), by simp, by simp [h]⟩
  · exact ⟨("next_stmt", st.counter "next_stmt"), by simp, by simp [h]⟩

/-- A read program on the writer reads its current state and changes nothing. -/
theorem runReads_model {α : Type} : ∀ (p : RProg α) (s : ModelStore),
    (RProg.interp ROp.run p : ModelM α) s = match p.onModel s.current with
      | .ok a => .ok (a, s)
      | .error e => .error e
  | .pure a, s => rfl
  | .read r k, s => by
    simp only [RProg.interp, RProg.onModel, RProg.runPure]
    rw [mbind, read_model]
    cases ROp.model r s.current with
    | ok x => exact runReads_model (k x) s
    | error e => rfl

/-- The store a body starts from. -/
def startOf (st : ModelState) (c0 : Counters) (now : Int) : ModelStore :=
  { committed := st, current := { st with txs := st.txs ++ [txRowOf c0 now] }, inTx := true, sps := [] }

/-- The context a speculative follow-up gets. -/
def afterCtx (ctx : TxCtx) (c0 : Counters) (now : Int) (opts : TxOptions) : TxCtx :=
  { ctx with t := (ctx0Of c0 now opts).t, instant := (ctx0Of c0 now opts).instant,
             report := { ctx.report with t := (ctx0Of c0 now opts).t, instant := (ctx0Of c0 now opts).instant } }

theorem speculative_spec {α β : Type} (now : Int) (opts : TxOptions) (body : EngM α)
    (G : TxCtx → α → ModelState → Except StoreError (Except Error β))
    (after : TxCtx → α → ModelM (Except Error β))
    (hafter : ∀ ctx a s, after ctx a s = match G ctx a s.current with
      | .ok x => .ok (x, s)
      | .error e => .error e)
    (st : ModelState) (hwf : WF st) :
    (∃ e, Model.onState (speculativeCore (pure now) opts body after) st = (.error e, st)) ∨
    (∃ c0 σ res r, countersOf st = some c0 ∧ TxInv σ ∧ σ.committed = st ∧
      SProg.runModel ((body.run (ctx0Of c0 now opts)).run) (startOf st c0 now) = .ok (res, σ) ∧
      Model.onState (speculativeCore (pure now) opts body after) st = (r, burnSt st (idsOf σ.current)) ∧
      (match res with
       | .error e => r = .error e
       | .ok (a, ctx) => G (afterCtx ctx c0 now opts) a σ.current = .ok r)) := by
  unfold Model.onState speculativeCore
  rw [mbind, tryBegin_model]
  simp only
  rw [mtry, mbind, savepoint_model rfl]
  simp only
  rw [mbind, mbind, loadCounters_model]
  simp only [begun]
  cases hc : countersOf st with
  | none =>
    simp only
    erw [mpure]
    simp only
    rw [mbind, mtry, mbind, rollbackTo_model rfl rfl]
    simp only
    rw [mbind, release_model rfl rfl]
    simp only
    rw [mbind, commit_model rfl]
    exact Or.inl ⟨_, rfl⟩
  | some c0 =>
    simp only
    rw [mbind, beginBody_model now opts c0 _ rfl]
    by_cases h1 : 0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)
    swap
    · rw [if_pos h1]
      simp only
      erw [mpure]
      simp only
      rw [mbind, mtry, mbind, rollbackTo_model rfl rfl]
      simp only
      rw [mbind, release_model rfl rfl]
      simp only
      rw [mbind, commit_model rfl]
      exact Or.inl ⟨_, rfl⟩
    rw [if_neg (not_not.2 h1)]
    by_cases h2 : inInt64 (nextInstant c0.lastInstant.toInt now) = true
    swap
    · rw [if_pos (by simpa using h2)]
      simp only
      rw [mbind, rollbackQuiet_model rfl]
      exact Or.inl ⟨_, rfl⟩
    rw [if_neg (by simp [h2])]
    simp only
    cases hins : st.insertTx (txRowOf c0 now) with
    | error e =>
      simp only
      rw [mbind, rollbackQuiet_model rfl]
      exact Or.inl ⟨_, rfl⟩
    | ok c =>
      have hc' := insertTx_ok hins
      subst hc'
      simp only
      rw [mbind]
      unfold runBody
      rw [interp_model]
      have hst : ModelStore.mk st { st with txs := st.txs ++ [txRowOf c0 now] } true [("spec", st)] =
          withSps (startOf st c0 now) [("spec", st)] := rfl
      rw [hst, runModel_withSps]
      have hinv := init_inv hwf hc h2
      cases hr : SProg.runModel ((body.run (ctx0Of c0 now opts)).run) (startOf st c0 now) with
      | error e =>
        simp only
        rw [mbind, rollbackQuiet_model rfl]
        exact Or.inl ⟨_, rfl⟩
      | ok p =>
        rcases p with ⟨res, σ⟩
        obtain ⟨hiσ, fr⟩ := inv_prog _ hinv hr
        have hσc : σ.committed = st := fr.1
        have hσtx : σ.inTx = true := hiσ.inTx
        have hσsp : (withSps σ [("spec", st)]).sps = [("spec", st)] := rfl
        simp only
        cases res with
        | error e =>
          simp only
          rw [mbind]
          erw [mpure]
          simp only
          rw [mbind, readIdCounters_model]
          simp only
          erw [mpure]
          simp only
          rw [mbind, mtry, mbind, rollbackTo_model (s := withSps σ [("spec", st)]) hσtx hσsp]
          simp only
          rw [mbind, release_model (s := { withSps σ [("spec", st)] with current := st }) hσtx hσsp]
          simp only
          rw [mbind, burnIds_model _ (s := { withSps σ [("spec", st)] with current := st, sps := [] }) hσtx]
          simp only
          rw [mbind]
          erw [commit_model (s := { withSps σ [("spec", st)] with current := burnSt st (idsOf σ.current), sps := [] }) hσtx]
          refine Or.inr ⟨c0, σ, .error e, .error e, rfl, hiσ, hσc, hr, rfl, rfl⟩
        | ok q =>
          rcases q with ⟨a, ctx⟩
          simp only
          rw [mbind]
          erw [hafter (afterCtx ctx c0 now opts) a (withSps σ [("spec", st)])]
          rw [show (withSps σ [("spec", st)]).current = σ.current from rfl]
          cases hg : G (afterCtx ctx c0 now opts) a σ.current with
          | error e =>
            simp only
            rw [mbind, rollbackQuiet_model rfl]
            exact Or.inl ⟨_, rfl⟩
          | ok r =>
            simp only
            rw [mbind, readIdCounters_model]
            simp only
            erw [mpure]
            simp only
            rw [mbind, mtry, mbind, rollbackTo_model (s := withSps σ [("spec", st)]) hσtx hσsp]
            simp only
            rw [mbind, release_model (s := { withSps σ [("spec", st)] with current := st }) hσtx hσsp]
            simp only
            rw [mbind, burnIds_model _ (s := { withSps σ [("spec", st)] with current := st, sps := [] }) hσtx]
            simp only
            rw [mbind]
            erw [commit_model (s := { withSps σ [("spec", st)] with current := burnSt st (idsOf σ.current), sps := [] }) hσtx]
            exact Or.inr ⟨c0, σ, .ok (a, ctx), r, rfl, hiσ, hσc, hr, rfl, hg⟩

/-! ## The result of a commit and of a dry run -/

/-- What a commit returns, from what its body computes. -/
def expected {α : Type} (now : Int) (opts : TxOptions) (body : EngM α) (st : ModelState) :
    Except Error (α × TxReport) :=
  match countersOf st with
  | none => .error (.invalidTerm .value "meta table is missing counters")
  | some c0 =>
    if ¬(0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)) then .error (.idSpaceExhausted .tx)
    else if inInt64 (nextInstant c0.lastInstant.toInt now) = false then
      .error (.store (StoreError.misuse s!"instant {nextInstant c0.lastInstant.toInt now} is outside the 64-bit range"))
    else match st.insertTx (txRowOf c0 now) with
      | .error e => .error (.store e)
      | .ok _ =>
        match SProg.runModel ((body.run (ctx0Of c0 now opts)).run) (startOf st c0 now) with
        | .error e => .error (.store e)
        | .ok (.error e, _) => .error e
        | .ok (.ok (a, ctx), _) => .ok (a, (afterCtx ctx c0 now opts).report.finish)

theorem transact_result {α : Type} (now : Int) (opts : TxOptions) (body : EngM α) (st : ModelState)
    (hwf : WF st) :
    (Model.transactE now opts body st).1 = expected now opts body st := by
  unfold Model.transactE Model.onState transactCore expected
  rw [mbind, tryBegin_model]
  simp only
  rw [mtry, mbind, loadCounters_model]
  simp only [begun]
  cases hc : countersOf st with
  | none =>
    simp only
    rw [mbind, rollbackQuiet_model rfl]
    rfl
  | some c0 =>
    simp only
    rw [mbind, beginBody_model now opts c0 _ rfl]
    by_cases h1 : 0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)
    swap
    · rw [if_pos h1, if_pos h1]; simp only; rw [mbind, rollbackQuiet_model rfl]; rfl
    rw [if_neg (not_not.2 h1), if_neg (not_not.2 h1)]
    by_cases h2 : inInt64 (nextInstant c0.lastInstant.toInt now) = true
    swap
    · rw [if_pos (by simpa using h2), if_pos (by simpa using h2)]; simp only
      rw [mbind, rollbackQuiet_model rfl]; rfl
    rw [if_neg (by simp [h2]), if_neg (by simp [h2])]
    simp only
    cases hins : st.insertTx (txRowOf c0 now) with
    | error e => simp only; rw [mbind, rollbackQuiet_model rfl]; rfl
    | ok c =>
      have hc' := insertTx_ok hins
      subst hc'
      simp only
      rw [mbind]
      unfold runBody
      rw [interp_model]
      have hst : ModelStore.mk st { st with txs := st.txs ++ [txRowOf c0 now] } true [] = startOf st c0 now := rfl
      rw [hst]
      cases hr : SProg.runModel ((body.run (ctx0Of c0 now opts)).run) (startOf st c0 now) with
      | error e => simp only; rw [mbind, rollbackQuiet_model rfl]; rfl
      | ok p =>
        rcases p with ⟨res, s3⟩
        obtain ⟨hi3, _⟩ := inv_prog _ (init_inv hwf hc h2) hr
        simp only
        cases res with
        | error e => simp only; rw [mbind, rollbackQuiet_model hi3.inTx]; rfl
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
          rfl

/-- What a speculation or dry run returns, from what its body and its follow-up compute. -/
def expectedSpec {α β : Type} (now : Int) (opts : TxOptions) (body : EngM α)
    (G : TxCtx → α → ModelState → Except StoreError (Except Error β)) (st : ModelState) : Except Error β :=
  match countersOf st with
  | none => .error (.invalidTerm .value "meta table is missing counters")
  | some c0 =>
    if ¬(0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)) then .error (.idSpaceExhausted .tx)
    else if inInt64 (nextInstant c0.lastInstant.toInt now) = false then
      .error (.store (StoreError.misuse s!"instant {nextInstant c0.lastInstant.toInt now} is outside the 64-bit range"))
    else match st.insertTx (txRowOf c0 now) with
      | .error e => .error (.store e)
      | .ok _ =>
        match SProg.runModel ((body.run (ctx0Of c0 now opts)).run) (startOf st c0 now) with
        | .error e => .error (.store e)
        | .ok (.error e, _) => .error e
        | .ok (.ok (a, ctx), σ) =>
          match G (afterCtx ctx c0 now opts) a σ.current with
          | .error e => .error (.store e)
          | .ok r => r

theorem speculative_result {α β : Type} (now : Int) (opts : TxOptions) (body : EngM α)
    (G : TxCtx → α → ModelState → Except StoreError (Except Error β))
    (after : TxCtx → α → ModelM (Except Error β))
    (hafter : ∀ ctx a s, after ctx a s = match G ctx a s.current with
      | .ok x => .ok (x, s)
      | .error e => .error e)
    (st : ModelState) (hwf : WF st) :
    (Model.onState (speculativeCore (pure now) opts body after) st).1 = expectedSpec now opts body G st := by
  unfold Model.onState speculativeCore expectedSpec
  rw [mbind, tryBegin_model]
  simp only
  rw [mtry, mbind, savepoint_model rfl]
  simp only
  rw [mbind, mbind, loadCounters_model]
  simp only [begun]
  cases hc : countersOf st with
  | none =>
    simp only
    erw [mpure]
    simp only
    rw [mbind, mtry, mbind, rollbackTo_model rfl rfl]
    simp only
    rw [mbind, release_model rfl rfl]
    simp only
    rw [mbind, commit_model rfl]
    rfl
  | some c0 =>
    simp only
    rw [mbind, beginBody_model now opts c0 _ rfl]
    by_cases h1 : 0 ≤ c0.lastT.toInt + 1 ∧ c0.lastT.toInt + 1 ≤ (counterMax : Int)
    swap
    · rw [if_pos h1, if_pos h1]
      simp only
      erw [mpure]
      simp only
      rw [mbind, mtry, mbind, rollbackTo_model rfl rfl]
      simp only
      rw [mbind, release_model rfl rfl]
      simp only
      rw [mbind, commit_model rfl]
      rfl
    rw [if_neg (not_not.2 h1), if_neg (not_not.2 h1)]
    by_cases h2 : inInt64 (nextInstant c0.lastInstant.toInt now) = true
    swap
    · rw [if_pos (by simpa using h2), if_pos (by simpa using h2)]
      simp only
      rw [mbind, rollbackQuiet_model rfl]
      rfl
    rw [if_neg (by simp [h2]), if_neg (by simp [h2])]
    simp only
    cases hins : st.insertTx (txRowOf c0 now) with
    | error e =>
      simp only
      rw [mbind, rollbackQuiet_model rfl]
      rfl
    | ok c =>
      have hc' := insertTx_ok hins
      subst hc'
      simp only
      rw [mbind]
      unfold runBody
      rw [interp_model]
      have hst : ModelStore.mk st { st with txs := st.txs ++ [txRowOf c0 now] } true [("spec", st)] =
          withSps (startOf st c0 now) [("spec", st)] := rfl
      rw [hst, runModel_withSps]
      have hinv := init_inv hwf hc h2
      cases hr : SProg.runModel ((body.run (ctx0Of c0 now opts)).run) (startOf st c0 now) with
      | error e =>
        simp only
        rw [mbind, rollbackQuiet_model rfl]
        rfl
      | ok p =>
        rcases p with ⟨res, σ⟩
        obtain ⟨hiσ, fr⟩ := inv_prog _ hinv hr
        have hσc : σ.committed = st := fr.1
        have hσtx : σ.inTx = true := hiσ.inTx
        have hσsp : (withSps σ [("spec", st)]).sps = [("spec", st)] := rfl
        simp only
        cases res with
        | error e =>
          simp only
          rw [mbind]
          erw [mpure]
          simp only
          rw [mbind, readIdCounters_model]
          simp only
          erw [mpure]
          simp only
          rw [mbind, mtry, mbind, rollbackTo_model (s := withSps σ [("spec", st)]) hσtx hσsp]
          simp only
          rw [mbind, release_model (s := { withSps σ [("spec", st)] with current := st }) hσtx hσsp]
          simp only
          rw [mbind, burnIds_model _ (s := { withSps σ [("spec", st)] with current := st, sps := [] }) hσtx]
          simp only
          rw [mbind]
          erw [commit_model (s := { withSps σ [("spec", st)] with current := burnSt st (idsOf σ.current), sps := [] }) hσtx]
          rfl
        | ok q =>
          rcases q with ⟨a, ctx⟩
          simp only
          rw [mbind]
          erw [hafter (afterCtx ctx c0 now opts) a (withSps σ [("spec", st)])]
          rw [show (withSps σ [("spec", st)]).current = σ.current from rfl]
          cases hg : G (afterCtx ctx c0 now opts) a σ.current with
          | error e =>
            simp only
            rw [mbind, rollbackQuiet_model rfl]
            rfl
          | ok r =>
            simp only
            rw [mbind, readIdCounters_model]
            simp only
            erw [mpure]
            simp only
            rw [mbind, mtry, mbind, rollbackTo_model (s := withSps σ [("spec", st)]) hσtx hσsp]
            simp only
            rw [mbind, release_model (s := { withSps σ [("spec", st)] with current := st }) hσtx hσsp]
            simp only
            rw [mbind, burnIds_model _ (s := { withSps σ [("spec", st)] with current := st, sps := [] }) hσtx]
            simp only
            rw [mbind]
            erw [commit_model (s := { withSps σ [("spec", st)] with current := burnSt st (idsOf σ.current), sps := [] }) hσtx]
            rfl


end Tiramemsu.Engine