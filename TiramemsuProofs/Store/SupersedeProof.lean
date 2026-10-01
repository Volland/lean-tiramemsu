/-
Supersede replays the layers. A successful supersede of a live statement `root` computes the
cascade set `C` of the root (the now-view dependents closure, root first); allocates `σ` for
`C` in cascade order; retracts every member of `C` with kind `supersede` at the current
transaction `t`; then lets the uniqueness/cardinality step retract other live statements at
`t`; appends, in cascade order, the replay of every member that is not a graph membership
(`replayRow`: new eid `σ m`, subject and object rewritten through `σ`, the patched object and
interval on the root only, `t_add = t`); appends the link `(σ root, sys:supersedes, root)`;
and returns `σ root`. Nothing else is inserted and no other row changes.
Requirement: memory-verbs / "Supersede replays the layers".
-/
import TiramemsuProofs.Store.Assert
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec Tiramemsu.View EngM

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The invariant across engine runs -/

theorem erun_inv {α : Type} {x : EngM α} {ctx : TxCtx} {s s' : ModelStore} {r : Except Error (α × TxCtx)}
    (hi : TxInv s) (h : erun x ctx s = .ok (r, s')) : TxInv s' :=
  (inv_prog _ hi h).1

theorem StandsOn_congr {a b : ModelState} (h : a.triples = b.triples) (v : View) : StandsOn a v = StandsOn b v := by
  funext x y; unfold StandsOn; rw [h]

/-- The row a replayed `NewRow` becomes at transaction `t`. -/
def NewRow.toRow (n : NewRow) (t : Int64) : TripleRow :=
  { eid := n.eid, s := n.s, p := n.p, o := n.o, tAdd := t, vFrom := n.vFrom, vTo := n.vTo }

/-! ## The loops of a supersede -/

theorem loop_alloc : ∀ (L : List Int64) (σ0 : Sigma) (c : TxCtx) (s : ModelStore) (σ' : Sigma) (c' : TxCtx)
    (s' : ModelStore),
    erun (forIn (L.map (⟨·⟩ : Int64 → ObjectId)) σ0 fun m (σ : Sigma) => allocEid >>= fun e =>
      (pure (ForInStep.yield (σ ++ [(m.raw, e.raw)])) : EngM (ForInStep Sigma))) c s = .ok (.ok (σ', c'), s') →
    σ'.map (·.1) = σ0.map (·.1) ++ L
  | [], σ0, c, s, σ', c', s', h => by
    simp only [List.map_nil, List.forIn_nil, erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h; simp
  | m :: L, σ0, c, s, σ', c', s', h => by
    rw [List.map_cons, List.forIn_cons, erun_bind, erun_bind] at h
    cases ha : erun allocEid c s with
    | error e => rw [ha] at h; cases h
    | ok q =>
      rcases q with ⟨q, s1⟩
      rcases q with e | ⟨e, c1⟩
      · rw [ha] at h; cases h
      · rw [ha] at h
        simp only [erun_pure] at h
        have := loop_alloc L _ c1 s1 σ' c' s' h
        rw [this]; simp

/-- The body of the loop collecting the cascade members' rows. -/
def rowsBody (m : ObjectId) (rows : List TripleRow) : EngM (ForInStep (List TripleRow)) := do
  match ← rd (.triple m.raw) with
  | some r => pure (.yield (rows ++ [r]))
  | none => do
    throw (Error.store (StoreError.misuse "cascade member vanished"))
    pure (.yield rows)

theorem loop_rows : ∀ (L : List Int64) (acc : List TripleRow) (c : TxCtx) (s : ModelStore) (rows : List TripleRow)
    (c' : TxCtx) (s' : ModelStore),
    erun (forIn (L.map (⟨·⟩ : Int64 → ObjectId)) acc rowsBody) c s = .ok (.ok (rows, c'), s') →
    s' = s ∧ ∃ new, rows = acc ++ new ∧ new.map (·.eid) = L ∧ ∀ r ∈ new, s.current.triple r.eid = some r
  | [], acc, c, s, rows, c', s', h => by
    simp only [List.map_nil, List.forIn_nil, erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h
    exact ⟨rfl, [], by simp, rfl, by simp⟩
  | m :: L, acc, c, s, rows, c', s', h => by
    rw [List.map_cons, List.forIn_cons, erun_bind] at h
    unfold rowsBody at h
    rw [erun_bind, erun_rd, ROp.model_triple] at h
    simp only [] at h
    cases ht : s.current.triple m with
    | none =>
      rw [ht] at h
      simp only [erun_bind, erun_throw] at h
      cases h
    | some r =>
      rw [ht] at h
      simp only [erun_pure] at h
      obtain ⟨rfl, new, rfl, hm, hall⟩ := loop_rows L (acc ++ [r]) c s rows c' s' h
      obtain ⟨-, he⟩ := triple_some ht
      refine ⟨rfl, r :: new, by simp, by simp [hm, he], ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [he]; exact ht
      · exact hall x hx

theorem cascadeKind_supersede (root e : Int64) : cascadeKind .supersede root e = .supersede := by
  unfold cascadeKind; split <;> rfl

theorem loop_retract_sup : ∀ (L : List Int64) (root : Int64) (c : TxCtx) (s : ModelStore) (u : PUnit) (c' : TxCtx)
    (s' : ModelStore),
    L.Nodup → (s.current.triples.Pairwise fun a b => a.eid ≠ b.eid) →
    (∀ e ∈ L, ∃ r ∈ s.current.triples, r.eid = e ∧ r.tRet = none) →
    erun (forIn (L.map (⟨·⟩ : Int64 → ObjectId)) PUnit.unit fun m (_ : PUnit) =>
      EngM.retractRow m .supersede >>= fun _ => (pure (ForInStep.yield PUnit.unit) : EngM (ForInStep PUnit)))
      c s = .ok (.ok (u, c'), s') →
    ∃ lt, (L ≠ [] → s.committed.counter "last_t" = some lt) ∧
      s' = { s with current := { s.current with
        triples := s.current.triples.map (retractSet L (lt + 1) .supersede root) } }
  | [], root, c, s, u, c', s', _, _, _, h => by
    simp only [List.map_nil, List.forIn_nil, erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨0, fun h => absurd rfl h, ?_⟩
    rw [retractSet_nil]
  | e :: L, root, c, s, u, c', s', hnd, hu, hlive, h => by
    rw [List.map_cons, List.forIn_cons, erun_bind, erun_bind] at h
    obtain ⟨he, hnd'⟩ := List.nodup_cons.1 hnd
    cases hs : erun (EngM.retractRow ⟨e⟩ .supersede) c s with
    | error x => rw [hs] at h; cases h
    | ok p =>
      rcases p with ⟨r1, s1⟩
      rcases r1 with x | ⟨d, c1⟩
      · rw [hs] at h; cases h
      · rw [hs] at h
        simp only [erun_pure] at h
        obtain ⟨r0, hr0, he0, hn0⟩ := hlive e (List.mem_cons_self ..)
        obtain ⟨lt, hlt, hs1⟩ := retractRow_live hu hs hr0 he0 hn0
        have hu1 : s1.current.triples.Pairwise fun a b => a.eid ≠ b.eid := by rw [hs1]; exact retractIn_uniq hu _ _ _
        have hlive1 : ∀ x ∈ L, ∃ r ∈ s1.current.triples, r.eid = x ∧ r.tRet = none := by
          intro x hx
          rw [hs1]
          exact retractIn_live (fun h => he (by have h' : x = e := h; rw [← h']; exact hx))
            (hlive x (List.mem_cons_of_mem _ hx))
        obtain ⟨lt', hlt', hs'⟩ := loop_retract_sup L root c1 s1 u c' s' hnd' hu1 hlive1 h
        refine ⟨lt, fun _ => hlt, ?_⟩
        have hrest : s1.current.triples.map (retractSet L (lt' + 1) .supersede root) =
            s1.current.triples.map (retractSet L (lt + 1) .supersede root) := by
          by_cases hL : L = []
          · subst hL; rw [retractSet_nil, retractSet_nil]
          · have h3 := hlt' hL
            rw [hs1] at h3
            have h4 : s.committed.counter "last_t" = some lt' := h3
            rw [hlt] at h4; cases h4; rfl
        rw [hs', hrest, hs1]
        unfold retractIn
        simp only []
        have hm := map_retractSet_cons (kind := .supersede) (root := root) (t := lt + 1) he s.current.triples
        rw [cascadeKind_supersede] at hm
        rw [hm]

/-- Whether a row is a graph membership, given the id of `sys:inGraph` (if interned). -/
def isMember (ig : Option ObjectId) (r : TripleRow) : Bool := ig.any (·.raw == r.p)

/-- The body of the replay loop. -/
def replayBody (ig : Option ObjectId) (σ : Sigma) (root newO : Int64) (newValid : Valid) (r : TripleRow)
    (_ : PUnit) : EngM (ForInStep PUnit) := do
  if ig.any (·.raw == r.p) then return .yield PUnit.unit
  let n := replayRow σ root newO newValid r
  if n.s == n.eid || n.o == n.eid then fail (.selfReference ⟨n.eid⟩)
  insertRow ⟨n.eid⟩ ⟨n.s⟩ ⟨n.p⟩ ⟨n.o⟩ ⟨n.vFrom, n.vTo⟩
  report fun x => { x with superseded := x.superseded.push (⟨r.eid⟩, ⟨n.eid⟩) }
  pure (.yield PUnit.unit)

theorem loop_replay (ig : Option ObjectId) (σ : Sigma) (root newO : Int64) (newValid : Valid) :
    ∀ (rows : List TripleRow) (c : TxCtx) (s : ModelStore) (u : PUnit) (c' : TxCtx) (s' : ModelStore),
    erun (forIn rows PUnit.unit (replayBody ig σ root newO newValid)) c s = .ok (.ok (u, c'), s') →
    ∃ lt, (rows.filter (fun r => !isMember ig r) ≠ [] → s.committed.counter "last_t" = some lt) ∧
      s'.committed = s.committed ∧
      s'.current.triples = s.current.triples ++
        (rows.filter (fun r => !isMember ig r)).map fun r => (replayRow σ root newO newValid r).toRow (lt + 1)
  | [], c, s, u, c', s', h => by
    simp only [List.forIn_nil, erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨0, fun h => absurd rfl h, rfl, by simp⟩
  | r :: rows, c, s, u, c', s', h => by
    rw [List.forIn_cons, erun_bind] at h
    unfold replayBody at h
    by_cases hm : ig.any (·.raw == r.p) = true
    · rw [if_pos hm, erun_pure] at h
      simp only [] at h
      obtain ⟨lt, hlt, hc, hrows⟩ := loop_replay ig σ root newO newValid rows c s u c' s' h
      have hf : (r :: rows).filter (fun r => !isMember ig r) = rows.filter (fun r => !isMember ig r) := by
        rw [List.filter_cons_of_neg]; simp [isMember, hm]
      exact ⟨lt, by rw [hf]; exact hlt, hc, by rw [hf]; exact hrows⟩
    · rw [if_neg hm] at h
      simp only [] at h
      by_cases hsr : ((replayRow σ root newO newValid r).s == (replayRow σ root newO newValid r).eid ||
          (replayRow σ root newO newValid r).o == (replayRow σ root newO newValid r).eid) = true
      · rw [if_pos hsr, erun_bind, erun_fail] at h; simp only [] at h; cases h
      · rw [if_neg hsr, erun_bind] at h
        cases hi : erun (insertRow ⟨(replayRow σ root newO newValid r).eid⟩ ⟨(replayRow σ root newO newValid r).s⟩
            ⟨(replayRow σ root newO newValid r).p⟩ ⟨(replayRow σ root newO newValid r).o⟩
            ⟨(replayRow σ root newO newValid r).vFrom, (replayRow σ root newO newValid r).vTo⟩) c s with
        | error x => rw [hi] at h; cases h
        | ok q =>
          rcases q with ⟨q, s1⟩
          rcases q with x | ⟨u1, c1⟩
          · rw [hi] at h; cases h
          · rw [hi] at h
            simp only [erun_bind, erun_report, erun_pure] at h
            obtain ⟨lt, hlt, hany, hc1, hrows1⟩ := insertRow_spec hi
            obtain ⟨lt', hlt', hc, hrows⟩ := loop_replay ig σ root newO newValid rows _ s1 u c' s' h
            have hf : (r :: rows).filter (fun r => !isMember ig r) = r :: rows.filter (fun r => !isMember ig r) := by
              rw [List.filter_cons_of_pos]; simp [isMember, hm]
            refine ⟨lt, fun _ => hlt, hc.trans hc1, ?_⟩
            have hsame : rows.filter (fun r => !isMember ig r) ≠ [] → lt' = lt := by
              intro hne
              have := hlt' hne
              rw [hc1, hlt] at this
              exact (Option.some.inj this).symm
            rw [hf, hrows, hrows1]
            by_cases hne : rows.filter (fun r => !isMember ig r) = []
            · rw [hne]; simp [newRowAt, NewRow.toRow]
            · rw [hsame hne]; simp [newRowAt, NewRow.toRow]

/-! ## The cascade-and-replay core -/

/-- The part of `supersede` after the checks of the new root content (definitionally the
continuation in `EngM.supersede`). -/
def supCore (root s p newO : ObjectId) (newValid : Valid) (b : Bool) : EngM ObjectId := do
  let set ← cascadeSet root
  let mut σ : Sigma := []
  for m in set do
    let e ← allocEid
    σ := σ ++ [(m.raw, e.raw)]
  let newRoot : ObjectId := ⟨σ.apply root.raw⟩
  if newO == newRoot then fail (.selfReference newRoot)
  let mut rows := []
  for m in set do
    match ← rd (.triple m.raw) with
    | some r => rows := rows ++ [r]
    | none => throw (.store (.misuse "cascade member vanished"))
  for m in set do
    let _ ← retractRow m .supersede
  uniqueAndCardinality s p newO newValid b
  let inGraph ← sysLookup Vocab.sysInGraph
  for r in rows do
    if inGraph.any (·.raw == r.p) then continue
    let n := replayRow σ root.raw newO.raw newValid r
    if n.s == n.eid || n.o == n.eid then fail (.selfReference ⟨n.eid⟩)
    insertRow ⟨n.eid⟩ ⟨n.s⟩ ⟨n.p⟩ ⟨n.o⟩ ⟨n.vFrom, n.vTo⟩
    report fun x => { x with superseded := x.superseded.push (⟨r.eid⟩, ⟨n.eid⟩) }
  let linkP ← sys Vocab.sysSupersedes
  let link ← allocEid
  insertRow link newRoot linkP root Valid.always
  pure newRoot

/-- What a successful cascade-and-replay does to the statement rows. -/
def ReplayOutcome (s s' : ModelStore) (root newO : ObjectId) (newValid : Valid) (nr : ObjectId) : Prop :=
  ∃ (C : List Int64) (σ : Sigma) (rows : List TripleRow) (ig : Option ObjectId) (lastT : Int64)
    (pre : List TripleRow) (link : TripleRow),
    s.committed.counter "last_t" = some lastT ∧
    C.Nodup ∧ C.head? = some root.raw ∧ (∀ x, x ∈ C ↔ Relation.ReflTransGen (StandsOn s.current {}) x root.raw) ∧
    σ.map (·.1) = C ∧ nr = ⟨σ.apply root.raw⟩ ∧
    rows.map (·.eid) = C ∧ (∀ r ∈ rows, s.current.triple r.eid = some r) ∧
    List.Forall₂ (RetStep (lastT + 1)) (s.current.triples.map (retractSet C (lastT + 1) .supersede root.raw)) pre ∧
    s'.current.triples = pre ++
      (rows.filter (fun r => !isMember ig r)).map (fun r => (replayRow σ root.raw newO.raw newValid r).toRow (lastT + 1)) ++
      [link] ∧
    link.s = σ.apply root.raw ∧ link.o = root.raw ∧ link.tAdd = lastT + 1 ∧ link.tRet = none ∧
    link.vFrom = none ∧ link.vTo = none ∧ s'.committed = s.committed

theorem supCore_spec {s s' : ModelStore} (hi : TxInv s) {root sx px newO : ObjectId} {newValid : Valid} {b : Bool}
    {r0 : TripleRow} (hr0 : r0 ∈ s.current.triples) (he0 : r0.eid = root.raw) (hn0 : r0.tRet = none)
    {c c' : TxCtx} {nr : ObjectId} (h : erun (supCore root sx px newO newValid b) c s = .ok (.ok (nr, c'), s')) :
    ReplayOutcome s s' root newO newValid nr := by
  unfold supCore at h
  dsimp only at h
  obtain ⟨o, hnd, hhd, hmem, hcs⟩ := cascadeSet_spec hi.bounded c (root := root) (List.mem_map.2 ⟨r0, hr0, he0⟩)
  rw [erun_bind, hcs] at h
  by_cases hlim : c.opts.maxCascade < o.length
  · rw [if_pos hlim] at h; cases h
  rw [if_neg hlim] at h
  simp only [] at h
  -- σ
  rw [erun_bind] at h
  split at h
  case h_2 | h_3 => cases h
  rename_i σ c1 s1 hal
  have hσ := loop_alloc o [] c s σ c1 s1 hal
  simp only [List.map_nil, List.nil_append] at hσ
  have hs1 : SameRows s s1 := LightE.rows (EOps.forIn_list _ _ fun _ _ => by repeat fp_step) hal
  have hi1 := erun_inv hi hal
  by_cases hsr : (newO == (⟨σ.apply root.raw⟩ : ObjectId)) = true
  · rw [if_pos hsr, erun_bind, erun_fail] at h; simp only [] at h; cases h
  rw [if_neg hsr] at h
  -- rows
  rw [erun_bind] at h
  split at h
  case h_2 | h_3 => cases h
  rename_i rows c2 s2 hrw
  obtain ⟨rfl, new, hnew, hrm, hrt⟩ := loop_rows o [] c1 s1 rows c2 s2 hrw
  simp only [List.nil_append] at hnew
  subst hnew
  -- retractions
  rw [erun_bind] at h
  split at h
  case h_2 | h_3 => cases h
  rename_i u3 c3 s3 hrt3
  have hlive : ∀ e ∈ o, ∃ r ∈ s2.current.triples, r.eid = e ∧ r.tRet = none := by
    intro e he
    rw [hs1.1]
    rcases Relation.ReflTransGen.cases_head ((hmem e).1 he) with h' | ⟨c, hc, _⟩
    · exact ⟨r0, hr0, he0.trans h'.symm, hn0⟩
    · obtain ⟨r, hr, hre, ha, _⟩ := hc
      exact ⟨r, hr, hre, (admits_now r).1 ha⟩
  obtain ⟨lt, hlt, hs3⟩ := loop_retract_sup o root.raw c2 s2 u3 c3 s3 hnd hi1.uniq hlive hrt3
  have hne : o ≠ [] := by intro h; rw [h] at hhd; cases hhd
  have hlt0 : s.committed.counter "last_t" = some lt := by rw [← hs1.2]; exact hlt hne
  have hi3 := erun_inv hi1 hrt3
  -- uniqueness and cardinality
  obtain ⟨_, c4, s4, hux, hrel4, h⟩ := noIns_peel h (noIns_uniqueAndCardinality _ _ _ _ _)
  obtain ⟨⟨hc4, hf4⟩, -⟩ := hrel4 hi3.uniq
  -- the id of sys:inGraph
  obtain ⟨ig, c5, s5, -, hs5, h⟩ := light_peel (SameRows.refl s4) h (light_sysLookup _)
  -- replays
  rw [erun_bind] at h
  split at h
  case h_2 | h_3 => cases h
  rename_i u6 c6 s6 hrp
  obtain ⟨lt6, hlt6, hc6, hrows6⟩ := loop_replay ig σ root.raw newO.raw newValid rows c5 s5 u6 c6 s6 hrp
  -- the link
  obtain ⟨lp, c7, s7, -, hs7, h⟩ := light_peel (SameRows.refl s6) h (light_sys _)
  obtain ⟨lk, c8, s8, -, hs8, h⟩ := light_peel hs7 h light_allocEid
  rw [erun_bind] at h
  split at h
  case h_2 | h_3 => cases h
  rename_i u9 c9 s9 hlk
  obtain ⟨lt9, hlt9, -, hc9, hrows9⟩ := insertRow_spec hlk
  simp only [erun_pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  -- committed states and transaction numbers
  have hc3 : s3.committed = s.committed := by rw [hs3]; exact hs1.2
  have hcs5 : s5.committed = s.committed := hs5.2.trans (hc4.trans hc3)
  have hcs8 : s8.committed = s.committed := hs8.2.trans (hc6.trans hcs5)
  have e9 : lt9 = lt := by rw [hcs8, hlt0] at hlt9; exact (Option.some.inj hlt9).symm
  have ht3 : tOf s3 = lt + 1 := by unfold tOf; rw [hc3, hlt0]; rfl
  have hrep : (rows.filter (fun r => !isMember ig r)).map
        (fun r => (replayRow σ root.raw newO.raw newValid r).toRow (lt6 + 1)) =
      (rows.filter (fun r => !isMember ig r)).map
        (fun r => (replayRow σ root.raw newO.raw newValid r).toRow (lt + 1)) := by
    by_cases hne6 : rows.filter (fun r => !isMember ig r) = []
    · rw [hne6]; rfl
    · have := hlt6 hne6
      rw [hcs5, hlt0] at this
      rw [Option.some.inj this]
  refine ⟨o, σ, rows, ig, lt, s4.current.triples, newRowAt lk ⟨σ.apply root.raw⟩ lp root Valid.always (lt + 1),
    hlt0, hnd, hhd, hmem, hσ, rfl, hrm, fun r hr => by rw [← hs1.1] at *; exact (by
      have := hrt r hr; unfold ModelState.triple at this ⊢; rw [hs1.1] at this; exact this), ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, hc9.trans hcs8⟩
  · have : s3.current.triples = s.current.triples.map (retractSet o (lt + 1) .supersede root.raw) := by
      rw [hs3]; simp only []; rw [hs1.1]
    rw [← this, ← ht3]; exact hf4
  · rw [hrows9, e9, hs8.1, hrows6, hrep, hs5.1]


/-! ## Supersede -/

/-- `supersede` after the new object is known (definitionally its continuation). -/
def supRest (root : ObjectId) (patch : Patch) (row : TripleRow) (newO : ObjectId) : EngM ObjectId := do
  let newValid : Valid := { vFrom := patch.vFrom.getD row.vFrom, vTo := patch.vTo.getD row.vTo }
  if !newValid.nonempty then fail (.invalidPatch "empty interval")
  if newO.raw == row.o && newValid == ⟨row.vFrom, row.vTo⟩ then fail (.invalidPatch "no change")
  let s : ObjectId := ⟨row.s⟩
  let p : ObjectId := ⟨row.p⟩
  checkPositions s p newO
  let pIri := (← iriOf p).getD ""
  EngM.ofExcept (checkReserved pIri (← tagOf s))
  let flag := Flag.ofIri pIri
  match flag with
  | some f =>
    validateFlag f p s newO
    validateSchemaChange f s newO (some root)
  | none => checkValueType p newO
  supCore root s p newO newValid (flag.any Flag.singleValued)

/-- `supersede` after the root row is known. -/
def supRow (root : ObjectId) (patch : Patch) (row : TripleRow) : EngM ObjectId := do
  let newO ← match patch.o with
    | some v => internValue v
    | none => pure ⟨row.o⟩
  supRest root patch row newO

theorem ReplayOutcome.of_same {s0 s s' : ModelStore} (hs : SameRows s0 s) {root newO : ObjectId} {newValid : Valid}
    {nr : ObjectId} (h : ReplayOutcome s s' root newO newValid nr) : ReplayOutcome s0 s' root newO newValid nr := by
  have e1 : s.current.triples = s0.current.triples := hs.1
  have e2 : s.committed = s0.committed := hs.2
  obtain ⟨C, σ, rows, ig, lastT, pre, link, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨C, σ, rows, ig, lastT, pre, link, by rw [← e2]; exact h1, h2, h3, ?_, h5, h6, h7, ?_, by rw [← e1]; exact h9,
    h10, by rw [← e2]; exact h11⟩
  · rw [← StandsOn_congr e1]; exact h4
  · intro r hr; have := h8 r hr; unfold ModelState.triple at this ⊢; rw [← e1]; exact this

theorem supRest_spec {s0 s' : ModelStore} (hi : TxInv s0) {root : ObjectId} {patch : Patch} {row : TripleRow}
    (hrow : row ∈ s0.current.triples) (hre : row.eid = root.raw) (hrl : row.tRet = none) {newO : ObjectId}
    {c c' : TxCtx} {nr : ObjectId} (h : erun (supRest root patch row newO) c s0 = .ok (.ok (nr, c'), s')) :
    ReplayOutcome s0 s' root newO ⟨patch.vFrom.getD row.vFrom, patch.vTo.getD row.vTo⟩ nr := by
  unfold supRest at h
  dsimp only at h
  split at h
  · rw [erun_bind, erun_fail] at h; simp only [] at h; cases h
  split at h
  · rw [erun_bind, erun_fail] at h; simp only [] at h; cases h
  obtain ⟨_, _, _, e1, hs, h⟩ := light_peel (SameRows.refl s0) h (light_checkPositions _ _ _)
  have hi1 := erun_inv hi e1
  obtain ⟨_, _, _, e2, hs, h⟩ := light_peel hs h (light_iriOf _)
  have hi2 := erun_inv hi1 e2
  obtain ⟨_, _, _, e3, hs, h⟩ := light_peel hs h (light_tagOf _ _)
  have hi3 := erun_inv hi2 e3
  obtain ⟨_, _, _, e4, hs, h⟩ := light_peel hs h (EOps.ofExcept _)
  have hi4 := erun_inv hi3 e4
  split at h
  · obtain ⟨_, _, _, e5, hs, h⟩ := light_peel hs h (light_validateFlag _ _ _ _)
    have hi5 := erun_inv hi4 e5
    obtain ⟨_, _, _, e6, hs, h⟩ := light_peel hs h (light_validateSchemaChange _ _ _ _)
    have hi6 := erun_inv hi5 e6
    exact ReplayOutcome.of_same hs (supCore_spec hi6 (by rw [hs.1]; exact hrow) hre hrl h)
  · obtain ⟨_, _, _, e5, hs, h⟩ := light_peel hs h (light_checkValueType _ _)
    have hi5 := erun_inv hi4 e5
    exact ReplayOutcome.of_same hs (supCore_spec hi5 (by rw [hs.1]; exact hrow) hre hrl h)

theorem supRow_spec {s0 s' : ModelStore} (hi : TxInv s0) {root : ObjectId} {patch : Patch} {row : TripleRow}
    (hrow : row ∈ s0.current.triples) (hre : row.eid = root.raw) (hrl : row.tRet = none)
    {c c' : TxCtx} {nr : ObjectId} (h : erun (supRow root patch row) c s0 = .ok (.ok (nr, c'), s')) :
    ∃ newO : ObjectId, (patch.o = none → newO = ⟨row.o⟩) ∧
      ReplayOutcome s0 s' root newO ⟨patch.vFrom.getD row.vFrom, patch.vTo.getD row.vTo⟩ nr := by
  unfold supRow at h
  dsimp only at h
  split at h
  · rename_i v hp
    obtain ⟨newO, _, _, e1, hs, h⟩ := light_peel (SameRows.refl s0) h (light_internValue _ _)
    have hi1 := erun_inv hi e1
    exact ⟨newO, (fun h' => by rw [hp] at h'; cases h'),
      ReplayOutcome.of_same hs (supRest_spec hi1 (by rw [hs.1]; exact hrow) hre hrl h)⟩
  · rename_i hp
    rw [erun_bind, erun_pure] at h
    exact ⟨⟨row.o⟩, fun _ => rfl, supRest_spec hi hrow hre hrl h⟩

theorem supersede_eqn (root : ObjectId) (patch : Patch) :
    supersede root patch = (originOk root >>= fun _ => rd (.triple root.raw) >>= fun x =>
      match x with
      | some r => if r.tRet.isNone then (pure r >>= supRow root patch) else (fail (.notLive root) >>= supRow root patch)
      | none => fail (.notLive root) >>= supRow root patch) := rfl

/-- Supersede replays the layers: a successful supersede of `root` with a patch finds `root`
live, and then (with `newO` the patched object, the old one when the patch has none, and the
patched interval) retracts exactly its cascade set with kind `supersede` at the current
transaction, lets uniqueness/cardinality retract other live rows at that transaction, appends
the replays of the non-membership members in cascade order (subject and object through `σ`,
the patch on the root only) and the link `(σ root, sys:supersedes, root)`, and returns
`σ root`. -/
theorem supersede_spec {s0 s' : ModelStore} (hi : TxInv s0) {root : ObjectId} {patch : Patch}
    {ctx c' : TxCtx} {nr : ObjectId} (h : erun (supersede root patch) ctx s0 = .ok (.ok (nr, c'), s')) :
    ∃ row : TripleRow, s0.current.triple root.raw = some row ∧ row.tRet = none ∧
      ∃ newO : ObjectId, (patch.o = none → newO = ⟨row.o⟩) ∧
        ReplayOutcome s0 s' root newO ⟨patch.vFrom.getD row.vFrom, patch.vTo.getD row.vTo⟩ nr := by
  rw [supersede_eqn] at h
  obtain ⟨_, _, _, e1, hs, h⟩ := light_peel (SameRows.refl s0) h (light_originOk _)
  have hi1 := erun_inv hi e1
  obtain ⟨x, c2, s2, e2, hs2, h⟩ := light_peel hs h (EOps.rd _ rfl)
  rw [erun_rd, ROp.model_triple] at e2
  simp only [Except.ok.injEq, Prod.mk.injEq] at e2
  obtain ⟨⟨hx, -⟩, hse⟩ := e2
  subst hse
  have ht : s0.current.triple root.raw = x := by
    rw [← hx]; unfold ModelState.triple; rw [hs.1]
  split at h
  · rename_i r
    by_cases hl : r.tRet.isNone = true
    · rw [if_pos hl, erun_bind, erun_pure] at h
      have hl' : r.tRet = none := by simpa [Option.isNone_iff_eq_none] using hl
      obtain ⟨hr, he⟩ := triple_some ht
      obtain ⟨newO, hno, hout⟩ := supRow_spec hi1 (by rw [hs.1]; exact hr) he hl' h
      exact ⟨r, ht, hl', newO, hno, ReplayOutcome.of_same hs hout⟩
    · rw [if_neg hl, erun_bind, erun_fail] at h; cases h
  · rw [erun_bind, erun_fail] at h; cases h

end Tiramemsu.Engine
