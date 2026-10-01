/-
What each body operation does on the model store, computed from the generic implementation.
-/
import TiramemsuProofs.Store.Invariant
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## Reads -/

theorem foldWithExit_collectM (xs : List TripleRow) (acc : Array TripleRow) (s : ModelStore) :
    (foldWithExit (m := ModelM) xs acc (fun acc r => pure (.yield (acc.push r)))) s =
      .ok (acc ++ xs.toArray, s) := by
  induction xs generalizing acc with
  | nil => simp [foldWithExit]; rfl
  | cons x xs ih =>
    simp only [foldWithExit]
    rw [mbind]
    show (foldWithExit (m := ModelM) xs (acc.push x) _) s = _
    rw [ih]; simp

/-- A read on the model's writer is the read of its current state; the store is unchanged. -/
theorem read_model (r : ROp) (s : ModelStore) :
    (ROp.run r : ModelM r.Res) s = match ROp.model r s.current with
      | .ok x => .ok (x, s)
      | .error e => .error e := by
  cases r with
  | scan sp =>
    rw [ROp.model_scan]
    show (ModelState.scanM (m := ModelM) s.current sp #[] (fun acc r => pure (.yield (acc.push r)))) s = _
    unfold ModelState.scanM ModelState.scanList?
    by_cases hv : sp.valid = true
    · simp only [hv, if_true]; rw [foldWithExit_collectM]; simp
    · simp only [hv]; rfl
  | _ => rfl

theorem read_same {r : ROp} {s s' : ModelStore} {x : r.Res} (h : (ROp.run r : ModelM r.Res) s = .ok (x, s')) :
    s' = s ∧ ROp.model r s.current = .ok x := by
  rw [read_model] at h
  cases hm : ROp.model r s.current with
  | ok y => rw [hm] at h; cases h; exact ⟨rfl, rfl⟩
  | error e => rw [hm] at h; cases h

/-! ## Writes -/

theorem needCounter_spec {n : String} {s s' : ModelStore} {v : Int64}
    (h : (needCounter (m := ModelM) n) s = .ok (v, s')) : s' = s ∧ s.current.counter n = some v := by
  unfold needCounter at h
  rw [mbind, mcounter] at h
  cases hc : s.current.counter n with
  | none => simp only [hc] at h; cases h
  | some w => simp only [hc] at h; cases h; exact ⟨rfl, rfl⟩

theorem needBase_spec {n : String} {s s' : ModelStore} {v : Int64}
    (h : (needBase (m := ModelM) n) s = .ok (v, s')) : s' = s ∧ s.committed.counter n = some v := by
  unfold needBase at h
  rw [mbind, mbase] at h
  cases hc : s.committed.counter n with
  | none => simp only [hc] at h; cases h
  | some w => simp only [hc] at h; cases h; exact ⟨rfl, rfl⟩

theorem needCounter_bind {β : Type} {n : String} {f : Int64 → ModelM β} {s : ModelStore} :
    (needCounter (m := ModelM) n >>= f) s =
      match s.current.counter n with
      | some v => f v s
      | none => .error (.misuse s!"meta table is missing counter {n}") := by
  rw [mbind]
  unfold needCounter
  rw [mbind, mcounter]
  cases s.current.counter n <;> rfl

theorem needBase_bind {β : Type} {n : String} {f : Int64 → ModelM β} {s : ModelStore} :
    (needBase (m := ModelM) n >>= f) s =
      match s.committed.counter n with
      | some v => f v s
      | none => .error (.misuse s!"meta table is missing counter {n}") := by
  rw [mbind]
  unfold needBase
  rw [mbind, mbase]
  cases s.committed.counter n <;> rfl

/-- Id allocation: unchanged (out of range), or one counter raised by one. -/
theorem alloc_spec {c : IdCounter} {s s' : ModelStore} {x : Except CodecError ObjectId}
    (h : (allocRun c : ModelM _) s = .ok (x, s')) :
    s' = s ∨ (s.inTx = true ∧ ∃ n cur, s.current.counter c.name = some n ∧ 0 ≤ n.toInt ∧
      n.toInt ≤ (counterMax : Int) ∧ s.current.setCounter c.name (n + 1) = .ok cur ∧
      s' = { s with current := cur } ∧ x = .ok (mkAlloc c.allocTag 0 n.toUInt64)) := by
  unfold allocRun at h
  rw [needCounter_bind] at h
  cases hc : s.current.counter c.name with
  | none => simp only [hc] at h; cases h
  | some n =>
    simp only [hc] at h
    by_cases hr : 0 ≤ n.toInt ∧ n.toInt ≤ (counterMax : Int)
    · rw [if_pos hr, mbind, msetCounter] at h
      cases he : (WriteOp.setCounter c.name (n + 1)).exec s with
      | error e => rw [he] at h; cases h
      | ok p =>
        rcases p with ⟨u, s1⟩
        rw [he] at h
        simp only [mpure] at h
        cases h
        obtain ⟨htx, cur, hstep, rfl⟩ := data_exec rfl he
        exact Or.inr ⟨htx, n, cur, rfl, hr.1, hr.2, hstep, rfl, rfl⟩
    · rw [if_neg hr, mpure] at h; cases h; exact Or.inl rfl

/-- The guarded insert: the row appended to the current state, with `t_add = last_t + 1`. -/
theorem insert_spec {r : NewRow} {s s' : ModelStore} {u : Unit}
    (h : (insertRun r : ModelM Unit) s = .ok (u, s')) :
    ∃ lastT base next, s.committed.counter "last_t" = some lastT ∧
      s.committed.counter "next_stmt" = some base ∧ s.current.counter "next_stmt" = some next ∧
      0 ≤ lastT.toInt ∧ lastT.toInt < lastTLimit ∧ rowGuard r base next = true ∧ s.inTx = true ∧
      s.current.triples.any (·.eid == r.eid) = false ∧
      s' = { s with current := { s.current with triples := s.current.triples ++
        [{ eid := r.eid, s := r.s, p := r.p, o := r.o, tAdd := lastT + 1, vFrom := r.vFrom, vTo := r.vTo }] } } := by
  unfold insertRun at h
  rw [needBase_bind] at h
  cases h1 : s.committed.counter "last_t" with
  | none => simp only [h1] at h; cases h
  | some lastT =>
    simp only [h1] at h
    rw [needBase_bind] at h
    cases h2 : s.committed.counter "next_stmt" with
    | none => simp only [h2] at h; cases h
    | some base =>
      simp only [h2] at h
      rw [needCounter_bind] at h
      cases h3 : s.current.counter "next_stmt" with
      | none => simp only [h3] at h; cases h
      | some next =>
        simp only [h3] at h
        by_cases hg : 0 ≤ lastT.toInt ∧ lastT.toInt < lastTLimit ∧ rowGuard r base next = true
        · rw [if_pos hg, minsertTriple] at h
          obtain ⟨htx, cur, hstep, rfl⟩ := data_exec rfl h
          obtain ⟨hany, rfl⟩ := insertTriple_ok hstep
          exact ⟨lastT, base, next, rfl, rfl, rfl, hg.1, hg.2.1, hg.2.2, htx, hany, rfl⟩
        · rw [if_neg hg, mthrow] at h; cases h

/-- The retraction: unchanged when not live, else the row retracted at `last_t + 1`. -/
theorem retract_spec' {e : Int64} {k : RetKind} {s s' : ModelStore} {b : Bool}
    (h : (retractRun e k : ModelM Bool) s = .ok (b, s')) :
    ∃ lastT, s.committed.counter "last_t" = some lastT ∧ 0 ≤ lastT.toInt ∧ lastT.toInt < lastTLimit ∧
      ((b = false ∧ s' = s ∧ (∀ r, s.current.triple e = some r → r.tRet.isSome)) ∨
       (b = true ∧ s.inTx = true ∧ ∃ r, s.current.triple e = some r ∧ r.tRet = none ∧
         s' = { s with current := { s.current with triples := s.current.triples.map (retractRow e (lastT + 1) k.code) } })) := by
  unfold retractRun at h
  rw [needBase_bind] at h
  cases h1 : s.committed.counter "last_t" with
  | none => simp only [h1] at h; cases h
  | some lastT =>
    simp only [h1] at h
    by_cases hg : 0 ≤ lastT.toInt ∧ lastT.toInt < lastTLimit
    · rw [if_pos hg, mbind, mtriple] at h
      refine ⟨lastT, rfl, hg.1, hg.2, ?_⟩
      cases ht : s.current.triple e with
      | none =>
        simp only [ht, mpure] at h; cases h
        exact Or.inl ⟨rfl, rfl, fun r hr => by cases hr⟩
      | some r =>
        simp only [ht] at h
        by_cases hl : r.tRet.isNone = true
        · rw [if_pos hl, mbind, mretract] at h
          cases he : (WriteOp.retract e (lastT + 1) k.code).exec s with
          | error x => rw [he] at h; cases h
          | ok p =>
            rcases p with ⟨u, s1⟩
            rw [he] at h
            simp only [mpure] at h
            cases h
            obtain ⟨htx, cur, hstep, rfl⟩ := data_exec rfl he
            obtain ⟨_, rfl⟩ := retract_ok hstep
            exact Or.inr ⟨rfl, htx, r, rfl, by simpa using hl, rfl⟩
        · rw [if_neg hl, mpure] at h; cases h
          refine Or.inl ⟨rfl, rfl, fun r' hr' => ?_⟩
          have := Option.some.inj hr'
          subst this
          cases hr : r.tRet with
          | none => simp [hr] at hl
          | some _ => rfl
    · rw [if_neg hg, mthrow] at h; cases h

/-- Lookup-or-insert of a term: unchanged, or one term appended and `next_term` set past it. -/
theorem intern_spec {k : TermKey} {num : Option UInt64} {s s' : ModelStore} {x : Except CodecError Nat}
    (h : (internKey k num : ModelM _) s = .ok (x, s')) :
    s' = s ∨ (s.inTx = true ∧ ∃ (next : Nat) (row : TermRow) (c1 c2 : ModelState),
      ((s.current.counter "next_term").getD 1).toNatClampNeg = next ∧ next ≤ termIdMax ∧
      s.current.insertTerm row = .ok c1 ∧ c1.setCounter "next_term" (next + 1).toInt64 = .ok c2 ∧
      s' = { s with current := c2 }) := by
  unfold internKey at h
  rw [mbind, mlookupKey] at h
  cases hl : modelLookupKey s.current k with
  | some i => simp only [hl, mpure] at h; cases h; exact Or.inl rfl
  | none =>
    simp only [hl] at h
    rw [mbind] at h
    have hn : (TermBackend.nextTerm : ModelM Nat) s =
        .ok (((s.current.counter "next_term").getD 1).toNatClampNeg, s) := rfl
    rw [hn] at h
    simp only at h
    by_cases hle : ((s.current.counter "next_term").getD 1).toNatClampNeg ≤ termIdMax
    · rw [if_pos hle, mbind] at h
      have hi : ∀ (row : Row), (TermBackend.insertRow row : ModelM Unit) s =
          (WriteOp.insertTerm row.toStore).exec s := fun _ => rfl
      rw [hi] at h
      cases he : (WriteOp.insertTerm _).exec s with
      | error e => rw [he] at h; cases h
      | ok p =>
        rcases p with ⟨u, s1⟩
        rw [he] at h
        simp only at h
        rw [mbind] at h
        have hs : ∀ (n : Nat), (TermBackend.setNextTerm n : ModelM Unit) s1 =
            (WriteOp.setCounter "next_term" n.toInt64).exec s1 := fun _ => rfl
        rw [hs] at h
        cases he2 : (WriteOp.setCounter "next_term" _).exec s1 with
        | error e => rw [he2] at h; cases h
        | ok p2 =>
          rcases p2 with ⟨u2, s2⟩
          rw [he2] at h
          simp only [mpure] at h
          cases h
          obtain ⟨htx, c1, hstep, rfl⟩ := data_exec rfl he
          obtain ⟨_, c2, hstep2, rfl⟩ := data_exec rfl he2
          exact Or.inr ⟨htx, _, _, c1, c2, rfl, hle, hstep, hstep2, rfl⟩
    · rw [if_neg hle, mpure] at h; cases h; exact Or.inl rfl

theorem markMulti_spec {p : Int64} {s s' : ModelStore} {u : Unit}
    (h : (markMultiRun p : ModelM Unit) s = .ok (u, s')) :
    s' = s ∨ (s.inTx = true ∧ ∃ c1 c2 v, s.current.addPredMulti p = .ok c1 ∧
      c1.setCounter "multi_version" v = .ok c2 ∧ s' = { s with current := c2 }) := by
  unfold markMultiRun at h
  rw [mbind, mpredMulti] at h
  by_cases hp : s.current.isPredMulti p = true
  · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false, mpure] at h; cases h; exact Or.inl rfl
  · simp only [hp, Bool.not_false, if_true] at h
    rw [mbind, maddPredMulti] at h
    cases he : (WriteOp.addPredMulti p).exec s with
    | error e => rw [he] at h; cases h
    | ok q =>
      rcases q with ⟨u1, s1⟩
      rw [he] at h
      simp only at h
      rw [needCounter_bind] at h
      cases hc : s1.current.counter "multi_version" with
      | none => simp only [hc] at h; cases h
      | some v =>
        simp only [hc, msetCounter] at h
        obtain ⟨htx, c1, hstep, rfl⟩ := data_exec rfl he
        obtain ⟨_, c2, hstep2, rfl⟩ := data_exec rfl h
        exact Or.inr ⟨htx, c1, c2, _, hstep, hstep2, rfl⟩

end Tiramemsu.Engine
