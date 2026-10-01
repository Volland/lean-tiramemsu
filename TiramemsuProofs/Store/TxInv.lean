/-
The invariant of a running transaction body, and its preservation by every body operation and
hence (by induction on `SProg`) by every body program.
Requirement: statement-lifecycle (the never-forget invariant, per operation and per program).
-/
import TiramemsuProofs.Store.OpSpec
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-- The invariant while a body runs: in a transaction over a well-formed committed state; the
transaction's `tx` row appended with an instant after the last one; `last_t` and `last_instant`
untouched; the current state extends the committed one; every statement `RowOK` for this
transaction's number. -/
structure TxInv (s : ModelStore) : Prop where
  inTx : s.inTx = true
  wf : WF s.committed
  lastTEq : s.current.counter "last_t" = s.committed.counter "last_t"
  lastIEq : s.current.counter "last_instant" = s.committed.counter "last_instant"
  txs : ∃ inst : Int64, s.current.txs = s.committed.txs ++ [⟨Int64.ofInt (lastT s.committed + 1), inst⟩] ∧
    lastInstant s.committed < inst.toInt
  ext : Extends s.committed s.current
  rows : ∀ r ∈ s.current.triples, RowOK (lastT s.committed + 1) (nextStmt s.current) r
  uniq : s.current.triples.Pairwise fun a b => a.eid ≠ b.eid
  present : ∀ n v, s.committed.counter n = some v → ∃ w, s.current.counter n = some w

/-- What a body operation keeps: the committed state, the flag and the savepoints. -/
def Frame (s s' : ModelStore) : Prop :=
  s'.committed = s.committed ∧ s'.inTx = s.inTx ∧ s'.sps = s.sps ∧ s'.current.txs = s.current.txs

theorem setCounter_txs {st c : ModelState} {n : String} {v : Int64} (h : st.setCounter n v = .ok c) :
    c.txs = st.txs := by
  unfold ModelState.setCounter at h; cases h; rfl

theorem ctr_of_some {st : ModelState} {n : String} {v : Int64} (h : st.counter n = some v) : ctr st n = v.toInt := by
  simp [ctr, h]

theorem retKind_code (k : RetKind) : 0 ≤ k.code.toInt ∧ k.code.toInt ≤ 3 := by
  cases k <;> decide

/-! ## Counter writes -/

/-- A counter write that leaves `last_t` and `last_instant` and does not lower an id counter. -/
theorem inv_setCounter {s : ModelStore} {n : String} {v : Int64} {c : ModelState}
    (hi : TxInv s) (hc : s.current.setCounter n v = .ok c)
    (hn : n ≠ "last_t" ∧ n ≠ "last_instant") (hmono : n ∈ idNames → ctr s.current n ≤ v.toInt) :
    TxInv { s with current := c } := by
  have hcnt := fun m => counter_setCounter s.current n m v c hc
  have htrip : c.triples = s.current.triples := by unfold ModelState.setCounter at hc; cases hc; rfl
  have hterms : c.terms = s.current.terms := by unfold ModelState.setCounter at hc; cases hc; rfl
  have htxs : c.txs = s.current.txs := by unfold ModelState.setCounter at hc; cases hc; rfl
  have hctr : ∀ m, m ≠ n → ctr c m = ctr s.current m := by intro m hm; simp [ctr, hcnt m, hm]
  have hmono' : ∀ m ∈ idNames, ctr s.current m ≤ ctr c m := by
    intro m hm
    by_cases hmn : m = n
    · subst hmn; rw [show ctr c m = v.toInt by simp [ctr, hcnt m]]; exact hmono hm
    · rw [hctr m hmn]
  have hnext : nextStmt s.current ≤ nextStmt c := hmono' "next_stmt" (by simp [idNames])
  obtain ⟨pre, new, hb, f, nw⟩ := hi.ext.rows
  refine ⟨hi.inTx, hi.wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c.counter "last_t" = _; rw [hcnt, if_neg (Ne.symm hn.1)]; exact hi.lastTEq
  · show c.counter "last_instant" = _; rw [hcnt, if_neg (Ne.symm hn.2)]; exact hi.lastIEq
  · show ∃ inst, c.txs = _ ∧ _; rw [htxs]; exact hi.txs
  · refine ⟨⟨pre, new, by show c.triples = _; rw [htrip, hb], f, nw⟩, by show _ <+: c.terms; rw [hterms]; exact hi.ext.terms,
      by show _ <+: c.txs; rw [htxs]; exact hi.ext.txs, fun m hm => le_trans (hi.ext.ids m hm) (hmono' m hm), ?_⟩
    have : lastT c = lastT s.current := by
      show ctr c "last_t" = ctr s.current "last_t"; exact hctr _ (Ne.symm hn.1)
    show lastT s.committed ≤ lastT c; rw [this]; exact hi.ext.lastT
  · intro r hr
    change r ∈ c.triples at hr
    rw [htrip] at hr
    exact (hi.rows r hr).mono le_rfl hnext
  · show c.triples.Pairwise _; rw [htrip]; exact hi.uniq
  · intro m w hw
    show ∃ x, c.counter m = some x
    rw [hcnt m]
    split
    · exact ⟨v, rfl⟩
    · exact hi.present m w hw

/-! ## Each operation -/

theorem inv_alloc {c : IdCounter} {s s' : ModelStore} {x : Except CodecError ObjectId} (hi : TxInv s)
    (h : (allocRun c : ModelM _) s = .ok (x, s')) : TxInv s' ∧ Frame s s' := by
  rcases alloc_spec h with rfl | ⟨_, n, cur, hn, h0, hmax, hset, rfl, _⟩
  · exact ⟨hi, rfl, rfl, rfl, rfl⟩
  · refine ⟨inv_setCounter hi hset (by cases c <;> decide) ?_, rfl, rfl, rfl, setCounter_txs hset⟩
    intro _
    rw [ctr_of_some hn]
    have : (counterMax : Int) < 2 ^ 63 - 1 := by unfold counterMax; norm_num
    rw [toInt_add_one (by omega) (by omega)]; omega

theorem inv_insert {r : NewRow} {s s' : ModelStore} {u : Unit} (hi : TxInv s)
    (h : (insertRun r : ModelM Unit) s = .ok (u, s')) : TxInv s' ∧ Frame s s' := by
  obtain ⟨lastT', base, next, h1, h2, h3, hl0, hl1, hg, htx, hany, rfl⟩ := insert_spec h
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  set row : TripleRow := { eid := r.eid, s := r.s, p := r.p, o := r.o, tAdd := lastT' + 1, vFrom := r.vFrom, vTo := r.vTo }
  have hT : lastT s.committed = lastT'.toInt := ctr_of_some h1
  have hB : nextStmt s.committed = base.toInt := ctr_of_some h2
  have hN : nextStmt s.current = next.toInt := ctr_of_some h3
  have htAdd : row.tAdd.toInt = lastT'.toInt + 1 := by
    show (lastT' + 1).toInt = _
    have : lastTLimit < 2 ^ 63 - 1 := by unfold lastTLimit; norm_num
    exact toInt_add_one (by omega) (by omega)
  -- the guard, unpacked
  simp only [rowGuard, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htag, hlo⟩, hhi⟩, hs0⟩, hs4⟩, hp⟩, hv⟩, hns⟩, hno⟩ := hg
  have hnoeid : ∀ x ∈ s.current.triples, x.eid ≠ r.eid := by
    intro x hx he
    have := List.any_eq_false.1 hany x hx
    simp [he] at this
  have rowOK : RowOK (lastT s.committed + 1) (nextStmt s.current) row := by
    refine ⟨htag, ?_, by show eidCtr r.eid < _; rw [hN]; exact hhi, ⟨hs0, hs4⟩, hp, hns, hno, hv, by rw [htAdd]; omega,
      by rw [htAdd, hT], Or.inl ⟨rfl, rfl⟩⟩
    show 0 ≤ eidCtr r.eid
    have := hi.wf.nextLo; rw [hB] at this; omega
  obtain ⟨pre, new, hb, f, nw⟩ := hi.ext.rows
  refine ⟨hi.inTx, hi.wf, hi.lastTEq, hi.lastIEq, hi.txs, ⟨⟨pre, new ++ [row], ?_, f, ?_⟩, hi.ext.terms, hi.ext.txs,
    hi.ext.ids, hi.ext.lastT⟩, ?_, ?_, hi.present⟩
  · show s.current.triples ++ [row] = _; rw [hb, List.append_assoc]
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact nw x hx
    · rw [List.mem_singleton] at hx; subst hx
      refine ⟨by rw [hB]; exact hlo, ?_⟩
      rw [htAdd, hT]; omega
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hi.rows x hx
    · rw [List.mem_singleton] at hx; subst hx; exact rowOK
  · show (s.current.triples ++ [row]).Pairwise _
    rw [List.pairwise_append]
    refine ⟨hi.uniq, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    exact hnoeid a ha

/-- Retracting a live row keeps a row evolution valid when it is newer than `T`. -/
theorem RowExt.retract {T : Int} {r r' : TripleRow} {e t k : Int64} (h : RowExt T r r')
    (hlive : r'.eid = e → r'.tRet = none) (ht : T < t.toInt) : RowExt T r (retractRow e t k r') := by
  obtain ⟨he, hs, hp, ho, ha, hf, hto, _, hne⟩ := retractRow_spec e t k r'
  by_cases hx : r'.eid = e
  · obtain ⟨hr1, _⟩ := (retractRow_spec e t k r').2.2.2.2.2.2.2.1 hx
    refine ⟨he.trans h.eid, hs.trans h.s, hp.trans h.p, ho.trans h.o, ha.trans h.tAdd, hf.trans h.vFrom,
      hto.trans h.vTo, Or.inr ⟨?_, t, hr1, ht⟩⟩
    rcases h.ret with ⟨e1, _⟩ | ⟨n1, _⟩
    · rw [← e1]; exact hlive hx
    · exact n1
  · rw [hne hx]; exact h

theorem forall₂_map_right {R : TripleRow → TripleRow → Prop} {f : TripleRow → TripleRow} :
    ∀ {l m : List TripleRow}, List.Forall₂ R l m → (∀ a b, b ∈ m → R a b → R a (f b)) →
      List.Forall₂ R l (m.map f)
  | [], [], _, _ => List.Forall₂.nil
  | _ :: _, _ :: _, List.Forall₂.cons hab rest, hf =>
    List.Forall₂.cons (hf _ _ (List.mem_cons_self ..) hab)
      (forall₂_map_right rest fun a b hb h => hf a b (List.mem_cons_of_mem _ hb) h)

theorem inv_retract {e : Int64} {k : RetKind} {s s' : ModelStore} {b : Bool} (hi : TxInv s)
    (h : (retractRun e k : ModelM Bool) s = .ok (b, s')) : TxInv s' ∧ Frame s s' := by
  obtain ⟨lastT', h1, hl0, hl1, hcase⟩ := retract_spec' h
  rcases hcase with ⟨_, rfl, _⟩ | ⟨_, _, r, hr, hlive, rfl⟩
  · exact ⟨hi, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  have hT : lastT s.committed = lastT'.toInt := ctr_of_some h1
  have ht : (lastT' + 1).toInt = lastT'.toInt + 1 := by
    have : lastTLimit < 2 ^ 63 - 1 := by unfold lastTLimit; norm_num
    exact toInt_add_one (by omega) (by omega)
  obtain ⟨hrm, hre⟩ := triple_eq_some hr
  -- every row with eid `e` is `r`, which is live
  have hlive' : ∀ x ∈ s.current.triples, x.eid = e → x.tRet = none := by
    intro x hx hxe
    have huniq := hi.uniq
    by_contra hne
    have hxr : x ≠ r := by intro hxr; subst hxr; exact hne hlive
    rw [List.pairwise_iff_get] at huniq
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hrm
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact huniq ⟨i, hi'⟩ ⟨j, hj⟩ hij (by simp [hxe, hre])
    · exact hxr rfl
    · exact huniq ⟨j, hj⟩ ⟨i, hi'⟩ hij (by simp [hxe, hre])
  obtain ⟨pre, new, hb, fr, nw⟩ := hi.ext.rows
  refine ⟨hi.inTx, hi.wf, hi.lastTEq, hi.lastIEq, hi.txs, ⟨⟨pre.map (retractRow e (lastT' + 1) k.code),
    new.map (retractRow e (lastT' + 1) k.code), ?_, ?_, ?_⟩, hi.ext.terms,
    hi.ext.txs, hi.ext.ids, hi.ext.lastT⟩, ?_, ?_, hi.present⟩
  · show s.current.triples.map (retractRow e (lastT' + 1) k.code) = _; rw [hb, List.map_append]
  · apply forall₂_map_right fr
    intro a x hx hax
    apply RowExt.retract hax
    · intro hxe; exact hlive' x (by rw [hb]; exact List.mem_append_left _ hx) hxe
    · rw [ht, ← hT]; omega
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨he', -, -, -, ha', -⟩ := retractRow_spec e (lastT' + 1) k.code y
    rw [he', ha']; exact nw y hy
  · intro x hx
    change x ∈ s.current.triples.map (retractRow e (lastT' + 1) k.code) at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have ok := hi.rows y hy
    show RowOK (lastT s.committed + 1) (nextStmt s.current) _
    obtain ⟨he', hs', hp', ho', ha', hf', hto', hset, hne⟩ := retractRow_spec e (lastT' + 1) k.code y
    by_cases hye : y.eid = e
    · obtain ⟨hr1, hr2⟩ := hset hye
      have hyl := hlive' y hy hye
      refine ⟨by rw [he']; exact ok.tag, by rw [he']; exact ok.ctrLo, by rw [he']; exact ok.ctrHi,
        by rw [hs']; exact ok.subj, by rw [hp']; exact ok.pred, by rw [hs', he']; exact ok.noSelfS,
        by rw [ho', he']; exact ok.noSelfO, by rw [hf', hto']; exact ok.valid, by rw [ha']; exact ok.tAddLo,
        by rw [ha']; exact ok.tAddHi, Or.inr ⟨_, _, hr1, hr2, ?_, ?_, retKind_code k⟩⟩
      · rw [ha', ht, ← hT]; exact ok.tAddHi
      · rw [ht, ← hT]
    · rw [hne hye]; exact ok
  · show (s.current.triples.map (retractRow e (lastT' + 1) k.code)).Pairwise _
    rw [List.pairwise_map]
    exact hi.uniq.imp fun hne => by
      rw [(retractRow_spec e (lastT' + 1) k.code _).1, (retractRow_spec e (lastT' + 1) k.code _).1]; exact hne

theorem inv_intern {k : TermKey} {num : Option UInt64} {s s' : ModelStore} {x : Except CodecError Nat}
    (hi : TxInv s) (h : (internKey k num : ModelM _) s = .ok (x, s')) : TxInv s' ∧ Frame s s' := by
  rcases intern_spec h with rfl | ⟨_, next, row, c1, c2, hnext, hle, hins, hset, rfl⟩
  · exact ⟨hi, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl, rfl, by rw [setCounter_txs hset, insertTerm_ok hins]⟩
  have hc1 := insertTerm_ok hins
  subst hc1
  -- the term insert keeps everything but the terms
  have hi1 : TxInv { s with current := { s.current with terms := s.current.terms ++ [{ row with num := normalizeNum row.num }] } } := by
    obtain ⟨pre, new, hb, fr, nw⟩ := hi.ext.rows
    exact ⟨hi.inTx, hi.wf, hi.lastTEq, hi.lastIEq, hi.txs,
      ⟨⟨pre, new, hb, fr, nw⟩, hi.ext.terms.trans (List.prefix_append _ _), hi.ext.txs, hi.ext.ids, hi.ext.lastT⟩,
      hi.rows, hi.uniq, hi.present⟩
  refine inv_setCounter (s := { s with current := { s.current with
    terms := s.current.terms ++ [{ row with num := normalizeNum row.num }] } }) (n := "next_term") hi1 hset
    (by decide) ?_
  intro _
  show ctr s.current "next_term" ≤ _
  have hn : (next : Int) < 2 ^ 63 - 1 := by unfold termIdMax at hle; omega
  have hv : ((next + 1 : Nat).toInt64).toInt = (next : Int) + 1 := by
    show (Int64.ofNat (next + 1)).toInt = _
    rw [Int64.toInt_ofNat', ← Int64.toInt_ofInt, Int64.toInt_ofInt_of_le (by omega) (by omega)]
    push_cast; ring
  rw [hv]
  unfold ctr
  cases hc : s.current.counter "next_term" with
  | none =>
    simp only [Option.getD_none]
    rw [show (0 : Int64).toInt = 0 from rfl]; omega
  | some v =>
    simp only [hc, Option.getD_some] at hnext ⊢
    have : v.toInt ≤ (v.toNatClampNeg : Int) := by
      unfold Int64.toNatClampNeg; omega
    omega

theorem inv_markMulti {p : Int64} {s s' : ModelStore} {u : Unit} (hi : TxInv s)
    (h : (markMultiRun p : ModelM Unit) s = .ok (u, s')) : TxInv s' ∧ Frame s s' := by
  rcases markMulti_spec h with rfl | ⟨_, c1, c2, v, hadd, hset, rfl⟩
  · exact ⟨hi, rfl, rfl, rfl, rfl⟩
  have htx := setCounter_txs hset
  unfold ModelState.addPredMulti at hadd
  cases hadd
  refine ⟨?_, rfl, rfl, rfl, htx⟩
  have hi1 : TxInv { s with current := { s.current with
      predMulti := if s.current.predMulti.contains p then s.current.predMulti else s.current.predMulti ++ [p] } } :=
    ⟨hi.inTx, hi.wf, hi.lastTEq, hi.lastIEq, hi.txs,
      ⟨hi.ext.rows, hi.ext.terms, hi.ext.txs, hi.ext.ids, hi.ext.lastT⟩, hi.rows, hi.uniq, hi.present⟩
  exact inv_setCounter (s := { s with current := { s.current with
      predMulti := if s.current.predMulti.contains p then s.current.predMulti else s.current.predMulti ++ [p] } })
    (n := "multi_version") hi1 hset (by decide) (by simp [idNames])

theorem inv_volPut {r : VolatileRow} {s s' : ModelStore} {u : Unit} (hi : TxInv s)
    (h : (WriteStore.volatilePut r : ModelM Unit) s = .ok (u, s')) : TxInv s' ∧ Frame s s' := by
  rw [mvolPut] at h
  obtain ⟨_, c, hc, rfl⟩ := data_exec rfl h
  unfold WriteOp.step ModelState.volatilePut at hc
  cases hc
  exact ⟨⟨hi.inTx, hi.wf, hi.lastTEq, hi.lastIEq, hi.txs,
    ⟨hi.ext.rows, hi.ext.terms, hi.ext.txs, hi.ext.ids, hi.ext.lastT⟩, hi.rows, hi.uniq, hi.present⟩, rfl, rfl, rfl, rfl⟩

theorem inv_volDel {a key : Int64} {s s' : ModelStore} {u : Unit} (hi : TxInv s)
    (h : (WriteStore.volatileDel a key : ModelM Unit) s = .ok (u, s')) : TxInv s' ∧ Frame s s' := by
  rw [mvolDel] at h
  obtain ⟨_, c, hc, rfl⟩ := data_exec rfl h
  unfold WriteOp.step ModelState.volatileDel at hc
  cases hc
  exact ⟨⟨hi.inTx, hi.wf, hi.lastTEq, hi.lastIEq, hi.txs,
    ⟨hi.ext.rows, hi.ext.terms, hi.ext.txs, hi.ext.ids, hi.ext.lastT⟩, hi.rows, hi.uniq, hi.present⟩, rfl, rfl, rfl, rfl⟩

/-- Every body operation preserves the invariant and the frame. -/
theorem inv_op (o : Op) {s s' : ModelStore} {x : o.Res} (hi : TxInv s)
    (h : (Op.run o : ModelM o.Res) s = .ok (x, s')) : TxInv s' ∧ Frame s s' := by
  cases o with
  | read r => obtain ⟨rfl, _⟩ := read_same h; exact ⟨hi, rfl, rfl, rfl, rfl⟩
  | alloc c => exact inv_alloc hi h
  | insert r => exact inv_insert hi h
  | retract e k => exact inv_retract hi h
  | intern k num => exact inv_intern hi h
  | volPut r => exact inv_volPut hi h
  | volDel a k => exact inv_volDel hi h
  | markMulti p => exact inv_markMulti hi h

theorem Frame.trans {a b c : ModelStore} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- Every body program preserves the invariant and the frame. -/
theorem inv_prog {α : Type} : ∀ (p : SProg α) {s s' : ModelStore} {a : α}, TxInv s →
    SProg.runModel p s = .ok (a, s') → TxInv s' ∧ Frame s s'
  | .pure _, s, s', a, hi, h => by
    simp only [SProg.runModel] at h; cases h; exact ⟨hi, rfl, rfl, rfl, rfl⟩
  | .op o k, s, s', a, hi, h => by
    simp only [SProg.runModel] at h
    cases hr : (Op.run o : ModelM o.Res) s with
    | error e => rw [hr] at h; cases h
    | ok p =>
      rcases p with ⟨x, s1⟩
      rw [hr] at h
      obtain ⟨hi1, f1⟩ := inv_op o hi hr
      obtain ⟨hi2, f2⟩ := inv_prog (k x) hi1 h
      exact ⟨hi2, f1.trans f2⟩

end Tiramemsu.Engine
