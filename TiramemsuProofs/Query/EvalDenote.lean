/-
query-semantics "Reference semantics": the evaluator on the model store returns the reference
bag of every validated query (the reference list under a root `OrderLimit`), for every plan.
Soundness direction: whenever `denote` returns a bag, the evaluator returns a permutation of it.
Hypotheses: the id bridge on the model state (`IdBridge`), the evaluator's path engine agrees
with the reference path semantics row by row (`PathSim`, true by construction for the path
engine, see `pathSim_engine`), and no stored pattern binds two eid columns of one match group
(`isoLocal`). Constants of pushed equalities need no hypothesis: `identityConst?` only accepts
constants that compare by identity (`identityConst_idEq`).
-/
import TiramemsuProofs.Query.JoinCore
import TiramemsuProofs.Query.OrderLimit
import TiramemsuProofs.Query.Validate
import TiramemsuProofs.Query.Stable

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Expressions equal up to the bags of `EXISTS` -/

/-- Two resolved expressions evaluate alike on every row. -/
def EqE (e e' : RExpr) : Prop := ∀ r, e.eval r = e'.eval r

theorem EqE.refl (e : RExpr) : EqE e e := fun _ => rfl

theorem EqE.holds {e e' : RExpr} (h : EqE e e') : e.holds = e'.holds := by
  funext r; unfold RExpr.holds RExpr.tri; rw [h r]

theorem EqE.eval {e e' : RExpr} (h : EqE e e') : e.eval = e'.eval := funext h

theorem tris_eq {r : Row} : ∀ {xs ys : List RExpr}, List.Forall₂ EqE xs ys → RExpr.tris r xs = RExpr.tris r ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, .cons h hs => by simp only [RExpr.tris]; rw [h r, tris_eq hs]

theorem eqTris_eq {r : Row} {o : Option Value} : ∀ {xs ys : List RExpr}, List.Forall₂ EqE xs ys →
    RExpr.eqTris r o xs = RExpr.eqTris r o ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, .cons h hs => by simp only [RExpr.eqTris]; rw [h r, eqTris_eq hs]

theorem firstOk_eq {r : Row} : ∀ {xs ys : List RExpr}, List.Forall₂ EqE xs ys → RExpr.firstOk r xs = RExpr.firstOk r ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, .cons h hs => by simp only [RExpr.firstOk]; rw [h r, firstOk_eq hs]

theorem evalAll_eq {r : Row} : ∀ {xs ys : List RExpr}, List.Forall₂ EqE xs ys → RExpr.evalAll r xs = RExpr.evalAll r ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, .cons h hs => by simp only [RExpr.evalAll]; rw [h r, evalAll_eq hs]

theorem EqE.cmp (op : CmpOp) {a a' b b' : RExpr} (ha : EqE a a') (hb : EqE b b') : EqE (.cmp op a b) (.cmp op a' b') :=
  fun r => by simp only [RExpr.eval]; rw [ha r, hb r]
theorem EqE.sameTerm {a a' b b' : RExpr} (ha : EqE a a') (hb : EqE b b') : EqE (.sameTerm a b) (.sameTerm a' b') :=
  fun r => by simp only [RExpr.eval]; rw [ha r, hb r]
theorem EqE.arith (op : ArithOp) {a a' b b' : RExpr} (ha : EqE a a') (hb : EqE b b') : EqE (.arith op a b) (.arith op a' b') :=
  fun r => by simp only [RExpr.eval]; rw [ha r, hb r]
theorem EqE.not {a a' : RExpr} (ha : EqE a a') : EqE (.not a) (.not a') :=
  fun r => by simp only [RExpr.eval]; rw [ha r]
theorem EqE.neg {a a' : RExpr} (ha : EqE a a') : EqE (.neg a) (.neg a') :=
  fun r => by simp only [RExpr.eval]; rw [ha r]
theorem EqE.and {xs ys : List RExpr} (h : List.Forall₂ EqE xs ys) : EqE (.and xs) (.and ys) :=
  fun r => by simp only [RExpr.eval]; rw [tris_eq h]
theorem EqE.or {xs ys : List RExpr} (h : List.Forall₂ EqE xs ys) : EqE (.or xs) (.or ys) :=
  fun r => by simp only [RExpr.eval]; rw [tris_eq h]
theorem EqE.coalesce {xs ys : List RExpr} (h : List.Forall₂ EqE xs ys) : EqE (.coalesce xs) (.coalesce ys) :=
  fun r => by simp only [RExpr.eval]; rw [firstOk_eq h]
theorem EqE.func (f : Func) {xs ys : List RExpr} (h : List.Forall₂ EqE xs ys) : EqE (.func f xs) (.func f ys) :=
  fun r => by simp only [RExpr.eval]; rw [evalAll_eq h]
theorem EqE.inList {a a' : RExpr} {xs ys : List RExpr} (n : Bool) (ha : EqE a a') (h : List.Forall₂ EqE xs ys) :
    EqE (.inList a xs n) (.inList a' ys n) :=
  fun r => by simp only [RExpr.eval]; rw [ha r, eqTris_eq h]
theorem EqE.ite {c c' a a' b b' : RExpr} (hc : EqE c c') (ha : EqE a a') (hb : EqE b b') :
    EqE (.ite c a b) (.ite c' a' b') :=
  fun r => by simp only [RExpr.eval]; rw [hc r, ha r, hb r]
theorem EqE.exists {b b' : Bag} (n : Bool) (h : b.Perm b') : EqE (.exists b n) (.exists b' n) :=
  fun r => by simp only [RExpr.eval]; rw [h.any_eq]

/-- Optional expressions that evaluate alike. -/
def OptEqE : Option RExpr → Option RExpr → Prop
  | none, none => True
  | some e, some e' => EqE e e'
  | _, _ => False

/-- Aggregates that compute alike. -/
def AggEq (a a' : Nat × AggFunc × Option RExpr × Bool) : Prop :=
  a.1 = a'.1 ∧ a.2.1 = a'.2.1 ∧ a.2.2.2 = a'.2.2.2 ∧ OptEqE a.2.2.1 a'.2.2.1

/-- Sort keys that compare alike. -/
def KeyEq (k k' : RExpr × Bool) : Prop := EqE k.1 k'.1 ∧ k.2 = k'.2

theorem aggregateOne_congr (f : AggFunc) {a a' : Option RExpr} (h : OptEqE a a') (d : Bool) :
    aggregateOne f a d = aggregateOne f a' d := by
  funext grp
  cases a with
  | none => cases a' with
    | none => rfl
    | some _ => cases h
  | some e => cases a' with
    | none => cases h
    | some e' =>
      simp only [OptEqE] at h
      simp only [aggregateOne]
      rw [show (fun r => RExpr.eval r e) = (fun r => RExpr.eval r e') from funext h]

theorem aggregateB_congr (n : Nat) (g : List Nat) {as as' : List (Nat × AggFunc × Option RExpr × Bool)}
    (h : List.Forall₂ AggEq as as') : aggregateB n g as = aggregateB n g as' := by
  funext xs
  unfold aggregateB
  simp only []
  congr 1; funext kg
  generalize ((g.zip kg.1).foldl (fun (r : Row) (i, c) => r.set i c) (Row.empty n)) = r0
  induction h generalizing r0 with
  | nil => rfl
  | @cons a a' _ _ ha _ ih =>
    obtain ⟨i, f, x, d⟩ := a
    obtain ⟨i', f', x', d'⟩ := a'
    obtain ⟨h1, h2, h3, h4⟩ := ha
    simp only at h1 h2 h3 h4
    subst h1 h2 h3
    simp only [List.foldl_cons]
    rw [aggregateOne_congr f h4 d, ih]

theorem orderLimitB_congr (m : Missing) {ks ks' : List (RExpr × Bool)} (h : List.Forall₂ KeyEq ks ks')
    (s l : Option Nat) : orderLimitB m ks s l = orderLimitB m ks' s l := by
  have h1 : ks.map (·.2) = ks'.map (·.2) := by
    induction h with
    | nil => rfl
    | cons hk _ ih => simp [hk.2, ih]
  have h2 : ∀ r, (ks.map fun (e, _) => e.eval r) = (ks'.map fun (e, _) => e.eval r) := by
    intro r
    clear h1
    induction h with
    | nil => rfl
    | @cons a b _ _ hk _ ih =>
      obtain ⟨e, d⟩ := a
      obtain ⟨e', d'⟩ := b
      simp only [List.map_cons, ih]
      rw [hk.1 r]
  funext xs
  unfold orderLimitB
  simp only [h1, h2]

theorem filterB_rel {c c' : RExpr} (hc : EqE c c') {xs ys : Bag} (h : xs.Perm ys) :
    (filterB c xs).Perm (filterB c' ys) := by
  unfold filterB; rw [hc.holds]; exact h.filter _

theorem extendB_rel (i : Nat) {e e' : RExpr} (he : EqE e e') {xs ys : Bag} (h : xs.Perm ys) :
    (extendB i e xs).Perm (extendB i e' ys) := by
  unfold extendB
  have : ∀ r, RExpr.eval r e = RExpr.eval r e' := he
  simp only [this]
  exact h.map _

theorem projectB_perm (keep : List Nat) (d : Bool) {xs ys : Bag} (h : xs.Perm ys) :
    (projectB keep d xs).Perm (projectB keep d ys) := by
  unfold projectB
  simp only []
  split
  · exact eraseDups_perm (h.map _)
  · exact h.map _

/-- The condition of a left join on a merged row. -/
def condF (c : Option RExpr) (r : Row) : Bool := match c with
  | some e => e.holds r
  | none => true

theorem condF_eq {c c' : Option RExpr} (hc : OptEqE c c') : condF c = condF c' := by
  cases c with
  | none => cases c' with
    | none => rfl
    | some _ => exact absurd hc id
  | some e => cases c' with
    | none => exact absurd hc id
    | some e' => funext r; exact congrFun (EqE.holds hc) r

theorem ljMatches_condF (m : Missing) (P Q : Schema) (c : Option RExpr) (a : Row) (ys : Bag) :
    ljMatches m P Q c a ys = ys.filterMap fun b =>
      if compat m P Q a b then (if condF c (merge a b) then some (merge a b) else none) else none := rfl

theorem leftJoinB_rel (m : Missing) (P Q : Schema) {c c' : Option RExpr} (hc : OptEqE c c') {xs xs' ys ys' : Bag}
    (hx : xs.Perm xs') (hy : ys.Perm ys') : (leftJoinB m P Q c xs ys).Perm (leftJoinB m P Q c' xs' ys') := by
  rw [leftJoinB_eq, leftJoinB_eq]
  refine (flatMap_perm_congr fun a _ => ?_).trans (hx.flatMap_right _)
  have hm : (ljMatches m P Q c a ys).Perm (ljMatches m P Q c' a ys') := by
    rw [ljMatches_condF, ljMatches_condF, condF_eq hc]
    exact hy.filterMap _
  exact ite_empty_perm hm

/-! ## Virtual-predicate patterns -/

theorem ev_filterMapM {α β : Type} {st : ModelState} {f : α → EvM (Option β)} {g : α → Option β} :
    ∀ (xs : List α), (∀ x ∈ xs, ev st (f x) = .ok (.ok (g x))) → ev st (xs.filterMapM f) = .ok (.ok (xs.filterMap g))
  | [], _ => by rw [List.filterMapM_nil]; rfl
  | x :: xs, h => by
    rw [List.filterMapM_cons, ev_bind, h x (List.mem_cons_self ..)]
    have ih := ev_filterMapM xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filterMap_cons]
    cases g x with
    | none => exact ih
    | some b => rw [ev_bind, ih]; rfl

/-- The evaluator's virtual row of one (masked) statement. -/
def gV (E : Env) (t : TriplePattern) (vp : VirtualPred) (r : TripleRow) : EvM (Option Row) := do
  match ← virtualValueE vp r with
  | none => return none
  | some val =>
    match ← matchValE E false t.s (← decodeE r.eid) (Row.empty E.n) with
    | none => return none
    | some row => matchValE E vp.byInstant t.o val row

/-- The statements a virtual-predicate pattern reads. -/
def vRows (t : TriplePattern) (v : Store.View) : EvM (List TripleRow) :=
  match t.s with
  | .const c => do
    match ← lookupE c.canonical with
    | some e => pure (← liftR (lookupEid v e)).toList
    | none => pure []
  | .id o => do pure (← liftR (lookupEid v o.raw)).toList
  | _ => do
    let rs ← liftR (rangeScan .spo v [])
    pure (rs.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt))

theorem virtualPat_eq (E : Env) (t : TriplePattern) (vp : VirtualPred) : virtualPat E t vp = (do
    let v ← resolveViewE t.view
    let rows ← vRows t v
    let out ← (rows.map (View.mask v)).filterMapM (gV E t vp)
    return if E.sem.graphSet == .setOfTriples then out.eraseDups else out) := by
  unfold virtualPat vRows gV
  simp only [bind_assoc]
  congr 1; funext v
  cases hs : t.s with
  | const c =>
    simp only [bind_assoc]
    congr 1; funext x
    cases x <;> simp only [bind_assoc, pure_bind, hs] <;> rfl
  | id o => simp only [bind_assoc, pure_bind, hs]; rfl
  | var x => simp only [bind_assoc, pure_bind, hs]; rfl
  | param x => simp only [bind_assoc, pure_bind, hs]; rfl

section
variable {st : ModelState} (hB : IdBridge st)
include hB

omit hB in
theorem mask_eid (v : Store.View) (r : TripleRow) : (View.mask v r).eid = r.eid ∧ (View.mask v r).s = r.s ∧
    (View.mask v r).p = r.p ∧ (View.mask v r).o = r.o := by
  unfold View.mask; split <;> simp

omit hB in
theorem onModel_txByT (t : Int64) : RProg.onModel st (RProg.lift (.txByT t)) = .ok (st.txByT t) := rfl

omit hB in
theorem ev_matchValE (E : Env) (bv : Bool) (tv : TermOrVar) (val : Value) (row : Row) {o : Option Row}
    (h : matchVal (E.at st) bv tv val row = .ok o) : ev st (matchValE E bv tv val row) = .ok (.ok o) := by
  cases tv with
  | var v => simp only [matchVal] at h; cases h; rfl
  | const c => simp only [matchVal] at h; cases h; rfl
  | param _ => simp only [matchVal] at h; cases h; rfl
  | id oo =>
    simp only [matchVal, Env.at_st] at h
    cases hd : decodeId st oo.raw with
    | error e => rw [hd] at h; cases h
    | ok w =>
      rw [hd] at h; simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      unfold matchValE; rw [ev_bind, ev_decodeE st hd]; rw [← h]; rfl

omit hB in
theorem ev_virtualValueE (vp : VirtualPred) {r : TripleRow} (hr : ∀ x ∈ stmtIds r, ∃ v, decodeId st x = .ok v)
    {o : Option Value} (h : virtualValue st vp r = .ok o) : ev st (virtualValueE vp r) = .ok (.ok o) := by
  cases vp with
  | subject =>
    simp only [virtualValue] at h
    obtain ⟨v, hv⟩ := hr r.s (by simp [stmtIds])
    rw [hv] at h; simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    unfold virtualValueE; rw [ev_bind, ev_decodeE st hv, ← h]; rfl
  | predicate =>
    simp only [virtualValue] at h
    obtain ⟨v, hv⟩ := hr r.p (by simp [stmtIds])
    rw [hv] at h; simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    unfold virtualValueE; rw [ev_bind, ev_decodeE st hv, ← h]; rfl
  | object =>
    simp only [virtualValue] at h
    obtain ⟨v, hv⟩ := hr r.o (by simp [stmtIds])
    rw [hv] at h; simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    unfold virtualValueE; rw [ev_bind, ev_decodeE st hv, ← h]; rfl
  | txAdded => simp only [virtualValue] at h; cases h; rfl
  | txRetracted => simp only [virtualValue] at h; cases h; rfl
  | validFrom => simp only [virtualValue] at h; cases h; rfl
  | validTo => simp only [virtualValue] at h; cases h; rfl
  | retractKind => simp only [virtualValue] at h; cases h; rfl
  | addedAt =>
    simp only [virtualValue] at h; cases h
    unfold virtualValueE instantE
    rw [ev_bind, ev_liftR, onModel_txByT]; rfl
  | retractedAt =>
    simp only [virtualValue] at h; cases h
    unfold virtualValueE
    cases ht : r.tRet with
    | none => rfl
    | some t => simp only []; unfold instantE; rw [ev_bind, ev_liftR, onModel_txByT]; rfl

theorem stmt_decodes {r : TripleRow} (hr : r ∈ st.triples) (v : Store.View) :
    ∀ x ∈ stmtIds (View.mask v r), ∃ w, decodeId st x = .ok w := by
  obtain ⟨h1, h2, h3, h4⟩ := mask_eid v r
  intro x hx
  simp only [stmtIds, h1, h2, h3, h4] at hx
  exact hB.decodes r hr x hx

theorem ev_gV (E : Env) (t : TriplePattern) (vp : VirtualPred) {r : TripleRow} (hr : r ∈ st.triples)
    (v : Store.View) {o : Option Row} (h : virtualRow (E.at st) t vp (View.mask v r) = .ok o) :
    ev st (gV E t vp (View.mask v r)) = .ok (.ok o) := by
  have hd := stmt_decodes hB hr v
  unfold virtualRow at h
  unfold gV
  cases hv : virtualValue st vp (View.mask v r) with
  | error e => simp only [Env.at_st, hv] at h; cases h
  | ok ov =>
    simp only [Env.at_st, hv, bind, Except.bind] at h
    rw [ev_bind, ev_virtualValueE vp hd hv]
    cases ov with
    | none => simp only at h ⊢; cases h; rfl
    | some val =>
      simp only at h ⊢
      obtain ⟨w, hw⟩ := hd (View.mask v r).eid (by simp [stmtIds])
      rw [hw] at h
      simp only [bindOpt, bind, Except.bind] at h
      rw [ev_bind, ev_decodeE st hw]
      simp only []
      cases hm : matchVal (E.at st) false t.s w (Row.empty E.n) with
      | error e => rw [Env.at_n, hm] at h; cases h
      | ok orow =>
        rw [Env.at_n, hm] at h
        rw [ev_bind, ev_matchValE E false t.s w _ hm]
        cases orow with
        | none => simp only at h ⊢; cases h; rfl
        | some row => simp only at h ⊢; exact ev_matchValE E _ t.o val row h

omit hB in
theorem filterMap_filter_of {α β : Type} (f : α → Option β) (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome → p x = true) → l.filterMap f = (l.filter p).filterMap f
  | [], _ => rfl
  | x :: xs, h => by
    have ih := filterMap_filter_of f p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.filterMap_cons, List.filterMap_cons, ih]
    · have hn : f x = none := by
        cases hf : f x with
        | none => rfl
        | some _ => exact absurd (h x (List.mem_cons_self ..) (by simp [hf])) hp
      rw [List.filter_cons_of_neg hp, List.filterMap_cons, hn, ih]

theorem filterMap_eid (v : Store.View) (go : TripleRow → Option Row) (e : Int64)
    (hgo : ∀ r ∈ st.triples, v.admits r = true → (go (View.mask v r)).isSome → r.eid = e) :
    ((visibleRows st v).map (View.mask v)).filterMap go =
      ((((st.triple e).filter v.admits).toList).map (View.mask v)).filterMap go := by
  rw [List.filterMap_map, List.filterMap_map]
  rw [filterMap_filter_of _ (fun r => r.eid == e) _ (fun r hr hs => by
    have := List.mem_filter.1 hr
    simpa using hgo r this.1 this.2 hs)]
  congr 1
  unfold visibleRows ModelState.triple
  rw [List.filter_comm, filter_eid_eq hB.wf]
  cases (st.triples.find? (·.eid == e)) with
  | none => rfl
  | some r0 => by_cases ha : v.admits r0 = true <;> simp [Option.filter, ha]

theorem virtualRow_subject {E : Env} {t : TriplePattern} {vp : VirtualPred} {v : Store.View} {r : TripleRow}
    (hr : r ∈ st.triples) {row : Row} (h : virtualRow (E.at st) t vp (View.mask v r) = .ok (some row)) :
    ∃ row0, matchVal (E.at st) false t.s (dv st r.eid) (Row.empty E.n) = .ok (some row0) := by
  unfold virtualRow at h
  cases hv : virtualValue (E.at st).st vp (View.mask v r) with
  | error e => rw [hv] at h; cases h
  | ok ov =>
    rw [hv] at h
    simp only [bind, Except.bind] at h
    cases ov with
    | none => simp at h; cases h
    | some val =>
      simp only at h
      rw [(mask_eid v r).1, Env.at_st, decodeId_dv hB hr (mem_stmtIds_eid r)] at h
      simp only [bindOpt, bind, Except.bind, Env.at_n] at h
      cases hm : matchVal (E.at st) false t.s (dv st r.eid) (Row.empty E.n) with
      | error e => rw [hm] at h; cases h
      | ok o =>
        cases o with
        | none => rw [hm] at h; simp [pure, Except.pure] at h
        | some row0 => exact ⟨row0, rfl⟩

theorem ev_virtualPat (E : Env) {t : TriplePattern} {vp : VirtualPred} (hvp : t.p.virtual? = some vp)
    (he : t.eid = none) {b : Bag} (h : triplePat (E.at st) t = .ok b) :
    ∃ b', ev st (virtualPat E t vp) = .ok (.ok b') ∧ b'.Perm b := by
  set v := resolveView st t.view with hv
  unfold triplePat at h
  simp only [hvp, Env.at_st, Env.at_sem, he, Option.isNone_none, Bool.and_true] at h
  rw [← hv] at h
  unfold collectRows at h
  set L := (visibleRows st v).map (View.mask v)
  cases hm : L.mapM (fun r => do return (← virtualRow (E.at st) t vp r).toList : TripleRow → Except LErr (List Row)) with
  | error e => rw [hm] at h; cases h
  | ok parts =>
    rw [hm] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    set go : TripleRow → Option Row := fun r => okv (virtualRow (E.at st) t vp r)
    have hall := mapM_ok_mem hm
    have hgo : ∀ r ∈ L, virtualRow (E.at st) t vp r = .ok (go r) := by
      intro r hr
      obtain ⟨w, hw⟩ := hall r hr
      cases hvr : virtualRow (E.at st) t vp r with
      | error e => rw [hvr] at hw; cases hw
      | ok o => show _ = Except.ok (okv _); rw [hvr]; rfl
    have hparts : parts = L.map fun r => (go r).toList := by
      rw [mapM_ok_okv hall] at hm
      cases hm
      apply List.map_congr_left
      intro r hr
      rw [hgo r hr]; rfl
    have hbag : parts.flatten = L.filterMap go := by
      rw [hparts, ← List.flatMap_def, filterMap_eq_flatMap]
    -- the evaluator
    have hrow : ∀ rows : List TripleRow, (∀ r ∈ rows, r ∈ st.triples ∧ v.admits r = true) →
        ev st ((rows.map (View.mask v)).filterMapM (gV E t vp)) = .ok (.ok ((rows.map (View.mask v)).filterMap go)) := by
      intro rows hrs
      apply ev_filterMapM
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      have hrL : View.mask v r ∈ L := List.mem_map.2 ⟨r, List.mem_filter.2 ⟨(hrs r hr).1, (hrs r hr).2⟩, rfl⟩
      exact ev_gV hB E t vp (hrs r hr).1 v (hgo _ hrL)
    have hfin : ∀ out : Bag, out.Perm (L.filterMap go) →
        ∃ b', ev st (pure (if E.sem.graphSet == .setOfTriples then out.eraseDups else out) : EvM Bag) = .ok (.ok b') ∧ b'.Perm b := by
      intro out hout
      refine ⟨_, rfl, ?_⟩
      rw [← h, hbag]
      split
      · exact eraseDups_perm hout
      · exact hout
    have hsub : ∀ (e : Int64) (r : TripleRow), r ∈ ((st.triple e).filter v.admits).toList → r ∈ st.triples ∧ v.admits r = true := by
      intro e r hr
      simp only [Option.mem_toList, Option.filter_eq_some_iff] at hr
      unfold ModelState.triple at hr
      exact ⟨List.mem_of_find?_eq_some hr.1, hr.2⟩
    -- the statements read
    have hvr : ∃ rows, ev st (vRows t v) = .ok (.ok rows) ∧ (∀ r ∈ rows, r ∈ st.triples ∧ v.admits r = true) ∧
        ((rows.map (View.mask v)).filterMap go).Perm (L.filterMap go) := by
      have key : ∀ e, (∀ r ∈ st.triples, v.admits r = true → (go (View.mask v r)).isSome → r.eid = e) →
          ((((st.triple e).filter v.admits).toList.map (View.mask v)).filterMap go).Perm (L.filterMap go) :=
        fun e he => List.Perm.of_eq (filterMap_eid hB v go e he).symm
      have subj : ∀ r ∈ st.triples, v.admits r = true → (go (View.mask v r)).isSome →
          ∃ row0, matchVal (E.at st) false t.s (dv st r.eid) (Row.empty E.n) = .ok (some row0) := by
        intro r hrT ha hsome
        obtain ⟨row, hrow'⟩ := Option.isSome_iff_exists.1 hsome
        have := hgo _ (List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hrT, ha⟩, rfl⟩)
        rw [hrow'] at this
        exact virtualRow_subject hB hrT this
      unfold vRows
      cases hs : t.s with
      | const c =>
        simp only []
        rw [ev_bind, ev_lookupE]
        simp only []
        cases hl : lookupId st c.canonical with
        | none =>
          refine ⟨[], rfl, fun _ h => (by cases h), ?_⟩
          rw [List.map_nil, List.filterMap_nil]
          refine List.Perm.of_eq (List.filterMap_eq_nil_iff.2 ?_).symm
          intro x hx
          obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
          have hrT := visible_mem hr
          cases hg : go (View.mask v r) with
          | none => rfl
          | some row =>
            exfalso
            obtain ⟨row0, hm0⟩ := subj r hrT (List.mem_filter.1 hr).2 (by simp [hg])
            rw [hs] at hm0
            simp only [matchVal, Bool.false_eq_true, ↓reduceIte] at hm0
            by_cases heq : (dv st r.eid == c.canonical) = true
            · have := lookupId_dv hB hrT (mem_stmtIds_eid r)
              rw [beq_iff_eq.1 heq, hl] at this; cases this
            · rw [if_neg heq] at hm0; cases hm0
        | some e =>
          simp only []
          rw [ev_bind, ev_lookupEid]
          refine ⟨_, rfl, hsub e, key e ?_⟩
          intro r hrT ha hsome
          obtain ⟨row0, hm0⟩ := subj r hrT ha hsome
          rw [hs] at hm0
          simp only [matchVal, Bool.false_eq_true, ↓reduceIte] at hm0
          by_cases heq : (dv st r.eid == c.canonical) = true
          · have := lookupId_dv hB hrT (mem_stmtIds_eid r)
            rw [beq_iff_eq.1 heq, hl] at this; exact (Option.some.inj this).symm
          · rw [if_neg heq] at hm0; cases hm0
      | id o =>
        simp only []
        rw [ev_bind, ev_lookupEid]
        refine ⟨_, rfl, hsub o.raw, key o.raw ?_⟩
        intro r hrT ha hsome
        obtain ⟨row0, hm0⟩ := subj r hrT ha hsome
        rw [hs] at hm0
        simp only [matchVal, Env.at_st] at hm0
        cases hd : decodeId st o.raw with
        | error e => rw [hd] at hm0; cases hm0
        | ok w =>
          rw [hd] at hm0
          simp only [bind, Except.bind, pure, Except.pure] at hm0
          by_cases heq : (w == dv st r.eid) = true
          · rw [beq_iff_eq.1 heq] at hd
            exact (hB.idInj r hrT r.eid (mem_stmtIds_eid r) o.raw _ hd (decodeId_dv hB hrT (mem_stmtIds_eid r))).symm
          · rw [if_neg heq] at hm0; cases hm0
      | var x =>
        simp only []
        rw [ev_bind, ev_rangeScan st .spo v [] (by simp)]
        refine ⟨_, rfl, fun r hr => ?_, ?_⟩
        · have := (List.mergeSort_perm _ _).subset hr
          have := (scanList_perm st .spo v []).subset this
          exact ⟨(List.mem_filter.1 this).1, by simpa [ScanSpec.prefixOk, scanSpec] using (List.mem_filter.1 this).2⟩
        · refine ((((List.mergeSort_perm _ _).trans (scanList_perm st .spo v [])).map _).filterMap _).trans ?_
          apply List.Perm.of_eq
          congr 2
          unfold visibleRows
          apply List.filter_congr
          intro r _
          simp [ScanSpec.prefixOk, scanSpec]
      | param x =>
        simp only []
        rw [ev_bind, ev_rangeScan st .spo v [] (by simp)]
        refine ⟨_, rfl, fun r hr => ?_, ?_⟩
        · have := (List.mergeSort_perm _ _).subset hr
          have := (scanList_perm st .spo v []).subset this
          exact ⟨(List.mem_filter.1 this).1, by simpa [ScanSpec.prefixOk, scanSpec] using (List.mem_filter.1 this).2⟩
        · refine ((((List.mergeSort_perm _ _).trans (scanList_perm st .spo v [])).map _).filterMap _).trans ?_
          apply List.Perm.of_eq
          congr 2
          unfold visibleRows
          apply List.filter_congr
          intro r _
          simp [ScanSpec.prefixOk, scanSpec]
    obtain ⟨rows, hr1, hr2, hr3⟩ := hvr
    rw [virtualPat_eq, ev_bind, ev_resolveViewE, ← hv]
    simp only []
    rw [ev_bind, hr1]
    simp only []
    rw [ev_bind, hrow rows hr2]
    exact hfin _ hr3

/-! ## Inline values -/

omit hB in
theorem ev_valuesRowE (E : Env) (vs : List Var) : ∀ (cells : List (Var × Option TermOrVar)) (r0 : Row) {row : Row},
    cells.foldlM (fun r (v, c) => do
        match ← cellValue (E.at st).st c with
        | some val => return r.setAt ((E.at st).idx v) (some val)
        | none => return r) r0 = (.ok row : Except LErr Row) →
    ev st (cells.foldlM (fun r (v, c) => do
        match c with
        | some (.const k) => return r.setAt (E.idx v) (some k.canonical)
        | some (.id o) => return r.setAt (E.idx v) (some (← decodeE o.raw))
        | _ => return r) r0) = .ok (.ok row)
  | [], r0, row, h => by simp only [List.foldlM_nil] at h ⊢; cases h; rfl
  | (v, c) :: rest, r0, row, h => by
    simp only [List.foldlM_cons] at h ⊢
    cases hc : cellValue st c with
    | error e => simp [Env.at_st, hc, bind, Except.bind] at h
    | ok ov =>
      simp only [Env.at_st, hc, bind, Except.bind] at h
      rw [ev_bind]
      have step : ev st (match c with
          | some (.const k) => (return r0.setAt (E.idx v) (some k.canonical) : EvM Row)
          | some (.id o) => return r0.setAt (E.idx v) (some (← decodeE o.raw))
          | _ => return r0) = .ok (.ok (match ov with
            | some val => r0.setAt (E.idx v) (some val)
            | none => r0)) := by
        cases c with
        | none => simp only [cellValue] at hc; cases hc; rfl
        | some tv =>
          cases tv with
          | const k => simp only [cellValue] at hc; cases hc; rfl
          | id o =>
            simp only [cellValue] at hc
            cases hd : decodeId st o.raw with
            | error e => rw [hd] at hc; cases hc
            | ok w =>
              rw [hd] at hc; simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hc
              subst hc
              rw [ev_bind, ev_decodeE st hd]; rfl
          | var x => simp only [cellValue] at hc; cases hc; rfl
          | param x => simp only [cellValue] at hc; cases hc; rfl
      rw [step]
      simp only []
      apply ev_valuesRowE E vs rest
      cases ov <;> exact h

end

/-! ## Rows of a single stored pattern and match groups -/

/-- A row binds only positions in `is`. -/
def OnlyBinds (is : List Nat) (r : Row) : Prop := ∀ j, (r.get j).isSome → j ∈ is

theorem onlyBinds_mono {is is' : List Nat} (h : ∀ j ∈ is, j ∈ is') {r : Row} (hr : OnlyBinds is r) :
    OnlyBinds is' r := fun j hj => h j (hr j hj)

theorem onlyBinds_empty (n : Nat) : OnlyBinds [] (Row.empty n) := by
  intro j hj
  simp [Row.empty, Row.get, List.getElem?_replicate] at hj
  split at hj <;> simp at hj

theorem bindVal_only {E : Env} {v : Var} {w : Value} {r r' : Row} (h : bindVal E v w r = some r') {is : List Nat}
    (hr : OnlyBinds is r) : OnlyBinds (E.idx v :: is) r' := by
  unfold bindVal at h
  simp only at h
  split at h
  · split at h
    · cases h; exact onlyBinds_mono (fun j hj => List.mem_cons_of_mem _ hj) hr
    · cases h
  · cases h
    intro j hj
    by_cases hji : j = E.idx v
    · rw [hji]; exact List.mem_cons_self ..
    · rw [get_setAt_ne _ _ hji] at hj; exact List.mem_cons_of_mem _ (hr j hj)

theorem mpos_only {E : Env} {tv : TermOrVar} {w : Value} {y : Int64} {r r' : Row} (h : mpos E tv w y r = some r')
    {is : List Nat} (hr : OnlyBinds is r) : OnlyBinds (tv.vars.map E.idx ++ is) r' := by
  cases tv with
  | var v => simpa [TermOrVar.vars] using bindVal_only h hr
  | const c => simp only [mpos] at h; split at h <;> cases h; simpa [TermOrVar.vars] using hr
  | id o => simp only [mpos] at h; split at h <;> cases h; simpa [TermOrVar.vars] using hr
  | param _ => cases h

theorem sRows_only {st : ModelState} {E : Env} {v : Store.View} {t : TriplePattern} {r : TripleRow} {x : Row}
    (h : x ∈ sRows st E v t r) : OnlyBinds (t.vars.map E.idx) x := by
  unfold sRows m0 at h
  cases h1 : mpos E t.s (dv st r.s) r.s (Row.empty E.n) with
  | none => rw [h1] at h; cases h
  | some row1 =>
    rw [h1] at h
    simp only [Option.bind] at h
    have o1 := mpos_only h1 (onlyBinds_empty E.n)
    cases h2 : mpos E t.p (dv st r.p) r.p row1 with
    | none => rw [h2] at h; cases h
    | some row2 =>
      rw [h2] at h
      simp only at h
      have o2 := mpos_only h2 o1
      cases h3 : mpos E t.o (dv st r.o) r.o row2 with
      | none => rw [h3] at h; cases h
      | some row3 =>
        rw [h3] at h
        simp only at h
        have o3 := mpos_only h3 o2
        have fin : ∀ row4, OnlyBinds (t.eid.toList.map E.idx ++ (t.o.vars.map E.idx ++ (t.p.vars.map E.idx ++
            (t.s.vars.map E.idx ++ [])))) row4 → x ∈ gRows E t.graph (memList st v r.eid) row4 →
            OnlyBinds (t.vars.map E.idx) x := by
          intro row4 o4 hx
          have o5 : OnlyBinds (t.graph.vars.map E.idx ++ (t.eid.toList.map E.idx ++ (t.o.vars.map E.idx ++
              (t.p.vars.map E.idx ++ (t.s.vars.map E.idx ++ []))))) x := by
            cases hg : t.graph with
            | any => rw [hg] at hx; simp [gRows] at hx; subst hx; simpa [GraphSel.vars] using o4
            | set gs =>
              rw [hg] at hx; simp only [gRows] at hx
              split at hx
              · simp at hx; subst hx; simpa [GraphSel.vars] using o4
              · cases hx
            | var gv =>
              rw [hg] at hx
              simp only [gRows, List.mem_filterMap] at hx
              obtain ⟨_, _, hb⟩ := hx
              simpa [GraphSel.vars] using bindVal_only hb o4
          refine onlyBinds_mono (fun j hj => ?_) o5
          simp only [TriplePattern.vars, List.map_append, List.mem_append, List.append_nil] at hj ⊢
          tauto
        cases he : t.eid with
        | none =>
          rw [he] at h
          exact fin row3 (by simpa [he] using o3) h
        | some ev =>
          rw [he] at h
          simp only at h
          cases h4 : bindVal E ev (dv st r.eid) row3 with
          | none => rw [h4] at h; cases h
          | some row4 =>
            rw [h4] at h
            exact fin row4 (by simpa [he] using bindVal_only h4 o3) h

theorem tpBag_only {st : ModelState} {E : Env} {t : TriplePattern} {x : Row} (h : x ∈ tpBag st E t) :
    OnlyBinds (t.vars.map E.idx) x := by
  unfold tpBag at h
  simp only at h
  have h' : x ∈ (visibleRows st (resolveView st t.view)).flatMap (sRows st E (resolveView st t.view) t) := by
    split at h
    · exact List.mem_eraseDups.1 h
    · exact h
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.1 h'
  exact sRows_only hr

/-- A stored pattern binds at most one eid column of each match group. -/
def isoLocalV (iso : List (Nat × Nat)) (vars : List Var) (t : TriplePattern) : Prop :=
  ∀ g i j, (g, i) ∈ iso → (g, j) ∈ iso → i ≠ j →
    ¬ (i ∈ t.vars.map vars.idxOf ∧ j ∈ t.vars.map vars.idxOf)

/-- `isoLocalV` for an environment. -/
abbrev isoLocal (E : Env) (t : TriplePattern) : Prop := isoLocalV E.iso E.vars t

theorem isoFilter_tpBag {st : ModelState} {E : Env} {t : TriplePattern} (hi : isoLocal E t) {xs : Bag}
    (hx : ∀ x ∈ xs, x ∈ tpBag st E t) : isoFilter E.iso xs = xs := by
  unfold isoFilter
  split
  · rfl
  · apply List.filter_eq_self.2
    intro x hxm
    have ho := tpBag_only (hx x hxm)
    unfold isoOk
    rw [List.all_eq_true]
    intro ⟨g, i⟩ hgi
    rw [List.all_eq_true]
    intro ⟨h, j⟩ hhj
    by_cases hgh : g = h
    · subst hgh
      by_cases hij : i = j
      · subst hij; simp
      · have hn := hi g i j hgi hhj hij
        cases hxi : x.get i with
        | none => simp [hxi]
        | some a =>
          cases hxj : x.get j with
          | none => simp [hxi, hxj]
          | some b =>
            exfalso; apply hn
            exact ⟨ho i (by rw [hxi]; rfl), ho j (by rw [hxj]; rfl)⟩
    · simp [hgh]

/-! ## Conditions on the query -/

/-- A constant whose equality pushes into a key prefix compares by identity (always true:
`safeConst_all`; kept as a name for the former hypothesis). -/
def SafeConst (v : Value) : Prop := ∀ k, identityConst? (.const v.canonical) = some k → IdEq k

mutual

/-- The conditions the evaluator theorem needs of a query: constants of equalities compare by
identity, and stored patterns bind at most one eid column per match group. -/
def OpOk (iso : List (Nat × Nat)) (vars : List Var) : IR.Op → Prop
  | .triple t => isoLocalV iso vars t
  | .path _ => True
  | .values _ _ => True
  | .join xs => OpsOk iso vars xs
  | .union xs => OpsOk iso vars xs
  | .leftJoin l r c => OpOk iso vars l ∧ OpOk iso vars r ∧ OptOk iso vars c
  | .filter c x => ExprOk iso vars c ∧ OpOk iso vars x
  | .extend _ e x => ExprOk iso vars e ∧ OpOk iso vars x
  | .aggregate _ aggs x => AggsOk iso vars aggs ∧ OpOk iso vars x
  | .project _ _ x => OpOk iso vars x
  | .orderLimit keys _ _ x => KeysOk iso vars keys ∧ OpOk iso vars x

def OpsOk (iso : List (Nat × Nat)) (vars : List Var) : List IR.Op → Prop
  | [] => True
  | x :: xs => OpOk iso vars x ∧ OpsOk iso vars xs

def ExprOk (iso : List (Nat × Nat)) (vars : List Var) : Expr → Prop
  | .const _ => True
  | .cmp _ a b => ExprOk iso vars a ∧ ExprOk iso vars b
  | .sameTerm a b => ExprOk iso vars a ∧ ExprOk iso vars b
  | .arith _ a b => ExprOk iso vars a ∧ ExprOk iso vars b
  | .and xs => ExprsOk iso vars xs
  | .or xs => ExprsOk iso vars xs
  | .coalesce xs => ExprsOk iso vars xs
  | .func _ xs => ExprsOk iso vars xs
  | .not a => ExprOk iso vars a
  | .neg a => ExprOk iso vars a
  | .inList a xs _ => ExprOk iso vars a ∧ ExprsOk iso vars xs
  | .ite c a b => ExprOk iso vars c ∧ ExprOk iso vars a ∧ ExprOk iso vars b
  | .exists q _ => OpOk iso vars q
  | .var _ => True
  | .param _ => True
  | .bound _ => True

def ExprsOk (iso : List (Nat × Nat)) (vars : List Var) : List Expr → Prop
  | [] => True
  | x :: xs => ExprOk iso vars x ∧ ExprsOk iso vars xs

def OptOk (iso : List (Nat × Nat)) (vars : List Var) : Option Expr → Prop
  | none => True
  | some e => ExprOk iso vars e

def AggsOk (iso : List (Nat × Nat)) (vars : List Var) : List (Var × AggFunc × Option Expr × Bool) → Prop
  | [] => True
  | (_, _, a, _) :: rest => OptOk iso vars a ∧ AggsOk iso vars rest

def KeysOk (iso : List (Nat × Nat)) (vars : List Var) : List (Expr × Bool) → Prop
  | [] => True
  | (e, _) :: rest => ExprOk iso vars e ∧ KeysOk iso vars rest

end

/-- A resolved constant that can become a key prefix compares by identity. -/
def ConstOk (e : RExpr) : Prop := ∀ k, identityConst? e = some k → IdEq k

/-- A pushed equality of a resolved conjunct has an identity constant. -/
def PrefOk (e : RExpr) : Prop := ∀ i k, prefixEq? e = some (i, k) → IdEq k

theorem prefOk_of {e : RExpr} (h : ∀ a b, e = .cmp .eq a b → ConstOk a ∧ ConstOk b) : PrefOk e := by
  intro i k hp
  unfold prefixEq? at hp
  split at hp
  · next i' b =>
    cases hb : identityConst? b with
    | none => rw [hb] at hp; cases hp
    | some k' =>
      rw [hb] at hp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact (h _ _ rfl).2 _ hb
  · next a i' _ =>
    cases ha : identityConst? a with
    | none => rw [ha] at hp; cases hp
    | some k' =>
      rw [ha] at hp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact (h _ _ rfl).1 _ ha
  · cases hp

/-- Every resolved constant that can become a key prefix compares by identity. -/
theorem constOk_all (e : RExpr) : ConstOk e := fun _ hk => identityConst_idEq hk

/-- Every pushed equality's constant compares by identity. -/
theorem prefOk_all (e : RExpr) : PrefOk e := prefOk_of fun _ _ _ => ⟨constOk_all _, constOk_all _⟩

/-- Every constant is safe (the former hypothesis on queries is now a theorem). -/
theorem safeConst_all (v : Value) : SafeConst v := fun _ hk => identityConst_idEq hk

theorem constOk_of {e : RExpr} (h : ∀ k, e ≠ .const k) : ConstOk e := by
  intro k hk; exact absurd (identityConst_some hk) (h k)

theorem prefOk_ne {e : RExpr} (h : ∀ a b, e ≠ .cmp .eq a b) : PrefOk e :=
  prefOk_of fun a b he => absurd he (h a b)

/-! ## Small facts for the main induction -/

@[simp] theorem ev_liftEx_ok {α : Type} (st : ModelState) (a : α) : ev st (liftEx (.ok a)) = .ok (.ok a) := rfl

theorem tri_and (xs : List RExpr) (r : Row) : (RExpr.and xs).tri r = triAnd (xs.map (·.tri r)) := by
  have ht : RExpr.tris r xs = xs.map (·.tri r) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [RExpr.tris, List.map_cons, ih]; rfl
  show Tri.ofOpt (((RExpr.and xs).eval r).bind ebv) = _
  simp only [RExpr.eval]
  rw [ht]
  generalize triAnd (List.map (fun x => RExpr.tri r x) xs) = T
  cases T <;> rfl

theorem holds_and (xs : List RExpr) (r : Row) : (RExpr.and xs).holds r = xs.all (·.holds r) := by
  rw [show (RExpr.and xs).holds r = ((RExpr.and xs).tri r == .t) from rfl, tri_and]
  unfold triAnd
  by_cases hf : (xs.map (·.tri r)).contains .f = true
  · rw [if_pos hf]
    obtain ⟨x, hx, hxf⟩ : ∃ x ∈ xs, x.tri r = .f := by simpa using hf
    have : xs.all (·.holds r) = false := by
      rw [List.all_eq_false]; exact ⟨x, hx, by simp [RExpr.holds, hxf]⟩
    rw [this]; rfl
  · rw [if_neg hf]
    by_cases he : (xs.map (·.tri r)).contains .err = true
    · rw [if_pos he]
      obtain ⟨x, hx, hxe⟩ : ∃ x ∈ xs, x.tri r = .err := by simpa using he
      have : xs.all (·.holds r) = false := by
        rw [List.all_eq_false]; exact ⟨x, hx, by simp [RExpr.holds, hxe]⟩
      rw [this]; rfl
    · rw [if_neg he]
      have : xs.all (·.holds r) = true := by
        rw [List.all_eq_true]
        intro x hx
        simp only [RExpr.holds, beq_iff_eq]
        cases h : x.tri r
        · rfl
        · exact absurd (by simpa using ⟨x, hx, h⟩ : (xs.map (·.tri r)).contains .f = true) hf
        · exact absurd (by simpa using ⟨x, hx, h⟩ : (xs.map (·.tri r)).contains .err = true) he
      rw [this]; rfl

theorem splitAnd_holds (e : RExpr) (r : Row) : (splitAnd e).all (·.holds r) = e.holds r := by
  cases e with
  | and xs => simp only [splitAnd]; rw [holds_and]
  | _ => simp [splitAnd]

theorem allHold_ofR (cs : List RExpr) (r : Row) : allHold (cs.map Pushed.ofR) r = cs.all (·.holds r) := by
  unfold allHold; rw [List.all_map]; rfl

theorem foldl_filterB_R (cs : List RExpr) : ∀ rows : Bag,
    cs.foldl (fun r c => filterB c r) rows = rows.filter fun r => cs.all (·.holds r) := by
  have := foldl_filterB (cs.map Pushed.ofR)
  intro rows
  have h2 := this rows
  simp only [List.foldl_map, Pushed.ofR] at h2
  rw [h2]
  congr 1; funext r; rw [allHold_ofR]

theorem isoFilter_filter (iso : List (Nat × Nat)) (f : Row → Bool) (L : Bag) :
    isoFilter iso (L.filter f) = (isoFilter iso L).filter f := by
  unfold isoFilter; split
  · rfl
  · rw [List.filter_filter, List.filter_filter]; congr 1; funext r; rw [Bool.and_comm]

theorem joinB_unit (m : Missing) (Q : Schema) (B : Bag) : joinB m [] Q [[]] B = B := by
  unfold joinB
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  induction B with
  | nil => rfl
  | cons b bs ih =>
    rw [List.filterMap_cons, compat_unit_left]
    simp only [ite_true]
    rw [ih]; rfl

theorem compat_bits {m : Missing} {P Q Q' : Schema} (h : ∀ i, bit Q i = bit Q' i) (a b : Row) :
    compat m P Q a b = compat m P Q' a b := by
  rw [Bool.eq_iff_iff, compat_iff, compat_iff]
  exact forall_congr' fun i => by rw [h i]

theorem leftJoinB_bits (m : Missing) (P : Schema) {Q Q' : Schema} (h : ∀ i, bit Q i = bit Q' i)
    (c : Option RExpr) (xs ys : Bag) : leftJoinB m P Q c xs ys = leftJoinB m P Q' c xs ys := by
  unfold leftJoinB
  simp only [compat_bits h]

theorem foldl_union_map {α : Type} (vs : List α) : ∀ (fs : List (α → Bool)) (f : α → Bool),
    (fs.map fun g => vs.map g).foldl Schema.union (vs.map f) = vs.map fun v => f v || fs.any fun g => g v
  | [], f => by simp
  | g :: gs, f => by
    simp only [List.map_cons, List.foldl_cons, union_map]
    rw [foldl_union_map vs gs]
    congr 1; funext v
    simp [List.any_cons, Bool.or_assoc]

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem liftL_ok {α : Type} {x : Except LErr α} {a : α} (h : liftL x = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok a' => cases h; rfl

/-- The pattern join on a model state: one stored pattern. -/
theorem joinAll_single (m : Missing) (n : Nat) (Q : Schema) (B : Bag) : (joinAll m n [(Q, B)]).2 = B := by
  simp [joinAll, joinSB, unitSB, joinB_unit]

section
variable {st : ModelState} (hB : IdBridge st)
include hB

theorem ev_joinCore_single {E : Env} {pathE : PathE} {pb : PathSem} (hp : PathSim st E pathE pb)
    {t : TriplePattern} (ht : t.p.virtual? = none) (hi : isoLocal E t) (conds : List Pushed)
    (hok : ∀ c ∈ conds, PushedOk c) :
    ∃ R, ev st (joinCore E pathE [.triple t] [none] conds) = .ok (.ok R) ∧
      R.Perm ((tpBag st E t).filter (allHold conds)) := by
  have hs : storedPat? (.triple t) = some t := by simp [storedPat?, ht]
  have := ev_joinCore hB hp [(.triple t, none, some (tpBag st E t))]
    (fun i hi' => by
      simp only [List.mem_singleton] at hi'; subst hi'
      exact Or.inl ⟨t, hs, rfl, rfl⟩) conds hok (L := tpBag st E t) (by
      simp only [othD, List.filterMap_cons, Option.map_some, List.filterMap_nil, List.map_cons, List.map_nil,
        List.filterMap_cons, Op.pathPat?]
      simp only [lateralPaths, joinAll_single])
  obtain ⟨R, h1, h2⟩ := this
  refine ⟨R, h1, h2.trans (List.Perm.of_eq ?_)⟩
  exact isoFilter_tpBag hi (fun x hx => (List.mem_filter.1 hx).1)

end

/-! ## Operator facts -/

theorem checkOp_virtual {t : TriplePattern} {u : Unit} (h : checkOp (.triple t) = .ok u) {vp : VirtualPred}
    (hv : t.p.virtual? = some vp) : t.eid = none := by
  simp only [checkOp] at h
  obtain ⟨_, _, h⟩ := bind_ok h
  rw [hv] at h
  simp only at h
  cases he : t.eid with
  | none => rfl
  | some _ => rw [he] at h; simp [invalid] at h

theorem denote_join_ok {Ed : Env} {pb : PathSem} {xs : List IR.Op} {b : Bag} (h : denote Ed pb (.join xs) = .ok b) :
    ∃ dbs L, denoteInputs Ed pb xs = .ok dbs ∧
      lateralPaths Ed pb (joinAll Ed.sem.missing Ed.n ((xs.zip dbs).filterMap fun (x, b) => b.map (Ed.schemaOf x, ·))).1
        (joinAll Ed.sem.missing Ed.n ((xs.zip dbs).filterMap fun (x, b) => b.map (Ed.schemaOf x, ·))).2
        (xs.filterMap Op.pathPat?) = .ok L ∧ b = isoFilter Ed.iso L := by
  rw [denote.eq_4] at h
  obtain ⟨dbs, h1, h⟩ := bind_ok h
  simp only [] at h
  generalize hJ : joinAll Ed.sem.missing Ed.n _ = J at h
  obtain ⟨P, rows⟩ := J
  simp only [] at h
  obtain ⟨L, h2, h⟩ := bind_ok h
  refine ⟨dbs, L, h1, ?_, ?_⟩
  · rw [hJ]; exact liftL_ok h2
  · cases h; rfl

/-- The reference join of a list of stored patterns. -/
theorem patJoin_single (st : ModelState) (E : Env) (t : TriplePattern) :
    patJoin st E [t] = (E.schemaOf (.triple t), tpBag st E t) := by
  unfold patJoin
  simp [joinAll, joinSB, unitSB, joinB_unit, Schema.union]

theorem filterMap_length_eq {α β : Type} {f : α → Option β} : ∀ {l : List α}, (l.filterMap f).length = l.length →
    ∀ x ∈ l, ∃ y, f x = some y
  | [], _, x, hx => by cases hx
  | a :: as, h, x, hx => by
    rw [List.filterMap_cons] at h
    cases ha : f a with
    | none =>
      rw [ha] at h
      have := List.length_filterMap_le f as
      simp at h; omega
    | some b =>
      rw [ha] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, ha⟩
      · exact filterMap_length_eq h x hx

theorem stored_list_eq : ∀ {xs : List IR.Op}, (∀ x ∈ xs, ∃ t, storedPat? x = some t) →
    xs = (xs.filterMap storedPat?).map (.triple ·)
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨t, ht⟩ := h x (List.mem_cons_self ..)
    rw [List.filterMap_cons, ht, List.map_cons, ← (storedPat_some ht).1,
      ← stored_list_eq (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem joinAll_fst (m : Missing) (n : Nat) (L : List SBag) : (joinAll m n L).1 = (L.map (·.1)).foldl Schema.union [] := by
  unfold joinAll
  suffices ∀ a : SBag, (L.foldl (joinSB m) a).1 = (L.map (·.1)).foldl Schema.union a.1 from this _
  induction L with
  | nil => intro a; rfl
  | cons x xs ih => intro a; simp only [List.foldl_cons, List.map_cons]; rw [ih]; rfl

section
variable {st : ModelState} (hB : IdBridge st)
include hB

theorem denoteInputs_stored {E : Env} {pb : PathSem} : ∀ (pats : List TriplePattern),
    (∀ t ∈ pats, t.p.virtual? = none) → ∀ {dbs}, denoteInputs (E.at st) pb (pats.map (.triple ·)) = .ok dbs →
    dbs = pats.map fun t => some (tpBag st E t)
  | [], _, dbs, h => by simp only [List.map_nil, denoteInputs] at h; cases h; rfl
  | t :: ts, hv, dbs, h => by
    simp only [List.map_cons, denoteInputs] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    rw [denote_triple_eq hB E pb (hv t (List.mem_cons_self ..)) hb,
      denoteInputs_stored ts (fun u hu => hv u (List.mem_cons_of_mem _ hu)) hbs]
    rfl

theorem sideways_rel {E : Env} {pb : PathSem} (hiso : E.iso = []) {r : IR.Op} {pats : List TriplePattern}
    (hs : sidewaysPats r = some pats) {rb : Bag} (hd : denote (E.at st) pb r = .ok rb) :
    E.schemaOf r = (patJoin st E pats).1 ∧ rb.Perm (patJoin st E pats).2 := by
  cases r with
  | triple t =>
    simp only [sidewaysPats] at hs
    cases ht : storedPat? (.triple t) with
    | none => rw [ht] at hs; cases hs
    | some t' =>
      rw [ht] at hs; simp only [Option.map_some, Option.some.injEq] at hs; subst hs
      obtain ⟨he, hv⟩ := storedPat_some ht
      cases he
      rw [patJoin_single, denote_triple_eq hB E pb hv hd]
      exact ⟨rfl, List.Perm.refl _⟩
  | join xs =>
    simp only [sidewaysPats] at hs
    split at hs
    · next hc =>
      cases hs
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
      have hall := filterMap_length_eq hc.1
      have hxs := stored_list_eq hall
      set pats := xs.filterMap storedPat?
      have hv : ∀ t ∈ pats, t.p.virtual? = none := by
        intro t htm
        obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 htm
        exact (storedPat_some hx).2
      obtain ⟨dbs, L, h1, h2, h3⟩ := denote_join_ok hd
      rw [hxs] at h1 h2
      have hdbs := denoteInputs_stored hB pats hv h1
      have hoth : (((pats.map (.triple ·)).zip dbs).filterMap fun (x, b) => b.map ((E.at st).schemaOf x, ·)) =
          pats.map fun t => (E.schemaOf (.triple t), tpBag st E t) := by
        rw [hdbs, List.zip_map', List.filterMap_map, ← List.filterMap_eq_map]
        rfl
      rw [hoth] at h2
      have hnp : (pats.map (.triple ·)).filterMap Op.pathPat? = [] := by
        rw [List.filterMap_map]; exact List.filterMap_eq_nil_iff.2 fun _ _ => rfl
      rw [hnp] at h2
      simp only [lateralPaths, Except.ok.injEq] at h2
      rw [h3, Env.at_iso, hiso, ← h2]
      refine ⟨?_, by simp [isoFilter, patJoin]⟩
      rw [hxs, schemaOf_join]
      unfold patJoin
      rw [joinAll_fst, List.map_map]
      obtain ⟨t0, ts, hts⟩ : ∃ t0 ts, pats = t0 :: ts := by
        cases hp : pats with
        | nil => exfalso; rw [hxs, hp] at hc; simp at hc
        | cons t0 ts => exact ⟨t0, ts, rfl⟩
      rw [hts]
      simp only [List.map_cons, List.foldl_cons, Function.comp_def, Env.schemaOf]
      rw [show Schema.union [] (E.vars.map (scope (.triple t0)).binds) = E.vars.map (scope (.triple t0)).binds by
        cases E.vars <;> simp [Schema.union]]
      have := foldl_union_map E.vars (ts.map fun t => (scope (.triple t)).binds) (scope (.triple t0)).binds
      rw [List.map_map] at this
      rw [show (ts.map fun x => List.map (scope (Op.triple x)).binds E.vars) =
        ts.map ((fun g => List.map g E.vars) ∘ fun t => (scope (Op.triple t)).binds) from rfl, this]
      congr 1; funext v
      simp [List.any_map, Function.comp_def]
    · cases hs
  | _ => simp [sidewaysPats] at hs

end

end Tiramemsu.Exec
