/-
The evaluator equals the reference semantics on the model store, operator by operator (the
induction behind query-semantics "Reference semantics"): soundness direction, as bags; resolved
expressions agree up to the order of `EXISTS` bags.
-/
import TiramemsuProofs.Query.EvalDenote

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-- What a resolved expression of the evaluator satisfies against the reference one. -/
def ExprSim (e'' e' : RExpr) : Prop := EqE e'' e' ∧ ConstOk e'' ∧ PrefOk e'' ∧ ∀ c ∈ splitAnd e'', PrefOk c

theorem exprSim_of {e'' e' : RExpr} (h : EqE e'' e') (hc : ∀ k, e'' ≠ .const k) (hp : PrefOk e'')
    (hn : ∀ xs, e'' ≠ .and xs) : ExprSim e'' e' := by
  refine ⟨h, constOk_of hc, hp, fun c hc' => ?_⟩
  cases e'' with
  | and xs => exact absurd rfl (hn xs)
  | _ => simp only [splitAnd, List.mem_singleton] at hc'; subst hc'; exact hp

theorem flatten_perm : ∀ {xs ys : List Bag}, List.Forall₂ List.Perm xs ys → xs.flatten.Perm ys.flatten
  | [], [], _ => List.Perm.refl _
  | _ :: _, _ :: _, .cons h hs => by simp only [List.flatten_cons]; exact h.append (flatten_perm hs)

section
variable {st : ModelState} (hB : IdBridge st) {E : Env} {pathE : PathE} {pb : PathSem} (hp : PathSim st E pathE pb)
include hB hp

omit hB hp in
/-- `Filter` over an operator evaluated by itself. -/
theorem filter_other {cs : List RExpr} {c' : RExpr} (hcs : ∀ r, cs.all (·.holds r) = c'.holds r)
    {x : EvM Bag} {bx : Bag} (hx : ∃ b', ev st x = .ok (.ok b') ∧ b'.Perm bx) :
    ∃ b', ev st (do let b ← x; pure (cs.foldl (fun r c => filterB c r) b)) = .ok (.ok b') ∧
      b'.Perm (filterB c' bx) := by
  obtain ⟨b', h1, h2⟩ := hx
  rw [ev_bind, h1]
  refine ⟨_, rfl, ?_⟩
  rw [foldl_filterB_R]
  unfold filterB
  rw [show (fun r => cs.all (·.holds r)) = c'.holds from funext hcs]
  exact h2.filter _

mutual

theorem eval_sim : ∀ (op : IR.Op), OpOk E.iso E.vars op → ∀ b, denote (E.at st) pb op = .ok b →
    ∃ b', ev st (eval E pathE op) = .ok (.ok b') ∧ b'.Perm b
  | .triple t, hok, b, hd => by
    rw [denote.eq_1] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    have hd' := liftL_ok hd
    rw [eval.eq_1, hc, ev_bind_ok st (ev_liftEx_ok st u)]
    cases hv : t.p.virtual? with
    | some vp =>
      simp only []
      exact ev_virtualPat hB E hv (checkOp_virtual hc hv) hd'
    | none =>
      simp only []
      obtain ⟨R, h1, h2⟩ := ev_joinCore_single hB hp hv hok [] (fun _ h => by cases h) (fun _ h => by cases h)
      refine ⟨R, h1, h2.trans (List.Perm.of_eq ?_)⟩
      rw [triplePat_eq hB E hv] at hd'
      cases hd'
      exact List.filter_eq_self.2 fun _ _ => rfl
  | .path p, _, b, hd => by
    rw [denote.eq_2] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    rw [eval.eq_2, hc, ev_bind_ok st (ev_liftEx_ok st u)]
    exact hp p [] b (liftL_ok hd)
  | .values vs rows, _, b, hd => by
    rw [denote.eq_3] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    have hd' := liftL_ok hd
    rw [eval.eq_3, hc, ev_bind_ok st (ev_liftEx_ok st u)]
    unfold valuesB at hd'
    have hall := mapM_ok_mem hd'
    rw [mapM_ok_okv hall] at hd'
    cases hd'
    refine ⟨_, ev_mapM st _ (fun cells hcells => ?_), List.Perm.refl _⟩
    obtain ⟨row, hrow⟩ := hall cells hcells
    rw [okv_ok hrow]
    exact ev_valuesRowE E vs _ _ hrow
  | .join xs, hok, b, hd => by
    obtain ⟨dbs, L, h1, h2, h3⟩ := denote_join_ok hd
    obtain ⟨ebs, he, ins, hx1, hx2, hx3, hrel⟩ := evalInputs_sim xs hok dbs h1
    rw [eval.eq_4, ev_bind, he]
    simp only []
    subst hx1 hx2 hx3
    rw [othD_eq] at h2
    obtain ⟨R, hR1, hR2⟩ := ev_joinCore hB hp ins hrel [] (fun _ h => by cases h) (fun _ h => by cases h) h2
    refine ⟨R, hR1, hR2.trans (List.Perm.of_eq ?_)⟩
    rw [h3, show L.filter (allHold []) = L from List.filter_eq_self.2 (fun _ _ => rfl)]
    rfl
  | .leftJoin l r c, hok, b, hd => by
    obtain ⟨hl, hr, hc⟩ := hok
    rw [denote.eq_5] at hd
    obtain ⟨lb, hlb, hd⟩ := bind_ok hd
    obtain ⟨rb, hrb, hd⟩ := bind_ok hd
    obtain ⟨c', hc', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨lb', hlb', hlp⟩ := eval_sim l hl lb hlb
    obtain ⟨c'', hc'', hcc⟩ := resolveOptX_sim c hc c' hc'
    rw [eval.eq_5, ev_bind, hlb']
    simp only []
    rw [ev_bind, hc'']
    simp only []
    by_cases hiso : E.iso.isEmpty = true
    · have hiso' : E.iso = [] := List.isEmpty_iff.1 hiso
      cases hs : sidewaysPats r with
      | some pats =>
        simp only [hiso, ite_true, hs]
        obtain ⟨R, hR1, hR2⟩ := ev_leftJoinSideways hB E (E.schemaOf l) c'' pats lb'
        obtain ⟨hQ, hrbp⟩ := sideways_rel hB hiso' hs hrb
        refine ⟨R, hR1, hR2.trans ?_⟩
        rw [Env.at_iso, Env.at_sem, Env.at_schemaOf, hQ]
        exact isoFilter_perm _ (leftJoinB_rel _ _ _ hcc hlp hrbp.symm)
      | none =>
        simp only [hiso, ite_true, hs]
        obtain ⟨rb', hrb', hrp⟩ := eval_sim r hr rb hrb
        rw [ev_bind, hrb']
        exact ⟨_, rfl, isoFilter_perm _ (leftJoinB_rel _ _ _ hcc hlp hrp)⟩
    · simp only [hiso, Bool.false_eq_true, ite_false]
      obtain ⟨rb', hrb', hrp⟩ := eval_sim r hr rb hrb
      rw [ev_bind, hrb']
      exact ⟨_, rfl, isoFilter_perm _ (leftJoinB_rel _ _ _ hcc hlp hrp)⟩
  | .union xs, hok, b, hd => by
    rw [denote.eq_6] at hd
    obtain ⟨bs, hbs, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨bs', h1, h2⟩ := evalList_sim xs hok bs hbs
    rw [eval.eq_6, ev_bind, h1]
    exact ⟨_, rfl, flatten_perm h2⟩
  | .filter c x, hok, b, hd => by
    obtain ⟨hc, hx⟩ := hok
    rw [denote.eq_7] at hd
    obtain ⟨c', hc', hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨c'', hc'', heq, _, _, hpa⟩ := resolveX_sim c hc c' hc'
    rw [eval.eq_7, ev_bind, hc'']
    simp only []
    have hcs : ∀ r, (splitAnd c'').all (·.holds r) = c'.holds r := fun r => by
      rw [splitAnd_holds, heq.holds]
    have hpush : ∀ c ∈ (splitAnd c'').map Pushed.ofR, PushedOk c := by
      intro c hc; obtain ⟨e, _, rfl⟩ := List.mem_map.1 hc; exact pushedOk_ofR e
    have hidc : ∀ c ∈ (splitAnd c'').map Pushed.ofR, ∀ i k, prefixEq? c.cond = some (i, k) → IdEq k := by
      intro c hc i k hpk; obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc; exact hpa e he i k hpk
    have hfa : ∀ r, allHold ((splitAnd c'').map Pushed.ofR) r = c'.holds r := fun r => by
      rw [allHold_ofR, hcs]
    cases x with
    | join xs =>
      simp only []
      obtain ⟨dbs, L, h1, h2, h3⟩ := denote_join_ok hbx
      obtain ⟨ebs, he, ins, hx1, hx2, hx3, hrel⟩ := evalInputs_sim xs hx dbs h1
      rw [ev_bind, he]
      simp only []
      subst hx1 hx2 hx3
      rw [othD_eq] at h2
      obtain ⟨R, hR1, hR2⟩ := ev_joinCore hB hp ins hrel _ hpush hidc h2
      refine ⟨R, hR1, hR2.trans (List.Perm.of_eq ?_)⟩
      rw [h3, Env.at_iso, isoFilter_filter]
      unfold filterB
      congr 1; funext r; exact hfa r
    | triple t =>
      simp only []
      rw [denote.eq_1] at hbx
      obtain ⟨u, hcu, hbx⟩ := bind_ok hbx
      have hbx' := liftL_ok hbx
      cases hv : t.p.virtual? with
      | none =>
        simp only []
        rw [hcu, ev_bind_ok st (ev_liftEx_ok st u)]
        obtain ⟨R, h1, h2⟩ := ev_joinCore_single hB hp hv hx _ hpush hidc
        refine ⟨R, h1, h2.trans (List.Perm.of_eq ?_)⟩
        rw [triplePat_eq hB E hv] at hbx'
        cases hbx'
        unfold filterB
        congr 1; funext r; exact hfa r
      | some vp =>
        simp only []
        rw [hcu, ev_bind_ok st (ev_liftEx_ok st u)]
        exact filter_other hcs (ev_virtualPat hB E hv (checkOp_virtual hcu hv) hbx')
    | path p => exact filter_other hcs (eval_sim _ hx bx hbx)
    | values vs rows => exact filter_other hcs (eval_sim _ hx bx hbx)
    | leftJoin l r c => exact filter_other hcs (eval_sim _ hx bx hbx)
    | union xs => exact filter_other hcs (eval_sim _ hx bx hbx)
    | filter c x => exact filter_other hcs (eval_sim _ hx bx hbx)
    | extend v e x => exact filter_other hcs (eval_sim _ hx bx hbx)
    | aggregate g a x => exact filter_other hcs (eval_sim _ hx bx hbx)
    | project vs d x => exact filter_other hcs (eval_sim _ hx bx hbx)
    | orderLimit k s l x => exact filter_other hcs (eval_sim _ hx bx hbx)
  | .extend v e x, hok, b, hd => by
    obtain ⟨he, hx⟩ := hok
    rw [denote.eq_8] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨e', he', hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨e'', he'', heq, _⟩ := resolveX_sim e he e' he'
    obtain ⟨bx', hbx', hxp⟩ := eval_sim x hx bx hbx
    rw [eval.eq_8, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, he'']
    simp only []
    rw [ev_bind, hbx']
    exact ⟨_, rfl, extendB_rel _ heq hxp⟩
  | .aggregate g aggs x, hok, b, hd => by
    obtain ⟨ha, hx⟩ := hok
    rw [denote.eq_9] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨as', ha', hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨as'', ha'', haeq⟩ := resolveAggsX_sim aggs ha as' ha'
    obtain ⟨bx', hbx', hxp⟩ := eval_sim x hx bx hbx
    rw [eval.eq_9, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, ha'']
    simp only []
    rw [ev_bind, hbx']
    refine ⟨_, rfl, ?_⟩
    rw [aggregateB_congr _ _ haeq]
    exact aggregateB_perm _ _ _ hxp
  | .project vs d x, hok, b, hd => by
    rw [denote.eq_10] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨bx', hbx', hxp⟩ := eval_sim x hok bx hbx
    rw [eval.eq_10, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, hbx']
    exact ⟨_, rfl, projectB_perm _ _ hxp⟩
  | .orderLimit keys s l x, hok, b, hd => by
    obtain ⟨hk, hx⟩ := hok
    rw [denote.eq_11] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    obtain ⟨ks', hk', hd⟩ := bind_ok hd
    obtain ⟨sk, hs, hd⟩ := bind_ok hd
    obtain ⟨lm, hl, hd⟩ := bind_ok hd
    obtain ⟨bx, hbx, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨ks'', hk'', hkeq⟩ := resolveKeysX_sim keys hk ks' hk'
    obtain ⟨bx', hbx', hxp⟩ := eval_sim x hx bx hbx
    rw [eval.eq_11, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, hk'']
    simp only []
    rw [ev_bind, hs, ev_liftEx_ok]
    simp only []
    rw [ev_bind, hl, ev_liftEx_ok]
    simp only []
    rw [ev_bind, hbx']
    refine ⟨_, rfl, List.Perm.of_eq ?_⟩
    rw [orderLimitB_congr _ hkeq, orderLimitB_perm _ _ _ _ hxp]
    rfl

theorem evalList_sim : ∀ (xs : List IR.Op), OpsOk E.iso E.vars xs → ∀ bs, denoteList (E.at st) pb xs = .ok bs →
    ∃ bs', ev st (evalList E pathE xs) = .ok (.ok bs') ∧ List.Forall₂ List.Perm bs' bs
  | [], _, bs, hd => by
    simp only [denoteList] at hd; cases hd
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | x :: xs, hok, bs, hd => by
    obtain ⟨hx, hxs⟩ := hok
    simp only [denoteList] at hd
    obtain ⟨b, hb, hd⟩ := bind_ok hd
    obtain ⟨bs0, hbs, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨b', hb', hp1⟩ := eval_sim x hx b hb
    obtain ⟨bs', hbs', hp2⟩ := evalList_sim xs hxs bs0 hbs
    simp only [evalList]
    rw [ev_bind, hb']
    simp only []
    rw [ev_bind, hbs']
    exact ⟨_, rfl, List.Forall₂.cons hp1 hp2⟩

theorem evalInputs_sim : ∀ (xs : List IR.Op), OpsOk E.iso E.vars xs → ∀ dbs, denoteInputs (E.at st) pb xs = .ok dbs →
    ∃ ebs, ev st (evalInputs E pathE xs) = .ok (.ok ebs) ∧
      ∃ ins : List (IR.Op × Option Bag × Option Bag), ins.map (·.1) = xs ∧ ins.map (·.2.1) = ebs ∧
        ins.map (·.2.2) = dbs ∧ ∀ i ∈ ins, InRel st E i.1 i.2.1 i.2.2
  | [], _, dbs, hd => by
    simp only [denoteInputs] at hd; cases hd
    exact ⟨[], rfl, [], rfl, rfl, rfl, fun _ h => by cases h⟩
  | x :: xs, hok, dbs, hd => by
    obtain ⟨hx, hxs⟩ := hok
    by_cases hpath : ∃ p, x = .path p
    · obtain ⟨p, rfl⟩ := hpath
      rw [denoteInputs.eq_2] at hd
      obtain ⟨u, hc, hd⟩ := bind_ok hd
      obtain ⟨ds, hds, hd⟩ := bind_ok hd
      cases hd
      obtain ⟨ebs, he, ins, h1, h2, h3, hrel⟩ := evalInputs_sim xs hxs ds hds
      rw [evalInputs.eq_3, hc, ev_bind_ok st (ev_liftEx_ok st u)]
      simp only [pure_bind]
      rw [ev_bind, he]
      refine ⟨_, rfl, (.path p, none, none) :: ins, by simp [h1], by simp [h2], by simp [h3], ?_⟩
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact Or.inr (Or.inl ⟨⟨p, rfl⟩, rfl, rfl⟩)
      · exact hrel i hi
    · have hnp : ∀ p, x = .path p → False := fun p h => hpath ⟨p, h⟩
      rw [denoteInputs.eq_3 _ _ _ _ hnp] at hd
      obtain ⟨b, hb, hd⟩ := bind_ok hd
      obtain ⟨ds, hds, hd⟩ := bind_ok hd
      cases hd
      obtain ⟨ebs, he, ins, h1, h2, h3, hrel⟩ := evalInputs_sim xs hxs ds hds
      cases hst : storedPat? x with
      | some t =>
        obtain ⟨hxt, hv⟩ := storedPat_some hst
        subst hxt
        have hb' := hb
        rw [denote.eq_1] at hb'
        obtain ⟨u, hc, _⟩ := bind_ok hb'
        rw [evalInputs.eq_2 _ _ _ _ _ hst, hc, ev_bind_ok st (ev_liftEx_ok st u)]
        simp only [pure_bind]
        rw [ev_bind, he]
        refine ⟨_, rfl, (.triple t, none, some b) :: ins, by simp [h1], by simp [h2], by simp [h3], ?_⟩
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact Or.inl ⟨t, hst, rfl, by rw [denote_triple_eq hB E pb hv hb]⟩
        · exact hrel i hi
      | none =>
        obtain ⟨b', hb', hbp⟩ := eval_sim x hx b hb
        rw [evalInputs.eq_4 _ _ _ _ hnp hst, ev_bind, hb']
        simp only [pure_bind]
        rw [ev_bind, he]
        refine ⟨_, rfl, (x, some b', some b) :: ins, by simp [h1], by simp [h2], by simp [h3], ?_⟩
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact Or.inr (Or.inr ⟨hst, fun p h => hnp p h, b', b, rfl, rfl, hbp⟩)
        · exact hrel i hi

theorem resolveX_sim : ∀ (e : Expr), ExprOk E.iso E.vars e → ∀ e', resolveE (E.at st) pb e = .ok e' →
    ∃ e'', ev st (resolveX E pathE e) = .ok (.ok e'') ∧ ExprSim e'' e'
  | .var v, _, e', hd => by
    simp only [resolveE] at hd; cases hd
    refine ⟨_, rfl, ?_⟩
    simp only [Env.at_vars, Env.at_idx]
    by_cases hv : E.vars.contains v = true
    · simp only [hv, ite_true]
      exact exprSim_of (EqE.refl _) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h) (fun _ h => by cases h)
    · simp only [hv, Bool.false_eq_true, ite_false]
      exact exprSim_of (EqE.refl _) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h) (fun _ h => by cases h)
  | .const v, hok, e', hd => by
    simp only [resolveE] at hd; cases hd
    refine ⟨_, rfl, EqE.refl _, fun k hk => ?_, (prefOk_ne fun _ _ h => by cases h), ?_⟩
    · exact hok k hk
    · intro c hc; simp only [splitAnd, List.mem_singleton] at hc; subst hc; exact prefOk_ne fun _ _ h => by cases h
  | .param _, _, e', hd => by
    simp only [resolveE] at hd; cases hd
    exact ⟨_, rfl, exprSim_of (EqE.refl _) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩
  | .bound v, _, e', hd => by
    simp only [resolveE] at hd; cases hd
    refine ⟨_, rfl, ?_⟩
    simp only [Env.at_vars, Env.at_idx]
    by_cases hv : E.vars.contains v = true
    · simp only [hv, ite_true]
      exact exprSim_of (EqE.refl _) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h) (fun _ h => by cases h)
    · simp only [hv, Bool.false_eq_true, ite_false]
      refine ⟨EqE.refl _, fun k hk => ?_, (prefOk_ne fun _ _ h => by cases h), ?_⟩
      · simp [identityConst?] at hk; subst hk; exact idEq_false
      · intro c hc; simp only [splitAnd, List.mem_singleton] at hc; subst hc
        exact prefOk_ne fun _ _ h => by cases h
  | .cmp op a b, hok, e', hd => by
    obtain ⟨ha, hb⟩ := hok
    simp only [resolveE] at hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    obtain ⟨b', hb', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a ha a' ha'
    obtain ⟨b'', hb'', sb⟩ := resolveX_sim b hb b' hb'
    simp only [resolveX]
    rw [ev_bind, ha'']; simp only []; rw [ev_bind, hb'']
    refine ⟨_, rfl, exprSim_of (EqE.cmp op sa.1 sb.1) (fun _ h => by cases h) ?_ (fun _ h => by cases h)⟩
    exact prefOk_of fun x y h => by cases h; exact ⟨sa.2.1, sb.2.1⟩
  | .sameTerm a b, hok, e', hd => by
    obtain ⟨ha, hb⟩ := hok
    simp only [resolveE] at hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    obtain ⟨b', hb', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a ha a' ha'
    obtain ⟨b'', hb'', sb⟩ := resolveX_sim b hb b' hb'
    simp only [resolveX]
    rw [ev_bind, ha'']; simp only []; rw [ev_bind, hb'']
    exact ⟨_, rfl, exprSim_of (EqE.sameTerm sa.1 sb.1) (fun _ h => by cases h)
      (prefOk_ne fun _ _ h => by cases h) (fun _ h => by cases h)⟩
  | .arith op a b, hok, e', hd => by
    obtain ⟨ha, hb⟩ := hok
    simp only [resolveE] at hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    obtain ⟨b', hb', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a ha a' ha'
    obtain ⟨b'', hb'', sb⟩ := resolveX_sim b hb b' hb'
    simp only [resolveX]
    rw [ev_bind, ha'']; simp only []; rw [ev_bind, hb'']
    exact ⟨_, rfl, exprSim_of (EqE.arith op sa.1 sb.1) (fun _ h => by cases h)
      (prefOk_ne fun _ _ h => by cases h) (fun _ h => by cases h)⟩
  | .and xs, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨xs', hxs', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨xs'', hxs'', hf, hpx⟩ := resolveEsX_sim xs hok xs' hxs'
    simp only [resolveX]
    rw [ev_bind, hxs'']
    refine ⟨_, rfl, EqE.and hf, (constOk_of fun _ h => by cases h), (prefOk_ne fun _ _ h => by cases h), ?_⟩
    simpa [splitAnd] using hpx
  | .or xs, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨xs', hxs', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨xs'', hxs'', hf, _⟩ := resolveEsX_sim xs hok xs' hxs'
    simp only [resolveX]
    rw [ev_bind, hxs'']
    exact ⟨_, rfl, exprSim_of (EqE.or hf) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩
  | .coalesce xs, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨xs', hxs', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨xs'', hxs'', hf, _⟩ := resolveEsX_sim xs hok xs' hxs'
    simp only [resolveX]
    rw [ev_bind, hxs'']
    exact ⟨_, rfl, exprSim_of (EqE.coalesce hf) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩
  | .not a, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a hok a' ha'
    simp only [resolveX]
    rw [ev_bind, ha'']
    exact ⟨_, rfl, exprSim_of (EqE.not sa.1) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩
  | .neg a, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a hok a' ha'
    simp only [resolveX]
    rw [ev_bind, ha'']
    exact ⟨_, rfl, exprSim_of (EqE.neg sa.1) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩
  | .inList a xs n, hok, e', hd => by
    obtain ⟨ha, hxs⟩ := hok
    simp only [resolveE] at hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    obtain ⟨xs', hxs', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a ha a' ha'
    obtain ⟨xs'', hxs'', hf, _⟩ := resolveEsX_sim xs hxs xs' hxs'
    simp only [resolveX]
    rw [ev_bind, ha'']; simp only []; rw [ev_bind, hxs'']
    exact ⟨_, rfl, exprSim_of (EqE.inList n sa.1 hf) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩
  | .ite c a b, hok, e', hd => by
    obtain ⟨hc, ha, hb⟩ := hok
    simp only [resolveE] at hd
    obtain ⟨c', hc', hd⟩ := bind_ok hd
    obtain ⟨a', ha', hd⟩ := bind_ok hd
    obtain ⟨b', hb', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨c'', hc'', sc⟩ := resolveX_sim c hc c' hc'
    obtain ⟨a'', ha'', sa⟩ := resolveX_sim a ha a' ha'
    obtain ⟨b'', hb'', sb⟩ := resolveX_sim b hb b' hb'
    simp only [resolveX]
    rw [ev_bind, hc'']; simp only []; rw [ev_bind, ha'']; simp only []; rw [ev_bind, hb'']
    exact ⟨_, rfl, exprSim_of (EqE.ite sc.1 sa.1 sb.1) (fun _ h => by cases h)
      (prefOk_ne fun _ _ h => by cases h) (fun _ h => by cases h)⟩
  | .func f args, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨u, hc, hd⟩ := bind_ok hd
    split at hd
    · cases hd
    · next hreg =>
      obtain ⟨xs', hxs', hd⟩ := bind_ok hd
      cases hd
      obtain ⟨xs'', hxs'', hf, _⟩ := resolveEsX_sim args hok xs' hxs'
      simp only [resolveX]
      rw [hc, ev_bind_ok st (ev_liftEx_ok st u)]
      rw [if_neg hreg, ev_bind, hxs'']
      exact ⟨_, rfl, exprSim_of (EqE.func f hf) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
        (fun _ h => by cases h)⟩
  | .exists q n, hok, e', hd => by
    simp only [resolveE] at hd
    obtain ⟨bq, hbq, hd⟩ := bind_ok hd
    cases hd
    obtain ⟨bq', hbq', hqp⟩ := eval_sim q hok bq hbq
    simp only [resolveX]
    rw [ev_bind, hbq']
    exact ⟨_, rfl, exprSim_of (EqE.exists n hqp) (fun _ h => by cases h) (prefOk_ne fun _ _ h => by cases h)
      (fun _ h => by cases h)⟩

theorem resolveEsX_sim : ∀ (es : List Expr), ExprsOk E.iso E.vars es → ∀ es', resolveEs (E.at st) pb es = .ok es' →
    ∃ es'', ev st (resolveEsX E pathE es) = .ok (.ok es'') ∧ List.Forall₂ EqE es'' es' ∧ ∀ c ∈ es'', PrefOk c
  | [], _, es', hd => by
    simp only [resolveEs] at hd; cases hd
    exact ⟨[], rfl, List.Forall₂.nil, fun _ h => by cases h⟩
  | x :: xs, hok, es', hd => by
    obtain ⟨hx, hxs⟩ := hok
    simp only [resolveEs] at hd
    obtain ⟨x', hx', hd⟩ := bind_ok hd
    obtain ⟨xs', hxs', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨x'', hx'', sx⟩ := resolveX_sim x hx x' hx'
    obtain ⟨xs'', hxs'', hf, hpx⟩ := resolveEsX_sim xs hxs xs' hxs'
    simp only [resolveEsX]
    rw [ev_bind, hx'']; simp only []; rw [ev_bind, hxs'']
    refine ⟨_, rfl, List.Forall₂.cons sx.1 hf, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact sx.2.2.1
    · exact hpx c hc

theorem resolveOptX_sim : ∀ (c : Option Expr), OptOk E.iso E.vars c → ∀ c', resolveOpt (E.at st) pb c = .ok c' →
    ∃ c'', ev st (resolveOptX E pathE c) = .ok (.ok c'') ∧ OptEqE c'' c'
  | none, _, c', hd => by
    simp only [resolveOpt] at hd; cases hd
    exact ⟨none, rfl, trivial⟩
  | some e, hok, c', hd => by
    simp only [resolveOpt] at hd
    obtain ⟨e', he', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨e'', he'', se⟩ := resolveX_sim e hok e' he'
    simp only [resolveOptX]
    rw [ev_bind, he'']
    exact ⟨some e'', rfl, se.1⟩

theorem resolveAggsX_sim : ∀ (as : List (Var × AggFunc × Option Expr × Bool)), AggsOk E.iso E.vars as →
    ∀ as', resolveAggs (E.at st) pb as = .ok as' →
    ∃ as'', ev st (resolveAggsX E pathE as) = .ok (.ok as'') ∧ List.Forall₂ AggEq as'' as'
  | [], _, as', hd => by
    simp only [resolveAggs] at hd; cases hd
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | (v, f, none, d) :: rest, hok, as', hd => by
      obtain ⟨_, hrest⟩ := hok
      simp only [resolveAggs, pure_bind] at hd
      obtain ⟨rest', hrest', hd⟩ := bind_ok hd
      cases hd
      obtain ⟨rest'', hrest'', hf⟩ := resolveAggsX_sim rest hrest rest' hrest'
      simp only [resolveAggsX, pure_bind]
      rw [ev_bind, hrest'']
      exact ⟨_, rfl, List.Forall₂.cons ⟨rfl, rfl, rfl, trivial⟩ hf⟩
  | (v, f, some e, d) :: rest, hok, as', hd => by
      obtain ⟨ha, hrest⟩ := hok
      simp only [resolveAggs, bind_assoc, pure_bind] at hd
      obtain ⟨e', he', hd⟩ := bind_ok hd
      obtain ⟨rest', hrest', hd⟩ := bind_ok hd
      cases hd
      obtain ⟨e'', he'', se⟩ := resolveX_sim e ha e' he'
      obtain ⟨rest'', hrest'', hf⟩ := resolveAggsX_sim rest hrest rest' hrest'
      simp only [resolveAggsX, bind_assoc, pure_bind]
      rw [ev_bind, he'']
      simp only []
      rw [ev_bind, hrest'']
      exact ⟨_, rfl, List.Forall₂.cons ⟨rfl, rfl, rfl, se.1⟩ hf⟩

theorem resolveKeysX_sim : ∀ (ks : List (Expr × Bool)), KeysOk E.iso E.vars ks →
    ∀ ks', resolveKeys (E.at st) pb ks = .ok ks' →
    ∃ ks'', ev st (resolveKeysX E pathE ks) = .ok (.ok ks'') ∧ List.Forall₂ KeyEq ks'' ks'
  | [], _, ks', hd => by
    simp only [resolveKeys] at hd; cases hd
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | (e, d) :: rest, hok, ks', hd => by
    obtain ⟨he, hrest⟩ := hok
    simp only [resolveKeys] at hd
    obtain ⟨e', he', hd⟩ := bind_ok hd
    obtain ⟨rest', hrest', hd⟩ := bind_ok hd
    cases hd
    obtain ⟨e'', he'', se⟩ := resolveX_sim e he e' he'
    obtain ⟨rest'', hrest'', hf⟩ := resolveKeysX_sim rest hrest rest' hrest'
    simp only [resolveKeysX]
    rw [ev_bind, he'']; simp only []; rw [ev_bind, hrest'']
    exact ⟨_, rfl, List.Forall₂.cons ⟨se.1, rfl⟩ hf⟩

end

end

end Tiramemsu.Exec
