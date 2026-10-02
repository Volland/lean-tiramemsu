/-
The join laws lifted to the reference semantics: `Join` is invariant under permutation of its
inputs, associative and has `Join[]` as unit, as bags (query-semantics "Machine-checked join
algebra"). Two results are related when both succeed with permuted bags, or both fail.
-/
import TiramemsuProofs.Query.JoinLaws
import Tiramemsu.Sem.Denote

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[verification#Proven Query Semantics]]

/-- Both succeed with permuted bags, or both fail. -/
def ERel (r s : Except QError Bag) : Prop :=
  (∃ a b, r = .ok a ∧ s = .ok b ∧ a.Perm b) ∨ (∃ e e', r = .error e ∧ s = .error e')

/-! ## `mapM` -/

theorem mapM_ok_of {α β ε : Type} (f : α → Except ε β) (g : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (g x)) → xs.mapM f = .ok (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, h x (List.mem_cons_self ..), mapM_ok_of f g xs fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem mapM_error_of {α β ε : Type} (f : α → Except ε β) :
    ∀ xs : List α, (∃ x ∈ xs, ∃ e, f x = .error e) → ∃ e, xs.mapM f = .error e
  | [], ⟨_, hx, _⟩ => by cases hx
  | x :: xs, ⟨y, hy, e, he⟩ => by
    rw [List.mapM_cons]
    cases hx : f x with
    | error e' => exact ⟨e', rfl⟩
    | ok b =>
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hx] at he; cases he
      · obtain ⟨e2, h2⟩ := mapM_error_of f xs ⟨y, hy, e, he⟩
        exact ⟨e2, by simp only [bind, Except.bind, h2]⟩

/-- The value of a successful result (`[]` otherwise). -/
def okOr (r : Except QError Bag) : Bag := match r with
  | .ok b => b
  | .error _ => []

theorem denoteList_eq (E : Env) (pb : PathSem) :
    ∀ xs : List Op, denoteList E pb xs = xs.mapM (denote E pb)
  | [] => by simp [denoteList]; rfl
  | x :: xs => by
    rw [denoteList, List.mapM_cons, denoteList_eq E pb xs]

theorem isoFilter_perm (iso : List (Nat × Nat)) {a b : Bag} (h : a.Perm b) : (isoFilter iso a).Perm (isoFilter iso b) := by
  unfold isoFilter; split
  · exact h
  · exact h.filter _

/-- Not a path pattern (path patterns are evaluated laterally, in input order). -/
def NoPath (x : Op) : Prop := Op.pathPat? x = none

theorem denoteInputs_eq (E : Env) (pb : PathSem) :
    ∀ xs : List Op, (∀ x ∈ xs, NoPath x) → denoteInputs E pb xs = (denoteList E pb xs).map (·.map some)
  | [], _ => rfl
  | x :: xs, h => by
    have hx : NoPath x := h x (List.mem_cons_self ..)
    have ih := denoteInputs_eq E pb xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases x with
    | path p => exact absurd hx (by simp [NoPath, Op.pathPat?])

    | _ =>
      simp only [denoteInputs, denoteList, ih]
      cases denote E pb _ <;> cases denoteList E pb xs <;> rfl

theorem others_eq (E : Env) : ∀ (xs : List Op) (bs : List Bag),
    ((xs.zip (bs.map some)).filterMap fun (x, b) => b.map (E.schemaOf x, ·)) = (xs.map E.schemaOf).zip bs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, b :: bs => by simp [others_eq E xs bs]

theorem pathPats_nil : ∀ xs : List Op, (∀ x ∈ xs, NoPath x) → xs.filterMap Op.pathPat? = []
  | [], _ => rfl
  | x :: xs, h => by
    have hx : Op.pathPat? x = none := h x (List.mem_cons_self ..)
    rw [List.filterMap_cons, hx, pathPats_nil xs fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The join of path-free inputs: the n-ary bag join of their bags. -/
theorem denote_join_eq (E : Env) (pb : PathSem) (xs : List Op) (h : ∀ x ∈ xs, NoPath x) :
    denote E pb (.join xs) = (denoteList E pb xs).map fun bs =>
      isoFilter E.iso (joinAll E.sem.missing E.n ((xs.map E.schemaOf).zip bs)).2 := by
  simp only [denote]
  rw [denoteInputs_eq E pb xs h, pathPats_nil xs h]
  cases denoteList E pb xs with
  | error e => rfl
  | ok bs => simp [Except.map, bind, Except.bind, others_eq, lateralPaths, liftL, pure, Except.pure]

/-- query-semantics: `Join` is invariant under permutation of its inputs (path-free inputs; path
patterns are evaluated laterally in input order). -/
theorem denote_join_perm (E : Env) (pb : PathSem) {xs ys : List Op}
    (h : xs.Perm ys) (hnp : ∀ x ∈ xs, NoPath x) : ERel (denote E pb (.join xs)) (denote E pb (.join ys)) := by
  have hnp' : ∀ y ∈ ys, NoPath y := fun y hy => hnp y (h.mem_iff.2 hy)
  rw [denote_join_eq E pb xs hnp, denote_join_eq E pb ys hnp', denoteList_eq, denoteList_eq]
  by_cases hall : ∀ x ∈ xs, ∃ b, denote E pb x = .ok b
  · have hx : ∀ x ∈ xs, denote E pb x = .ok (okOr (denote E pb x)) := fun x hx => by
      obtain ⟨b, hb⟩ := hall x hx; rw [hb]; rfl
    have hy : ∀ x ∈ ys, denote E pb x = .ok (okOr (denote E pb x)) := fun x hx' => hx x (h.mem_iff.2 hx')
    rw [mapM_ok_of _ _ xs hx, mapM_ok_of _ _ ys hy]
    refine Or.inl ⟨_, _, rfl, rfl, isoFilter_perm _ ?_⟩
    rw [List.zip_map', List.zip_map']
    exact (joinAll_perm _ _ (h.map _)).2
  · push Not at hall
    obtain ⟨x, hx, hne⟩ := hall
    have herr : ∃ e, denote E pb x = .error e := by
      cases hd : denote E pb x with
      | ok b => exact absurd hd (hne b)
      | error e => exact ⟨e, rfl⟩
    obtain ⟨e, he⟩ := herr
    obtain ⟨e1, h1⟩ := mapM_error_of (denote E pb) xs ⟨x, hx, e, he⟩
    obtain ⟨e2, h2⟩ := mapM_error_of (denote E pb) ys ⟨x, h.mem_iff.1 hx, e, he⟩
    rw [h1, h2]
    exact Or.inr ⟨e1, e2, rfl, rfl⟩

/-! ## Scopes of joins -/

theorem beq_eq_decide' (v w : Var) : (v == w) = decide (v = w) := by
  by_cases h : v = w <;> simp [h]

theorem push_binds (s : Scope) (v w : Var) : (s.push v).binds w = (s.binds w || v == w) := by
  unfold Scope.push Scope.binds
  rw [beq_eq_decide']
  by_cases h : v ∈ s.vars
  · have hc : s.vars.contains v = true := by simpa using h
    simp only [hc, if_true]
    by_cases hw : v = w
    · subst hw; simp [h]
    · simp [hw]
  · have hc : s.vars.contains v = false := by simpa using h
    simp only [hc, Bool.false_eq_true, if_false, List.contains_append]
    by_cases hw : v = w
    · subst hw; simp
    · simp [hw, Ne.symm hw]

theorem miss_vars (s : Scope) (v : Var) : (s.miss v).vars = s.vars := by
  unfold Scope.miss; split <;> rfl

theorem foldl_push_binds (vs : List Var) : ∀ (s : Scope) (w : Var),
    (vs.foldl Scope.push s).binds w = (s.binds w || vs.contains w) := by
  induction vs with
  | nil => intro s w; simp
  | cons v vs ih =>
    intro s w
    rw [List.foldl_cons, ih, push_binds, beq_eq_decide', List.contains_cons, beq_eq_decide' w v]
    by_cases h : v = w
    · subst h; simp
    · simp [h, Ne.symm h]

theorem foldl_miss_vars (f : Scope → Var → Scope) (hf : ∀ s v, (f s v).vars = s.vars) :
    ∀ (vs : List Var) (s : Scope), (vs.foldl f s).vars = s.vars := by
  intro vs; induction vs with
  | nil => intro s; rfl
  | cons v vs ih => intro s; simp [ih, hf]

theorem foldl_scopes_binds (w : Var) : ∀ (ss : List Scope) (acc : Scope),
    (ss.foldl (fun acc sc => sc.vars.foldl Scope.push acc) acc).binds w =
      (acc.binds w || ss.any (·.binds w))
  | [], acc => by simp
  | s :: ss, acc => by
    rw [List.foldl_cons, foldl_scopes_binds w ss, foldl_push_binds, List.any_cons, Bool.or_assoc]
    rfl

theorem joinScopes_binds (ss : List Scope) (w : Var) :
    (joinScopes ss).binds w = ss.any (·.binds w) := by
  unfold joinScopes
  have hv := foldl_miss_vars
    (fun acc v => if (ss.filter (·.binds v)).all (·.maybeMissing.contains v) then acc.miss v else acc)
    (fun s v => by split <;> simp [miss_vars])
  show List.contains _ w = _
  rw [hv]
  have := foldl_scopes_binds w ss {}
  simpa [Scope.binds] using this

theorem scopeList_eq : ∀ xs : List Op, scopeList xs = xs.map scope
  | [] => rfl
  | x :: xs => by simp [scopeList, scopeList_eq xs]

theorem schemaOf_join (E : Env) (xs : List Op) :
    E.schemaOf (.join xs) = E.vars.map fun v => xs.any fun x => (scope x).binds v := by
  simp only [Env.schemaOf, scope, scopeList_eq]
  congr 1; funext v
  rw [joinScopes_binds, List.any_map]; rfl

theorem union_map {α : Type} (vs : List α) (f g : α → Bool) :
    Schema.union (vs.map f) (vs.map g) = vs.map fun v => f v || g v := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Schema.union, ih]

/-! ## Associativity and unit -/

theorem isoFilter_nil (a : Bag) : isoFilter [] a = a := by simp [isoFilter]

theorem joinAll_two (m : Missing) (n : Nat) (x y : SBag) :
    SRel (joinAll m n [x, y]) (joinSB m x y) := by
  unfold joinAll
  simp only [List.foldl_cons, List.foldl_nil]
  exact joinSB_congr m y (joinSB_unit_left m n x)

/-- query-semantics: `Join` is associative (for queries without match groups). -/
theorem nopath_join (xs : List Op) : NoPath (.join xs) := rfl

theorem denote_join_assoc (E : Env) (pb : PathSem) (hiso : E.iso = [])
    (a b c : Op) (ha : NoPath a) (hb : NoPath b) (hc : NoPath c) :
    ERel (denote E pb (.join [a, .join [b, c]])) (denote E pb (.join [.join [a, b], c])) := by
  have l3 (x y : Op) (hx : NoPath x) (hy : NoPath y) : ∀ z ∈ [x, y], NoPath z := by
    intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  rw [denote_join_eq E pb _ (l3 _ _ ha (nopath_join _)), denote_join_eq E pb _ (l3 _ _ (nopath_join _) hc)]
  simp only [denoteList, denote_join_eq E pb _ (l3 _ _ hb hc), denote_join_eq E pb _ (l3 _ _ ha hb), hiso,
    isoFilter_nil]
  cases ha : denote E pb a with
  | error e => cases hb : denote E pb b <;> cases hc : denote E pb c <;> simp [bind, Except.bind, pure, Except.pure, Except.map] <;>
      exact Or.inr ⟨_, _, rfl, rfl⟩
  | ok A =>
    cases hb : denote E pb b with
    | error e => cases hc : denote E pb c <;> simp [bind, Except.bind, pure, Except.pure, Except.map] <;>
        exact Or.inr ⟨_, _, rfl, rfl⟩
    | ok B =>
      cases hc : denote E pb c with
      | error e => simp [bind, Except.bind, pure, Except.pure, Except.map]; exact Or.inr ⟨_, _, rfl, rfl⟩
      | ok C =>
        simp only [bind, Except.bind, pure, Except.pure, Except.map, List.map_cons, List.map_nil, List.zip_cons_cons,
          List.zip_nil_left]
        refine Or.inl ⟨_, _, rfl, rfl, ?_⟩
        rw [schemaOf_join, schemaOf_join]
        simp only [List.any_cons, List.any_nil, Bool.or_false]
        have hbc : (E.vars.map fun v => (scope b).binds v || (scope c).binds v) =
            Schema.union (E.schemaOf b) (E.schemaOf c) := (union_map _ _ _).symm
        have hab : (E.vars.map fun v => (scope a).binds v || (scope b).binds v) =
            Schema.union (E.schemaOf a) (E.schemaOf b) := (union_map _ _ _).symm
        rw [hbc, hab]
        have l1 := joinAll_two E.sem.missing E.n (E.schemaOf a, A)
          (Schema.union (E.schemaOf b) (E.schemaOf c), (joinAll E.sem.missing E.n [(E.schemaOf b, B), (E.schemaOf c, C)]).2)
        have l2 := joinAll_two E.sem.missing E.n
          (Schema.union (E.schemaOf a) (E.schemaOf b), (joinAll E.sem.missing E.n [(E.schemaOf a, A), (E.schemaOf b, B)]).2)
          (E.schemaOf c, C)
        have i1 := joinAll_two E.sem.missing E.n (E.schemaOf b, B) (E.schemaOf c, C)
        have i2 := joinAll_two E.sem.missing E.n (E.schemaOf a, A) (E.schemaOf b, B)
        have c1 : SRel (Schema.union (E.schemaOf b) (E.schemaOf c), (joinAll E.sem.missing E.n [(E.schemaOf b, B), (E.schemaOf c, C)]).2)
            (joinSB E.sem.missing (E.schemaOf b, B) (E.schemaOf c, C)) := ⟨rfl, i1.2⟩
        have c2 : SRel (Schema.union (E.schemaOf a) (E.schemaOf b), (joinAll E.sem.missing E.n [(E.schemaOf a, A), (E.schemaOf b, B)]).2)
            (joinSB E.sem.missing (E.schemaOf a, A) (E.schemaOf b, B)) := ⟨rfl, i2.2⟩
        exact (l1.trans (joinSB_congr_right _ _ c1)).2.trans
          (((joinSB_assoc _ _ _ _).symm.trans (joinSB_congr _ _ c2.symm)).trans l2.symm).2

theorem compat_unit_falses (m : Missing) (P Q : Schema) (a : Row) (hQ : ∀ i, bit Q i = false) :
    compat m P Q a [] = true := by
  rw [compat_iff]; intro i
  rw [hQ i]
  have : cell [] i = none := by simp [cell]
  rw [this]; cases cell a i <;> cases m <;> simp [cellCompat]

/-- query-semantics: `Join[]` is a unit. -/
theorem denote_join_unit (E : Env) (pb : PathSem) (hiso : E.iso = []) (a : Op) (ha : NoPath a) :
    ERel (denote E pb (.join [a, .join []])) (denote E pb a) := by
  have l2 : ∀ z ∈ [a, .join []], NoPath z := by
    intro z hz; simp at hz; rcases hz with rfl | rfl
    · exact ha
    · exact nopath_join _
  rw [denote_join_eq E pb _ l2]
  simp only [denoteList, denote_join_eq E pb [] (by simp), hiso, isoFilter_nil]
  cases ha : denote E pb a with
  | error e => simp [bind, Except.bind, Except.map]; exact Or.inr ⟨_, _, rfl, rfl⟩
  | ok A =>
    simp only [bind, Except.bind, pure, Except.pure, Except.map, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_left]
    refine Or.inl ⟨_, _, rfl, rfl, ?_⟩
    have l := joinAll_two E.sem.missing E.n (E.schemaOf a, A) (E.schemaOf (.join []), (joinAll E.sem.missing E.n []).2)
    have hz : ∀ i, bit (E.schemaOf (.join [])) i = false := by
      intro i; rw [schemaOf_join]; simp only [bit, List.any_nil, List.getD_eq_getElem?_getD]
      rw [List.getElem?_map]; cases (E.vars[i]?) <;> rfl
    have : (joinSB E.sem.missing (E.schemaOf a, A) (E.schemaOf (.join []), (joinAll E.sem.missing E.n []).2)).2 = A := by
      simp only [joinSB, joinAll, List.foldl_nil, unitSB, joinB_eq, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      conv => rhs; rw [← List.flatMap_singleton' A]
      refine flatMap_congr fun r _ => ?_
      simp [jcell, compat_unit_falses _ _ _ r hz]
    exact l.2.trans (List.Perm.of_eq this)

end Tiramemsu.Sem
