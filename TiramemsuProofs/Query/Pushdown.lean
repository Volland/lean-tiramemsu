/-
Filter push-down and sideways binding passing (nested-loop-join "Filter push-down and binding
passing"): an `EXISTS`-free conjunct reads only the cells of its variables, so once every row
binds them the conjunct commutes with every later join step; the index nested loop that applies
each conjunct as soon as its variables are bound returns the filtered reference join. A
`LeftJoin` whose right side is a join of stored patterns, evaluated by passing each left row into
the right side's nested loop, is the reference left join. All statements assume `IdBridge`.
-/
import TiramemsuProofs.Query.Inlj

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Expressions read only their variables -/

/-- Two rows agree on a list of positions. -/
def AgreeOn (is : List Nat) (r r' : Row) : Prop := ∀ i ∈ is, r.get i = r'.get i

mutual

theorem eval_congr : ∀ (e : RExpr) {r r' : Row}, (rvarsOf e).2 = false → AgreeOn (rvarsOf e).1 r r' →
    e.eval r = e.eval r'
  | .var i, r, r', _, h => by simp only [RExpr.eval]; exact h i (by simp [rvarsOf])
  | .bound i, r, r', _, h => by simp only [RExpr.eval]; rw [h i (by simp [rvarsOf])]
  | .const _, _, _, _, _ => rfl
  | .err, _, _, _, _ => rfl
  | .exists _ _, _, _, hx, _ => by simp [rvarsOf] at hx
  | .cmp op a b, r, r', hx, h => by
    simp only [rvarsOf, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.eval]
    rw [eval_congr a hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      eval_congr b hx.2 (fun i hi => h i (List.mem_append_right _ hi))]
  | .sameTerm a b, r, r', hx, h => by
    simp only [rvarsOf, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.eval]
    rw [eval_congr a hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      eval_congr b hx.2 (fun i hi => h i (List.mem_append_right _ hi))]
  | .arith op a b, r, r', hx, h => by
    simp only [rvarsOf, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.eval]
    rw [eval_congr a hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      eval_congr b hx.2 (fun i hi => h i (List.mem_append_right _ hi))]
  | .not a, r, r', hx, h => by
    simp only [rvarsOf] at hx h
    simp only [RExpr.eval]; rw [eval_congr a hx h]
  | .neg a, r, r', hx, h => by
    simp only [rvarsOf] at hx h
    simp only [RExpr.eval]; rw [eval_congr a hx h]
  | .and xs, r, r', hx, h => by
    simp only [rvarsOf] at hx h
    simp only [RExpr.eval]; rw [tris_congr xs hx h]
  | .or xs, r, r', hx, h => by
    simp only [rvarsOf] at hx h
    simp only [RExpr.eval]; rw [tris_congr xs hx h]
  | .coalesce xs, r, r', hx, h => by
    simp only [rvarsOf] at hx h
    simp only [RExpr.eval]; exact firstOk_congr xs hx h
  | .func f xs, r, r', hx, h => by
    simp only [rvarsOf] at hx h
    simp only [RExpr.eval]; rw [evalAll_congr xs hx h]
  | .inList a xs n, r, r', hx, h => by
    simp only [rvarsOf, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.eval]
    rw [eval_congr a hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      eqTris_congr xs (a.eval r') hx.2 (fun i hi => h i (List.mem_append_right _ hi))]
  | .ite c a b, r, r', hx, h => by
    simp only [rvarsOf, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.eval]
    rw [eval_congr c hx.1.1 (fun i hi => h i (List.mem_append_left _ (List.mem_append_left _ hi))),
      eval_congr a hx.1.2 (fun i hi => h i (List.mem_append_left _ (List.mem_append_right _ hi))),
      eval_congr b hx.2 (fun i hi => h i (List.mem_append_right _ hi))]

theorem tris_congr : ∀ (xs : List RExpr) {r r' : Row}, (rvarsOfList xs).2 = false →
    AgreeOn (rvarsOfList xs).1 r r' → RExpr.tris r xs = RExpr.tris r' xs
  | [], _, _, _, _ => rfl
  | x :: xs, r, r', hx, h => by
    simp only [rvarsOfList, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.tris]
    rw [eval_congr x hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      tris_congr xs hx.2 (fun i hi => h i (List.mem_append_right _ hi))]

theorem eqTris_congr : ∀ (xs : List RExpr) (o : Option Value) {r r' : Row}, (rvarsOfList xs).2 = false →
    AgreeOn (rvarsOfList xs).1 r r' → RExpr.eqTris r o xs = RExpr.eqTris r' o xs
  | [], _, _, _, _, _ => rfl
  | x :: xs, o, r, r', hx, h => by
    simp only [rvarsOfList, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.eqTris]
    rw [eval_congr x hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      eqTris_congr xs o hx.2 (fun i hi => h i (List.mem_append_right _ hi))]

theorem firstOk_congr : ∀ (xs : List RExpr) {r r' : Row}, (rvarsOfList xs).2 = false →
    AgreeOn (rvarsOfList xs).1 r r' → RExpr.firstOk r xs = RExpr.firstOk r' xs
  | [], _, _, _, _ => rfl
  | x :: xs, r, r', hx, h => by
    simp only [rvarsOfList, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.firstOk]
    rw [eval_congr x hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      firstOk_congr xs hx.2 (fun i hi => h i (List.mem_append_right _ hi))]

theorem evalAll_congr : ∀ (xs : List RExpr) {r r' : Row}, (rvarsOfList xs).2 = false →
    AgreeOn (rvarsOfList xs).1 r r' → RExpr.evalAll r xs = RExpr.evalAll r' xs
  | [], _, _, _, _ => rfl
  | x :: xs, r, r', hx, h => by
    simp only [rvarsOfList, Bool.or_eq_false_iff] at hx h
    simp only [RExpr.evalAll]
    rw [eval_congr x hx.1 (fun i hi => h i (List.mem_append_left _ hi)),
      evalAll_congr xs hx.2 (fun i hi => h i (List.mem_append_right _ hi))]

end

/-! ## Conjuncts on rows that bind their variables -/

/-- A pushed conjunct built from its condition (`Pushed.ofR`): its positions are those the
condition reads, and it is early only without `EXISTS`. -/
def PushedOk (c : Pushed) : Prop := c.vars = (rvarsOf c.cond).1 ∧ (c.early = true → (rvarsOf c.cond).2 = false)

theorem pushedOk_ofR (c : RExpr) : PushedOk (Pushed.ofR c) := by
  unfold Pushed.ofR PushedOk; simp

/-- Every conjunct of a list holds. -/
def allHold (cs : List Pushed) (r : Row) : Bool := cs.all fun c => c.cond.holds r

theorem foldl_filterB (cs : List Pushed) : ∀ rows : Bag,
    cs.foldl (fun r c => filterB c.cond r) rows = rows.filter (allHold cs) := by
  induction cs with
  | nil => intro rows; unfold allHold; simp
  | cons c cs ih =>
    intro rows
    rw [List.foldl_cons, ih]
    unfold filterB allHold
    rw [List.filter_filter]
    congr 1; funext r; rw [List.all_cons, Bool.and_comm]

theorem allHold_append (as bs : List Pushed) (r : Row) : allHold (as ++ bs) r = (allHold as r && allHold bs r) := by
  simp [allHold, List.all_append]

theorem allHold_perm {as bs : List Pushed} (h : as.Perm bs) (r : Row) : allHold as r = allHold bs r := by
  unfold allHold; rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H c hc => H c (h.symm.subset hc), fun H c hc => H c (h.subset hc)⟩

theorem get_merge (a b : Row) (i : Nat) : (merge a b).get i = (a.get i <|> b.get i) := by
  rw [get_eq_cell, get_eq_cell, get_eq_cell, merge_cell]

/-- A row binds the positions. -/
def Binds (is : List Nat) (r : Row) : Prop := ∀ i ∈ is, (r.get i).isSome

theorem binds_merge_left {is : List Nat} {a : Row} (h : Binds is a) (b : Row) : Binds is (merge a b) := by
  intro i hi; rw [get_merge]; have := h i hi; cases ha : a.get i <;> simp_all

theorem binds_merge_right {is : List Nat} {b : Row} (h : Binds is b) (a : Row) : Binds is (merge a b) := by
  intro i hi; rw [get_merge]; have := h i hi; cases ha : a.get i <;> simp_all

theorem agree_merge {is : List Nat} {a : Row} (h : Binds is a) (b : Row) : AgreeOn is (merge a b) a := by
  intro i hi; rw [get_merge]; have := h i hi; cases ha : a.get i <;> simp_all

/-- An early conjunct over bound positions holds on a merge as on the left row. -/
theorem holds_merge {c : Pushed} (hc : PushedOk c) (he : c.early = true) {a : Row} (hb : Binds c.vars a)
    (b : Row) : c.cond.holds (merge a b) = c.cond.holds a := by
  unfold RExpr.holds RExpr.tri
  rw [eval_congr c.cond (hc.2 he) (hc.1 ▸ agree_merge hb b)]

theorem allHold_merge {cs : List Pushed} {is : List Nat} (hc : ∀ c ∈ cs, PushedOk c ∧ c.early = true ∧ ∀ i ∈ c.vars, i ∈ is)
    {a : Row} (hb : Binds is a) (b : Row) : allHold cs (merge a b) = allHold cs a := by
  unfold allHold
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  have key : ∀ c ∈ cs, c.cond.holds (merge a b) = c.cond.holds a := fun c h =>
    holds_merge (hc c h).1 (hc c h).2.1 (fun i hi => hb i ((hc c h).2.2 i hi)) b
  exact ⟨fun H c h => (key c h) ▸ H c h, fun H c h => (key c h).symm ▸ H c h⟩

/-- A filter on the left rows commutes with a join when it only reads cells the left rows bind. -/
theorem filter_joinB {m : Missing} {P Q : Schema} {xs ys : Bag} {f : Row → Bool}
    (hf : ∀ a ∈ xs, ∀ b, f (merge a b) = f a) :
    (joinB m P Q xs ys).filter f = joinB m P Q (xs.filter f) ys := by
  unfold joinB
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.filter_append, ih (fun a' h => hf a' (List.mem_cons_of_mem _ h))]
    by_cases ha : f a = true
    · rw [List.filter_cons_of_pos ha, List.flatMap_cons]
      congr 1
      rw [List.filter_eq_self.2]
      intro r hr
      obtain ⟨b, _, hb⟩ := List.mem_filterMap.1 hr
      split at hb
      · cases hb; rw [hf a (List.mem_cons_self ..)]; exact ha
      · cases hb
    · rw [List.filter_cons_of_neg ha, List.filter_eq_nil_iff.2, List.nil_append]
      intro r hr
      obtain ⟨b, _, hb⟩ := List.mem_filterMap.1 hr
      split at hb
      · cases hb; rw [hf a (List.mem_cons_self ..)]; exact ha
      · cases hb

/-! ## Pattern rows bind the pattern's variables -/

theorem sRows_graph {st : ModelState} {E : Env} {v : Store.View} {t : TriplePattern} {r : TripleRow} {x : Row}
    (h : x ∈ sRows st E v t r) {gv : Var} (hg : t.graph = .var gv) : (x.get (E.idx gv)).isSome := by
  unfold sRows at h
  split at h
  · cases h
  · rw [hg] at h
    simp only [gRows, List.mem_filterMap] at h
    obtain ⟨_, _, hb⟩ := h
    rw [(bindVal_spec hb).2]; rfl

theorem posFact_var {E : Env} {tv : TermOrVar} {w : Value} {y : Int64} {x : Row} (h : PosFact E tv w y x) :
    Binds (tv.vars.map E.idx) x := by
  cases tv with
  | var v => intro i hi; simp [TermOrVar.vars] at hi; subst hi; simp only [PosFact] at h; rw [h]; rfl
  | _ => intro i hi; simp [TermOrVar.vars] at hi

theorem sRows_binds {st : ModelState} {E : Env} {v : Store.View} {t : TriplePattern} {r : TripleRow} {x : Row}
    (h : x ∈ sRows st E v t r) : Binds (t.vars.map E.idx) x := by
  obtain ⟨h1, h2, h3, h4⟩ := sRows_pos h
  intro i hi
  simp only [TriplePattern.vars, List.map_append, List.mem_append] at hi
  rcases hi with (((hi | hi) | hi) | hi) | hi
  · exact posFact_var h1 i hi
  · exact posFact_var h2 i hi
  · exact posFact_var h3 i hi
  · cases he : t.eid with
    | none => rw [he] at hi; simp at hi
    | some ev => rw [he] at hi; simp at hi; subst hi; rw [h4 ev he]; rfl
  · cases hg : t.graph with
    | var gv => rw [hg] at hi; simp [GraphSel.vars] at hi; subst hi; exact sRows_graph h hg
    | _ => rw [hg] at hi; simp [GraphSel.vars] at hi

theorem tpBag_binds {st : ModelState} {E : Env} {t : TriplePattern} {x : Row} (h : x ∈ tpBag st E t) :
    Binds (t.vars.map E.idx) x := by
  unfold tpBag at h
  simp only at h
  have h' : x ∈ (visibleRows st (resolveView st t.view)).flatMap (sRows st E (resolveView st t.view) t) := by
    split at h
    · exact List.mem_eraseDups.1 h
    · exact h
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.1 h'
  exact sRows_binds hr

/-! ## The nested loop with pushed conjuncts -/

/-- The reference fold of a pattern order from a schema-bag. -/
def patFold (st : ModelState) (E : Env) (order : List (Nat × TriplePattern)) (a : SBag) : SBag :=
  (order.map fun t => (E.schemaOf (.triple t.2), tpBag st E t.2)).foldl (joinSB E.sem.missing) a

/-- The positions an order binds. -/
def orderVars (E : Env) (order : List (Nat × TriplePattern)) : List Nat :=
  order.flatMap fun t => t.2.vars.map E.idx

theorem mem_joinB {m : Missing} {P Q : Schema} {xs ys : Bag} {r : Row} (h : r ∈ joinB m P Q xs ys) :
    ∃ a ∈ xs, ∃ b ∈ ys, r = merge a b := by
  obtain ⟨a, ha, hr⟩ := List.mem_flatMap.1 h
  obtain ⟨b, hb, he⟩ := List.mem_filterMap.1 hr
  split at he
  · cases he; exact ⟨a, ha, b, hb, rfl⟩
  · cases he

theorem patFold_binds (st : ModelState) (E : Env) : ∀ (order : List (Nat × TriplePattern)) (P : Schema) (rows : Bag)
    (bound : List Nat), (∀ r ∈ rows, Binds bound r) →
    ∀ r ∈ (patFold st E order (P, rows)).2, Binds (bound ++ orderVars E order) r
  | [], P, rows, bound, h => by simpa [patFold, orderVars] using h
  | (i, t) :: rest, P, rows, bound, h => by
    have := patFold_binds st E rest (Schema.union P (E.schemaOf (.triple t)))
      (joinB E.sem.missing P (E.schemaOf (.triple t)) rows (tpBag st E t)) (bound ++ t.vars.map E.idx) (by
        intro r hr
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_joinB hr
        intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · exact binds_merge_left (h a ha) b j hj
        · exact binds_merge_right (tpBag_binds hb) a j hj)
    intro r hr
    have h2 := this r hr
    intro j hj
    apply h2 j
    simp only [orderVars, List.flatMap_cons, List.mem_append] at hj ⊢
    rcases hj with hj | hj | hj
    · exact Or.inl (Or.inl hj)
    · exact Or.inl (Or.inr hj)
    · exact Or.inr hj

theorem patFold_filter (st : ModelState) (E : Env) {cs : List Pushed} {bound : List Nat}
    (hc : ∀ c ∈ cs, PushedOk c ∧ c.early = true ∧ ∀ i ∈ c.vars, i ∈ bound) :
    ∀ (order : List (Nat × TriplePattern)) (P : Schema) (rows : Bag), (∀ r ∈ rows, Binds bound r) →
    patFold st E order (P, rows.filter (allHold cs)) =
      ((patFold st E order (P, rows)).1, (patFold st E order (P, rows)).2.filter (allHold cs))
  | [], P, rows, _ => rfl
  | (i, t) :: rest, P, rows, h => by
    have step : joinB E.sem.missing P (E.schemaOf (.triple t)) (rows.filter (allHold cs)) (tpBag st E t) =
        (joinB E.sem.missing P (E.schemaOf (.triple t)) rows (tpBag st E t)).filter (allHold cs) :=
      (filter_joinB fun a ha b => allHold_merge hc (h a ha) b).symm
    show patFold st E rest (joinSB E.sem.missing (P, rows.filter (allHold cs)) _) = _
    simp only [joinSB]
    rw [step]
    exact patFold_filter st E hc rest _ _ (by
      intro r hr
      obtain ⟨a, ha, b, _, rfl⟩ := mem_joinB hr
      exact binds_merge_left (h a ha) b)

/-! ## Constant equalities as key prefixes -/

/-- A constant whose value equality is identity: the only value equal to it is itself. -/
def IdEq (k : Value) : Prop := ∀ w, valueEq w k = true → w = k

theorem cmpBytes_eq_symm : ∀ (a b : List UInt8), cmpBytes a b = .eq → cmpBytes b a = .eq
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpBytes] at h
  | _ :: _, [], h => by simp [cmpBytes] at h
  | x :: xs, y :: ys, h => by
    simp only [cmpBytes] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · have hxy : ¬ y < x := by assumption
        have hyx : ¬ x < y := by assumption
        rw [if_neg hxy, if_neg hyx]
        exact cmpBytes_eq_symm xs ys h

theorem valueEq_symm (a b : Value) : valueEq a b = valueEq b a := by
  unfold valueEq
  cases a <;> cases b <;> simp only [] <;>
    first
    | (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq];
       exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, cmpBytes_eq_symm _ _ h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, cmpBytes_eq_symm _ _ h2⟩⟩)
    | (rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact ⟨Eq.symm, Eq.symm⟩)

theorem identityConst_some {b : RExpr} {k : Value} (h : identityConst? b = some k) : b = .const k := by
  unfold identityConst? at h
  split at h
  · next k' => split at h <;> (cases h; try rfl)
  · cases h

theorem holds_cmp_eq {x y : RExpr} {r : Row} (h : (RExpr.cmp .eq x y).holds r = true) :
    ∃ u v, x.eval r = some u ∧ y.eval r = some v ∧ valueEq u v = true := by
  unfold RExpr.holds RExpr.tri at h
  simp only [RExpr.eval] at h
  cases hx : x.eval r with
  | none => rw [hx] at h; simp [bind, Option.bind, Tri.ofOpt] at h
  | some u =>
    cases hy : y.eval r with
    | none => rw [hx, hy] at h; simp [bind, Option.bind, Tri.ofOpt] at h
    | some v =>
      refine ⟨u, v, rfl, rfl, ?_⟩
      rw [hx, hy] at h
      cases he : valueEq u v
      · simp [bind, Option.bind, compareVals, he, ebv, Tri.ofOpt] at h
      · rfl

theorem holds_eq_var_const {i : Nat} {k : Value} {r : Row} (hr : (RExpr.cmp .eq (.var i) (.const k)).holds r = true) :
    ∃ w, r.get i = some w ∧ valueEq w k = true := by
  obtain ⟨u, v, h1, h2, h3⟩ := holds_cmp_eq hr
  simp only [RExpr.eval] at h1 h2; cases h2
  exact ⟨u, h1, h3⟩

theorem holds_eq_const_var {i : Nat} {k : Value} {r : Row} (hr : (RExpr.cmp .eq (.const k) (.var i)).holds r = true) :
    ∃ w, r.get i = some w ∧ valueEq w k = true := by
  obtain ⟨u, v, h1, h2, h3⟩ := holds_cmp_eq hr
  simp only [RExpr.eval] at h1 h2; cases h1
  exact ⟨v, h2, by rw [valueEq_symm]; exact h3⟩

/-- A pushed equality with a constant forces the cell to the constant. -/
theorem prefixEq_holds {c : RExpr} {i : Nat} {k : Value} (h : prefixEq? c = some (i, k)) (hk : IdEq k)
    {r : Row} (hr : c.holds r = true) : r.get i = some k := by
  unfold prefixEq? at h
  split at h
  · next i' b =>
    cases hb : identityConst? b with
    | none => rw [hb] at h; cases h
    | some k' =>
      rw [hb] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [identityConst_some hb] at hr
      obtain ⟨w, hw, he⟩ := holds_eq_var_const hr
      rw [hw, hk w he]
  · next a i' _ =>
    cases ha : identityConst? a with
    | none => rw [ha] at h; cases h
    | some k' =>
      rw [ha] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [identityConst_some ha] at hr
      obtain ⟨w, hw, he⟩ := holds_eq_const_var hr
      rw [hw, hk w he]
  · cases h

/-- One seeding step. -/
def seedStep (r : Row) (e : Nat × Value) : Row := if (r.get e.1).isNone then r.setAt e.1 (some e.2) else r

theorem setAt_length_ge (r : Row) (i : Nat) (x : Option Value) : r.length ≤ (r.setAt i x).length := by
  unfold Row.setAt; split <;> simp

theorem setAt_length_le (r : Row) (i : Nat) (x : Option Value) : (r.setAt i x).length ≤ max r.length (i + 1) := by
  unfold Row.setAt; split
  · simp
  · simp; omega

/-- What seeding does to a row: each cell is kept, or was unbound and becomes a seeded constant. -/
theorem seed_spec : ∀ (eqs : List (Nat × Value)) (a : Row),
    (a.length ≤ (eqs.foldl seedStep a).length) ∧
    (∀ L, a.length ≤ L → (∀ e ∈ eqs, e.1 < L) → (eqs.foldl seedStep a).length ≤ L) ∧
    ∀ j, (eqs.foldl seedStep a).get j = a.get j ∨
      (a.get j = none ∧ ∃ k, (j, k) ∈ eqs ∧ (eqs.foldl seedStep a).get j = some k)
  | [], a => ⟨le_refl _, fun _ h _ => h, fun _ => Or.inl rfl⟩
  | e :: es, a => by
    obtain ⟨h1, h2, h3⟩ := seed_spec es (seedStep a e)
    have l1 : a.length ≤ (seedStep a e).length := by
      unfold seedStep
      split
      · exact setAt_length_ge _ _ _
      · exact le_refl _
    refine ⟨l1.trans h1, fun L hL he => h2 L ?_ (fun e' h => he e' (List.mem_cons_of_mem _ h)), fun j => ?_⟩
    · unfold seedStep; split
      · exact (setAt_length_le _ _ _).trans (max_le hL (he e (List.mem_cons_self ..)))
      · exact hL
    · simp only [List.foldl_cons]
      have hs : (seedStep a e).get j = a.get j ∨ (a.get j = none ∧ j = e.1 ∧ (seedStep a e).get j = some e.2) := by
        unfold seedStep
        split
        · next hn =>
          by_cases hj : j = e.1
          · subst hj; right; exact ⟨by simpa using hn, rfl, get_setAt_self _ _ _⟩
          · left; exact get_setAt_ne _ _ hj
        · left; rfl
      rcases h3 j with h | ⟨hn, k, hk, hv⟩
      · rcases hs with hs | ⟨hn', hje, hv'⟩
        · left; rw [h, hs]
        · right; refine ⟨hn', e.2, ?_, by rw [h, hv']⟩
          rw [hje]; exact List.mem_cons_self ..
      · rcases hs with hs | ⟨hn', hje, hv'⟩
        · right; rw [hs] at hn; exact ⟨hn, k, List.mem_cons_of_mem _ hk, hv⟩
        · rw [hv'] at hn; cases hn

theorem cellCompat_none_left (m : Missing) (q : Bool) (w : Value) : cellCompat m false q none (some w) = true := by
  cases m <;> simp [cellCompat]

/-- Seeding an outer row with pushed constant equalities changes no row the equalities keep. -/
theorem seed_joinB {m : Missing} {P Q : Schema} {J : Bag} {eqs : List (Nat × Value)} {g : Row → Bool}
    (hP : ∀ e ∈ eqs, bit P e.1 = false) (hJ : ∀ b ∈ J, ∀ e ∈ eqs, (b.get e.1).isSome)
    (hc : ∀ e ∈ eqs, ∀ r, g r = true → r.get e.1 = some e.2) (a : Row) :
    (joinB m P Q [eqs.foldl seedStep a] J).filter g = (joinB m P Q [a] J).filter g ∧
      ∀ x ∈ joinB m P Q [eqs.foldl seedStep a] J, x ∈ joinB m P Q [a] J := by
  obtain ⟨hl1, hl2, hsp⟩ := seed_spec eqs a
  set a' := eqs.foldl seedStep a
  -- the facts per right row
  have per : ∀ b ∈ J, (compat m P Q a' b = true → compat m P Q a b = true ∧ merge a' b = merge a b) ∧
      (compat m P Q a b = true → g (merge a b) = true → compat m P Q a' b = true) := by
    intro b hb
    have hbe := hJ b hb
    have hlen : a'.length ≤ max a.length b.length := hl2 _ (le_max_left _ _) (fun e he => by
      have := hbe e he
      rw [Row.get] at this
      cases h : b[e.1]? with
      | none => rw [h] at this; cases this
      | some _ => exact lt_of_lt_of_le (List.getElem?_eq_some_iff.1 h).1 (le_max_right _ _))
    by_cases hseed : ∀ j k, a.get j = none → (j, k) ∈ eqs → a'.get j = some k → b.get j = some k
    · have hcell : ∀ j, cell (merge a' b) j = cell (merge a b) j := by
        intro j
        rw [merge_cell, merge_cell, ← get_eq_cell, ← get_eq_cell, ← get_eq_cell]
        rcases hsp j with h | ⟨hn, k, hk, hv⟩
        · rw [h]
        · rw [hv, hn, hseed j k hn hk hv]; rfl
      have hmerge : merge a' b = merge a b := by
        apply getD_ext
        · simp only [merge_length]; omega
        · exact hcell
      have hcompat : compat m P Q a' b = compat m P Q a b := by
        rw [Bool.eq_iff_iff, compat_iff, compat_iff]
        refine forall_congr' fun j => ?_
        rcases hsp j with h | ⟨hn, k, hk, hv⟩
        · rw [← get_eq_cell a', h, get_eq_cell]
        · have hbj := hseed j k hn hk hv
          rw [← get_eq_cell a', ← get_eq_cell a, ← get_eq_cell b, hv, hn, hbj, hP _ hk]
          simp [cellCompat_none_left, cellCompat]
      exact ⟨fun h => ⟨hcompat ▸ h, hmerge⟩, fun h _ => hcompat ▸ h⟩
    · push Not at hseed
      obtain ⟨j, k, hn, hk, hv, hbj⟩ := hseed
      obtain ⟨w, hw⟩ : ∃ w, b.get j = some w := Option.isSome_iff_exists.1 (hbe _ hk)
      have hwk : w ≠ k := fun h => hbj (h ▸ hw)
      have hc1 : compat m P Q a' b = false := by
        cases h : compat m P Q a' b
        · rfl
        · have := compat_get h hv hw; exact absurd this.symm hwk
      refine ⟨fun h => (by rw [hc1] at h; cases h), fun _ hg => ?_⟩
      have := hc _ hk _ hg
      rw [get_merge, hn, hw] at this
      exact absurd (Option.some.inj this) hwk
  unfold joinB
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine ⟨?_, ?_⟩
  · rw [List.filter_filterMap, List.filter_filterMap]
    apply List.filterMap_congr
    intro b hb
    obtain ⟨p1, p2⟩ := per b hb
    by_cases h1 : compat m P Q a' b = true
    · obtain ⟨h2, h3⟩ := p1 h1
      simp [h1, h2, h3]
    · have h1' : compat m P Q a' b = false := by simpa using h1
      cases h2 : compat m P Q a b
      · simp [h1', h2]
      · cases hg : g (merge a b)
        · simp [h1', h2, hg, Option.filter]
        · exact absurd (p2 h2 hg) h1
  · intro x hx
    obtain ⟨b, hb, he⟩ := List.mem_filterMap.1 hx
    split at he
    · next h1 =>
      cases he
      obtain ⟨h2, h3⟩ := (per b hb).1 h1
      exact List.mem_filterMap.2 ⟨b, hb, by simp [h2, h3]⟩
    · cases he

/-! ## The greedy order is an order -/

theorem foldl_choose_mem {α : Type} (q : α → α → Bool) : ∀ (l : List α) (x : α),
    l.foldl (fun b p => if q p b then p else b) x ∈ x :: l
  | [], x => List.mem_cons_self ..
  | y :: ys, x => by
    simp only [List.foldl_cons]
    split
    · exact List.mem_cons_of_mem _ (foldl_choose_mem q ys y)
    · have := foldl_choose_mem q ys x
      rcases List.mem_cons.1 this with h | h
      · rw [h]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem perm_cons_filter_idx {β : Type} {rest : List (Nat × β)} (hn : (rest.map (·.1)).Nodup)
    {best : Nat × β} (hb : best ∈ rest) : (best :: rest.filter (·.1 != best.1)).Perm rest := by
  have hnd : rest.Nodup := List.Nodup.of_map _ hn
  refine (List.perm_ext_iff_of_nodup ?_ hnd).2 fun x => ?_
  · refine List.nodup_cons.2 ⟨fun h => by simp at h, hnd.filter _⟩
  · simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq]
    constructor
    · rintro (rfl | ⟨h, _⟩)
      · exact hb
      · exact h
    · intro hx
      by_cases he : x.1 = best.1
      · exact Or.inl ((List.inj_on_of_nodup_map hn) hx hb he)
      · exact Or.inr ⟨hx, he⟩

theorem greedyGo_perm (count : Value → Option Nat) : ∀ (fuel : Nat) (bound : List Var)
    (rest : List (Nat × TriplePattern)), (rest.map (·.1)).Nodup → rest.length ≤ fuel →
    (greedyOrder.go count fuel bound rest).Perm rest
  | 0, _, rest, _, hl => by
    have : rest = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    subst this; rfl
  | fuel + 1, bound, [], _, _ => by simp [greedyOrder.go]
  | fuel + 1, bound, first :: more, hn, hl => by
    simp only [greedyOrder.go]
    set best := (first :: more).foldl (fun b p => if greedyOrder.better count bound p b then p else b) first
    have hb : best ∈ first :: more := by
      have := foldl_choose_mem (fun p b => greedyOrder.better count bound p b) (first :: more) first
      rcases List.mem_cons.1 this with h | h
      · have hb' : best = first := h
        rw [hb']; exact List.mem_cons_self ..
      · exact h
    have hn' : (((first :: more).filter (·.1 != best.1)).map (·.1)).Nodup :=
      (List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) hn)
    have hlen : ((first :: more).filter (·.1 != best.1)).length ≤ fuel := by
      have h1 := (perm_cons_filter_idx hn hb).length_eq
      simp only [List.length_cons] at h1 hl
      omega
    exact ((greedyGo_perm count fuel _ _ hn' hlen).cons best).trans (perm_cons_filter_idx hn hb)

/-- Statistics and the greedy rule change only the order: the greedy order is a permutation. -/
theorem greedyOrder_perm (bound0 : List Var) (pats : List (Nat × TriplePattern)) (count : Value → Option Nat)
    (hn : (pats.map (·.1)).Nodup) : (greedyOrder bound0 pats count).Perm pats :=
  greedyGo_perm count _ bound0 pats hn (Nat.le_refl _)

/-! ## Folds from a schema-bag -/

theorem foldl_from (m : Missing) (n : Nat) (L : List SBag) (a : SBag) :
    SRel (L.foldl (joinSB m) a) (joinSB m a (joinAll m n L)) := by
  have h1 := joinAll_append m n [a] L
  have h2 : SRel (joinAll m n ([a] ++ L)) (L.foldl (joinSB m) a) := by
    unfold joinAll
    rw [List.singleton_append, List.foldl_cons]
    exact foldl_congr m L (joinSB_unit_left m n a)
  have h3 : SRel (joinAll m n [a]) a := by
    unfold joinAll; simp only [List.foldl_cons, List.foldl_nil]; exact joinSB_unit_left m n a
  exact h2.symm.trans (h1.trans (joinSB_congr m _ h3))

section
variable {st : ModelState} (hB : IdBridge st)
include hB

/-- nested-loop-join "Filter push-down": the index nested loop that applies each early conjunct
as soon as the patterns placed so far bind its variables returns the reference fold filtered
by the applied conjuncts; the rest are returned for later. -/
theorem ev_inljGo (E : Env) : ∀ (order : List (Nat × TriplePattern)) (P : Schema) (rows rows' : Bag)
    (bound : List Nat) (pending : List Pushed), rows.Perm rows' → (∀ r ∈ rows', Binds bound r) →
    (∀ c ∈ pending, PushedOk c) →
    ∃ P' R applied later, ev st (inljRun.go E P rows bound pending order) = .ok (.ok (P', R, later)) ∧
      pending.Perm (applied ++ later) ∧ P' = (patFold st E order (P, rows')).1 ∧
      R.Perm ((patFold st E order (P, rows')).2.filter (allHold applied)) ∧
      (∀ c ∈ applied, PushedOk c ∧ c.early = true ∧ ∀ i ∈ c.vars, i ∈ bound ++ orderVars E order)
  | [], P, rows, rows', bound, pending, hp, _, _ =>
    ⟨P, rows, [], pending, rfl, by simp, rfl, by
      have : rows'.filter (allHold []) = rows' := List.filter_eq_self.2 (fun _ _ => rfl)
      simpa [patFold, this] using hp, by simp⟩
  | (i, t) :: rest, P, rows, rows', bound, pending, hp, hb, hok => by
    unfold inljRun.go
    rw [ev_bind, ev_resolveViewE]
    simp only
    obtain ⟨R1, hR1, hp1⟩ := ev_inljStep hB E P (E.schemaOf (.triple t)) t rows
    rw [ev_bind, hR1]
    simp only
    set bound1 := bound ++ t.vars.map E.idx
    set f : Pushed → Bool := fun c => c.early && c.vars.all bound1.contains
    rw [List.partition_eq_filter_filter, foldl_filterB]
    set J1 := joinB E.sem.missing P (E.schemaOf (.triple t)) rows' (tpBag st E t)
    have hJ1 : ∀ r ∈ J1, Binds bound1 r := by
      intro r hr
      obtain ⟨a, ha, b, hb', rfl⟩ := mem_joinB hr
      intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · exact binds_merge_left (hb a ha) b j hj
      · exact binds_merge_right (tpBag_binds hb') a j hj
    have hnow : ∀ c ∈ pending.filter f, PushedOk c ∧ c.early = true ∧ ∀ i ∈ c.vars, i ∈ bound1 := by
      intro c hc
      obtain ⟨hc1, hc2⟩ := List.mem_filter.1 hc
      simp only [f, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hc2
      exact ⟨hok c hc1, hc2.1, hc2.2⟩
    obtain ⟨P', R, applied', later, hev, hpl, hP', hR, happ⟩ :=
      ev_inljGo E rest (Schema.union P (E.schemaOf (.triple t))) (R1.filter (allHold (pending.filter f)))
        (J1.filter (allHold (pending.filter f))) bound1 (pending.filter fun c => !f c)
        ((hp1.trans (joinB_perm_left _ hp)).filter _)
        (fun r hr => hJ1 r (List.mem_filter.1 hr).1)
        (fun c hc => hok c (List.mem_filter.1 hc).1)
    have hfold := patFold_filter st E hnow rest (Schema.union P (E.schemaOf (.triple t))) J1 hJ1
    refine ⟨P', R, pending.filter f ++ applied', later, hev, ?_, ?_, ?_, ?_⟩
    · refine (List.filter_append_perm f pending).symm.trans ?_
      rw [List.append_assoc]
      exact List.Perm.append_left _ hpl
    · rw [hP', hfold]; rfl
    · refine hR.trans ?_
      rw [hfold]
      show List.Perm _ ((patFold st E rest (Schema.union P (E.schemaOf (.triple t)), J1)).2.filter _)
      rw [List.filter_filter]
      apply List.Perm.of_eq
      congr 1; funext r; rw [allHold_append, Bool.and_comm]
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨h1, h2, h3⟩ := hnow c hc
        refine ⟨h1, h2, fun j hj => ?_⟩
        have := h3 j hj
        simp only [bound1, orderVars, List.flatMap_cons, List.mem_append] at this ⊢
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨h1, h2, h3⟩ := happ c hc
        refine ⟨h1, h2, fun j hj => ?_⟩
        have := h3 j hj
        simp only [bound1, orderVars, List.flatMap_cons, List.mem_append] at this ⊢
        rcases this with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-- The matches of one left row in a left join. -/
def ljMatches (m : Missing) (P Q : Schema) (c : Option RExpr) (a : Row) (ys : Bag) : Bag :=
  ys.filterMap fun b =>
    if compat m P Q a b then
      let r := merge a b
      if (match c with | some e => e.holds r | none => true) then some r else none
    else none

omit hB in
theorem ljMatches_eq (m : Missing) (P Q : Schema) (c : Option RExpr) (a : Row) (ys : Bag) :
    ljMatches m P Q c a ys = (match c with
      | some e => (joinB m P Q [a] ys).filter e.holds
      | none => joinB m P Q [a] ys) := by
  unfold ljMatches joinB
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  cases c with
  | none => simp
  | some e =>
    simp only
    induction ys with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.filterMap_cons]
      by_cases hc : compat m P Q a b = true
      · by_cases he : e.holds (merge a b) = true
        · simp [hc, he, ih]
        · simp [hc, he, ih]
      · simp [hc, ih]

omit hB in
theorem leftJoinB_eq (m : Missing) (P Q : Schema) (c : Option RExpr) (xs ys : Bag) :
    leftJoinB m P Q c xs ys = xs.flatMap fun a =>
      if (ljMatches m P Q c a ys).isEmpty then [a] else ljMatches m P Q c a ys := rfl

omit hB in
theorem ite_empty_perm {a : Row} {ms ms' : Bag} (h : ms.Perm ms') :
    (if ms.isEmpty then [a] else ms).Perm (if ms'.isEmpty then [a] else ms') := by
  have : ms.isEmpty = ms'.isEmpty := by
    cases ms with
    | nil => rw [List.Perm.nil_eq h]
    | cons x xs => cases ms' with
      | nil => exact absurd h.length_eq (by simp)
      | cons y ys => rfl
  rw [this]; split
  · exact List.Perm.refl _
  · exact h

omit hB in
theorem zipIdx_swap_nodup {α : Type} (l : List α) : ((l.zipIdx.map fun (t, i) => (i, t)).map (·.1)).Nodup := by
  rw [List.map_map]
  have : ((fun x : Nat × α => x.1) ∘ fun (x : α × Nat) => (x.2, x.1)) = (·.2) := by funext x; rfl
  rw [this, List.zipIdx_map_snd]
  exact List.nodup_range' ..

/-- The reference join of a list of stored patterns. -/
def patJoin (st : ModelState) (E : Env) (pats : List TriplePattern) : SBag :=
  joinAll E.sem.missing E.n (pats.map fun t => (E.schemaOf (.triple t), tpBag st E t))

/-- nested-loop-join "Binding passing": a `LeftJoin` whose right side is a join of stored patterns,
evaluated by passing each left row sideways into the right side's index nested loop, is the
reference left join with the patterns' reference join. -/
theorem ev_leftJoinSideways (E : Env) (P : Schema) (c : Option RExpr) (pats : List TriplePattern) (xs : Bag) :
    ∃ R, ev st (leftJoinSideways E P c pats xs) = .ok (.ok R) ∧
      R.Perm (isoFilter E.iso (leftJoinB E.sem.missing P (patJoin st E pats).1 c xs (patJoin st E pats).2)) := by
  unfold leftJoinSideways
  simp only
  set order := greedyOrder [] (pats.zipIdx.map fun (t, i) => (i, t)) E.predCount
  have hord : order.Perm (pats.zipIdx.map fun (t, i) => (i, t)) :=
    greedyOrder_perm _ _ _ (zipIdx_swap_nodup pats)
  have hL : (order.map fun t => (E.schemaOf (.triple t.2), tpBag st E t.2)).Perm
      (pats.map fun t => (E.schemaOf (.triple t), tpBag st E t)) := by
    refine (hord.map _).trans (List.Perm.of_eq ?_)
    rw [List.map_map]
    conv => rhs; rw [← List.zipIdx_map_fst 0 pats, List.map_map]
    rfl
  -- one left row
  have hrow : ∀ a, ∃ P' ms, ev st (inljRun E P [a] order []) = .ok (.ok (P', ms, [])) ∧
      ms.Perm (joinB E.sem.missing P (patJoin st E pats).1 [a] (patJoin st E pats).2) := by
    intro a
    obtain ⟨P', ms, h1, h2⟩ := ev_inljGo_nil hB E order P [a] [a] [] (List.Perm.refl _)
    refine ⟨P', ms, h1, h2.2.trans ?_⟩
    have := (foldl_perm E.sem.missing hL (P, [a])).trans (foldl_from E.sem.missing E.n _ (P, [a]))
    exact this.2
  set f : Row → Bag := fun a =>
    match ev st (inljRun E P [a] order []) with
    | .ok (.ok (_, ms, _)) =>
      let ms := match c with
        | some e => ms.filter e.holds
        | none => ms
      if ms.isEmpty then [a] else ms
    | _ => []
  rw [ev_bind, ev_mapM st (g := f) xs (fun a _ => by
    obtain ⟨P', ms, h1, _⟩ := hrow a
    rw [ev_bind, h1]
    simp only [f, h1]
    rfl)]
  refine ⟨_, rfl, isoFilter_perm _ ?_⟩
  rw [← List.flatMap_def, leftJoinB_eq]
  refine flatMap_perm_congr fun a _ => ?_
  obtain ⟨P', ms, h1, h2⟩ := hrow a
  simp only [f, h1]
  apply ite_empty_perm
  rw [ljMatches_eq]
  cases c with
  | none => exact h2
  | some e => exact h2.filter _

end

end Tiramemsu.Exec
