/-
Merge laws of the 2P-set of statements (D15).
Requirements: merge-laws / "Merge laws" and "Merge preserves never forget".
-/
import Tiramemsu.Model.Merge
import TiramemsuProofs.Store.Order
import Mathlib.Tactic

namespace Tiramemsu.Model

open Tiramemsu.Store

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The minimum of two keys -/

/-- The smaller of two keys. -/
def kmin (x y : List (Option Int)) : List (Option Int) := if cmpKey x y == .gt then y else x

theorem kmin_comm (x y : List (Option Int)) : kmin x y = kmin y x := by
  unfold kmin
  have hs := cmpKey_swap x y
  cases h : cmpKey x y <;> simp_all
  · exact cmpKey_eq_iff.1 h

theorem kmin_self (x : List (Option Int)) : kmin x x = x := by unfold kmin; split <;> rfl

theorem kmin_cases (x y : List (Option Int)) : kmin x y = x ∨ kmin x y = y := by
  unfold kmin; split <;> simp

theorem cmp_gt_iff (x y : List (Option Int)) : cmpKey x y = .gt ↔ cmpKey y x = .lt := by
  rw [cmpKey_swap y x]; cases cmpKey x y <;> simp

theorem cmp_le_trans {x y z : List (Option Int)} (h1 : cmpKey x y ≠ .gt) (h2 : cmpKey y z ≠ .gt) :
    cmpKey x z ≠ .gt := by
  cases hxy : cmpKey x y <;> cases hyz : cmpKey y z <;> simp_all
  · rw [cmpKey_lt_trans hxy hyz]; simp
  · rw [← cmpKey_eq_iff.1 hyz, hxy]; simp
  · rw [cmpKey_eq_iff.1 hxy, hyz]; simp
  · rw [cmpKey_eq_iff.1 hxy, cmpKey_eq_iff.1 hyz, cmpKey_refl]; simp

theorem cmp_gt_trans {x y z : List (Option Int)} (h1 : cmpKey x y = .gt) (h2 : cmpKey y z = .gt) :
    cmpKey x z = .gt := by
  rw [cmp_gt_iff] at *; exact cmpKey_lt_trans h2 h1

theorem kmin_assoc (x y z : List (Option Int)) : kmin (kmin x y) z = kmin x (kmin y z) := by
  unfold kmin
  by_cases gxy : cmpKey x y = .gt <;> by_cases gyz : cmpKey y z = .gt
  · simp [gxy, gyz, cmp_gt_trans gxy gyz]
  · simp [gxy, gyz]
  · simp [gxy, gyz]
  · have := cmp_le_trans gxy gyz
    simp [gxy, gyz, this]

/-! ## Rows as two keys -/

theorem minBy_key (k : TripleRow → List (Option Int)) (a b : TripleRow) :
    k (minBy k a b) = kmin (k a) (k b) := by
  unfold minBy kmin; split <;> rfl

theorem contentKey_ret (r : TripleRow) (t k : Option Int64) :
    contentKey { r with tRet := t, retKind := k } = contentKey r := rfl

theorem retKey_set (r c : TripleRow) :
    retKey { c with tRet := r.tRet, retKind := r.retKind } = retKey r := rfl

theorem contentKey_join (a b : TripleRow) : contentKey (joinRow a b) = kmin (contentKey a) (contentKey b) := by
  unfold joinRow; simp only [contentKey_ret, minBy_key]

theorem retKey_join (a b : TripleRow) : retKey (joinRow a b) = kmin (retKey a) (retKey b) := by
  unfold joinRow; simp only [retKey_set, minBy_key]

theorem optMap_toInt_inj {a b : Option Int64} (h : a.map (·.toInt) = b.map (·.toInt)) : a = b := by
  cases a <;> cases b <;> simp_all [Int64.toInt_inj]

/-- A row is determined by its content key and its retraction key. -/
theorem row_ext {a b : TripleRow} (hc : contentKey a = contentKey b) (hr : retKey a = retKey b) :
    a = b := by
  rcases a with ⟨e, s, p, o, ta, tr, vf, vt, rk⟩
  rcases b with ⟨e', s', p', o', ta', tr', vf', vt', rk'⟩
  simp only [contentKey, retKey, List.cons.injEq, Option.some.injEq, and_true] at hc hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  obtain ⟨_, h8, h9⟩ := hr
  simp only [Int64.toInt_inj] at h1 h2 h3 h4 h5
  rw [optMap_toInt_inj h6, optMap_toInt_inj h7, optMap_toInt_inj h8, optMap_toInt_inj h9, h1, h2, h3, h4, h5]

theorem joinRow_comm (a b : TripleRow) : joinRow a b = joinRow b a :=
  row_ext (by rw [contentKey_join, contentKey_join, kmin_comm]) (by rw [retKey_join, retKey_join, kmin_comm])

theorem joinRow_assoc (a b c : TripleRow) : joinRow (joinRow a b) c = joinRow a (joinRow b c) :=
  row_ext (by simp only [contentKey_join, kmin_assoc]) (by simp only [retKey_join, kmin_assoc])

theorem joinRow_self (a : TripleRow) : joinRow a a = a :=
  row_ext (by rw [contentKey_join, kmin_self]) (by rw [retKey_join, kmin_self])

theorem joinRow_eid {a b : TripleRow} (h : a.eid = b.eid) : (joinRow a b).eid = a.eid := by
  have hk := contentKey_join a b
  rcases kmin_cases (contentKey a) (contentKey b) with h' | h' <;> rw [h'] at hk <;>
    simp only [contentKey, List.cons.injEq, Option.some.injEq, Int64.toInt_inj] at hk
  · exact hk.1
  · rw [hk.1, h]

/-! ## Joins of optional states -/

theorem joinOpt_comm (x y : Option TripleRow) : joinOpt x y = joinOpt y x := by
  cases x <;> cases y <;> simp [joinOpt, joinRow_comm]

theorem joinOpt_assoc (x y z : Option TripleRow) : joinOpt (joinOpt x y) z = joinOpt x (joinOpt y z) := by
  cases x <;> cases y <;> cases z <;> simp [joinOpt, joinRow_assoc]

theorem joinOpt_self (x : Option TripleRow) : joinOpt x x = x := by
  cases x <;> simp [joinOpt, joinRow_self]

/-! ## Statement sets -/

/-- Strictly ascending by eid. -/
def Sorted (s : StmtSet) : Prop := s.Pairwise fun a b => a.eid.toInt < b.eid.toInt

theorem lookup_cons (x : TripleRow) (xs : StmtSet) (e : Int) :
    lookup (x :: xs) e = if x.eid.toInt = e then some x else lookup xs e := by
  unfold lookup; by_cases h : x.eid.toInt = e <;> simp [h, List.find?_cons]

theorem lookup_none_of_lt {xs : StmtSet} {e : Int} (h : ∀ x ∈ xs, e < x.eid.toInt) : lookup xs e = none := by
  unfold lookup
  rw [List.find?_eq_none]
  intro x hx
  have := h x hx
  simp; omega

theorem lookup_eid {xs : StmtSet} {e : Int} {r : TripleRow} (h : lookup xs e = some r) : r.eid.toInt = e := by
  unfold lookup at h
  simpa using List.find?_some h

theorem mem_of_lookup {xs : StmtSet} {e : Int} {r : TripleRow} (h : lookup xs e = some r) : r ∈ xs := by
  unfold lookup at h; exact List.mem_of_find?_eq_some h

/-- Every row of a merge has the eid of a row of one side. -/
theorem merge_eids (xs ys : StmtSet) : ∀ z ∈ merge xs ys, (∃ x ∈ xs, x.eid = z.eid) ∨ (∃ y ∈ ys, y.eid = z.eid) := by
  induction xs, ys using merge.induct with
  | case1 ys => intro z hz; simp only [merge] at hz; exact Or.inr ⟨z, hz, rfl⟩
  | case2 xs _ => intro z hz; simp only [merge] at hz; exact Or.inl ⟨z, hz, rfl⟩
  | case3 x xs y ys h ih =>
    intro z hz
    rw [merge, if_pos h] at hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact Or.inl ⟨z, List.mem_cons_self .., rfl⟩
    · rcases ih z hz with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
      · exact Or.inl ⟨a, List.mem_cons_of_mem _ ha, he⟩
      · exact Or.inr ⟨a, ha, he⟩
  | case4 x xs y ys h1 h2 ih =>
    intro z hz
    rw [merge, if_neg h1, if_pos h2] at hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact Or.inr ⟨z, List.mem_cons_self .., rfl⟩
    · rcases ih z hz with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
      · exact Or.inl ⟨a, ha, he⟩
      · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, he⟩
  | case5 x xs y ys h1 h2 ih =>
    intro z hz
    rw [merge, if_neg h1, if_neg h2] at hz
    rcases List.mem_cons.1 hz with rfl | hz
    · have : x.eid = y.eid := Int64.toInt_inj.1 (by omega)
      exact Or.inl ⟨x, List.mem_cons_self .., (joinRow_eid this).symm⟩
    · rcases ih z hz with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
      · exact Or.inl ⟨a, List.mem_cons_of_mem _ ha, he⟩
      · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, he⟩

/-- The merge of sorted sets is sorted. -/
theorem merge_sorted : ∀ {xs ys : StmtSet}, Sorted xs → Sorted ys → Sorted (merge xs ys) := by
  intro xs ys
  induction xs, ys using merge.induct with
  | case1 ys => intro _ h; simpa [merge] using h
  | case2 xs _ => intro h _; simpa [merge] using h
  | case3 x xs y ys h ih =>
    intro hx hy
    rw [merge, if_pos h]
    have hx' := List.pairwise_cons.1 hx
    refine List.pairwise_cons.2 ⟨?_, ih hx'.2 hy⟩
    intro z hz
    rcases merge_eids _ _ z hz with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
    · rw [← he]; exact hx'.1 a ha
    · rw [← he]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact h
      · exact lt_trans h ((List.pairwise_cons.1 hy).1 a ha)
  | case4 x xs y ys h1 h2 ih =>
    intro hx hy
    rw [merge, if_neg h1, if_pos h2]
    have hy' := List.pairwise_cons.1 hy
    refine List.pairwise_cons.2 ⟨?_, ih hx hy'.2⟩
    intro z hz
    rcases merge_eids _ _ z hz with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
    · rw [← he]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact h2
      · exact lt_trans h2 ((List.pairwise_cons.1 hx).1 a ha)
    · rw [← he]; exact hy'.1 a ha
  | case5 x xs y ys h1 h2 ih =>
    intro hx hy
    rw [merge, if_neg h1, if_neg h2]
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    have hxy : x.eid = y.eid := Int64.toInt_inj.1 (by omega)
    refine List.pairwise_cons.2 ⟨?_, ih hx'.2 hy'.2⟩
    intro z hz
    rw [joinRow_eid hxy]
    rcases merge_eids _ _ z hz with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
    · rw [← he]; exact hx'.1 a ha
    · rw [← he, hxy]; exact hy'.1 a ha

theorem joinOpt_none_right (x : Option TripleRow) : joinOpt x none = x := by cases x <;> rfl

theorem lookup_none_head {x : TripleRow} {xs : StmtSet} (hx : Sorted (x :: xs)) {e : Int}
    (h : e < x.eid.toInt) : lookup (x :: xs) e = none := by
  apply lookup_none_of_lt
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact h
  · exact lt_trans h ((List.pairwise_cons.1 hx).1 z hz)

/-- The merge is pointwise the join: `lookup (merge a b) e = join (lookup a e) (lookup b e)`. -/
theorem lookup_merge : ∀ {xs ys : StmtSet}, Sorted xs → Sorted ys → ∀ e,
    lookup (merge xs ys) e = joinOpt (lookup xs e) (lookup ys e) := by
  intro xs ys
  induction xs, ys using merge.induct with
  | case1 ys => intro _ _ e; simp [merge, lookup, joinOpt]
  | case2 xs h => intro _ _ e; cases xs with
    | nil => simp [merge, lookup, joinOpt]
    | cons x xs => simp [merge, joinOpt_none_right, lookup]
  | case3 x xs y ys h ih =>
    intro hx hy e
    have hm : merge (x :: xs) (y :: ys) = x :: merge xs (y :: ys) := by rw [merge, if_pos h]
    rw [hm, lookup_cons, lookup_cons, ih (List.pairwise_cons.1 hx).2 hy]
    by_cases hxe : x.eid.toInt = e
    · subst hxe
      rw [if_pos rfl, if_pos rfl, lookup_none_head hy h]; rfl
    · rw [if_neg hxe, if_neg hxe]
  | case4 x xs y ys h1 h2 ih =>
    intro hx hy e
    have hm : merge (x :: xs) (y :: ys) = y :: merge (x :: xs) ys := by rw [merge, if_neg h1, if_pos h2]
    rw [hm, lookup_cons, ih hx (List.pairwise_cons.1 hy).2, lookup_cons y ys]
    by_cases hye : y.eid.toInt = e
    · subst hye
      rw [if_pos rfl, if_pos rfl, lookup_none_head hx h2]; rfl
    · rw [if_neg hye, if_neg hye]
  | case5 x xs y ys h1 h2 ih =>
    intro hx hy e
    have hxy : x.eid = y.eid := Int64.toInt_inj.1 (by omega)
    have hm : merge (x :: xs) (y :: ys) = joinRow x y :: merge xs ys := by rw [merge, if_neg h1, if_neg h2]
    rw [hm, lookup_cons, lookup_cons, lookup_cons, ih (List.pairwise_cons.1 hx).2 (List.pairwise_cons.1 hy).2,
      joinRow_eid hxy]
    by_cases hxe : x.eid.toInt = e
    · rw [if_pos hxe, if_pos hxe, if_pos (by rw [← hxy]; exact hxe)]; rfl
    · rw [if_neg hxe, if_neg hxe, if_neg (by rw [← hxy]; exact hxe)]

/-- Extensionality: sorted statement sets with equal lookups are equal. -/
theorem stmtSet_ext : ∀ {xs ys : StmtSet}, Sorted xs → Sorted ys → (∀ e, lookup xs e = lookup ys e) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by have := h y.eid.toInt; simp [lookup] at this
  | x :: _, [], _, _, h => by have := h x.eid.toInt; simp [lookup] at this
  | x :: xs, y :: ys, hx, hy, h => by
    have hx' := List.pairwise_cons.1 hx
    have hy' := List.pairwise_cons.1 hy
    -- the heads have the smallest eid on each side, so they are equal
    have hxy : x = y := by
      have h1 := h x.eid.toInt
      have h2 := h y.eid.toInt
      rw [lookup_cons, if_pos rfl, lookup_cons] at h1
      rw [lookup_cons, lookup_cons, if_pos rfl] at h2
      by_cases he : y.eid.toInt = x.eid.toInt
      · rw [if_pos he] at h1; exact Option.some.inj h1
      · rw [if_neg he] at h1
        have hm := lookup_eid h1.symm
        have hlt := hy'.1 x (mem_of_lookup h1.symm)
        by_cases he' : x.eid.toInt = y.eid.toInt
        · exact absurd he'.symm he
        · rw [if_neg he'] at h2
          have hm2 := hx'.1 y (mem_of_lookup h2)
          omega
    subst hxy
    congr 1
    apply stmtSet_ext hx'.2 hy'.2
    intro e
    have := h e
    rw [lookup_cons, lookup_cons] at this
    by_cases he : x.eid.toInt = e
    · subst he
      rw [lookup_none_of_lt hx'.1, lookup_none_of_lt hy'.1]
    · simpa [he] using this

/-- Merge is commutative. -/
theorem merge_comm {a b : StmtSet} (ha : Sorted a) (hb : Sorted b) : merge a b = merge b a :=
  stmtSet_ext (merge_sorted ha hb) (merge_sorted hb ha) fun e => by
    rw [lookup_merge ha hb, lookup_merge hb ha, joinOpt_comm]

/-- Merge is associative. -/
theorem merge_assoc {a b c : StmtSet} (ha : Sorted a) (hb : Sorted b) (hc : Sorted c) :
    merge (merge a b) c = merge a (merge b c) :=
  stmtSet_ext (merge_sorted (merge_sorted ha hb) hc) (merge_sorted ha (merge_sorted hb hc)) fun e => by
    rw [lookup_merge (merge_sorted ha hb) hc, lookup_merge ha hb, lookup_merge ha (merge_sorted hb hc),
      lookup_merge hb hc, joinOpt_assoc]

/-- Merge is idempotent. -/
theorem merge_self {a : StmtSet} (ha : Sorted a) : merge a a = a :=
  stmtSet_ext (merge_sorted ha ha) ha fun e => by rw [lookup_merge ha ha, joinOpt_self]

/-! ## Never forget under merge -/

/-- Every eid of either side is in the merge. -/
theorem merge_keeps_eids {a b : StmtSet} (ha : Sorted a) (hb : Sorted b) (e : Int) :
    (lookup (merge a b) e).isSome ↔ (lookup a e).isSome ∨ (lookup b e).isSome := by
  rw [lookup_merge ha hb]
  cases lookup a e <;> cases lookup b e <;> simp [joinOpt]

/-- The content of a row (everything but the retraction). -/
def content (r : TripleRow) : TripleRow := { r with tRet := none, retKind := none }

theorem content_eq_of_key {a b : TripleRow} (h : contentKey a = contentKey b) : content a = content b :=
  row_ext (by simpa [content, contentKey] using h) rfl

theorem contentKey_eq_of_content {a b : TripleRow} (h : content a = content b) : contentKey a = contentKey b := by
  have := congrArg contentKey h; simpa [content, contentKey] using this

theorem joinRow_ret (x y : TripleRow) :
    ((joinRow x y).tRet, (joinRow x y).retKind) =
      if cmpKey (retKey x) (retKey y) = .gt then (y.tRet, y.retKind) else (x.tRet, x.retKind) := by
  simp only [joinRow, minBy]
  by_cases h : cmpKey (retKey x) (retKey y) = .gt <;> simp [h]

/-- A live row's retraction key is above a retracted row's. -/
theorem retKey_live_gt {x y : TripleRow} (hx : x.tRet = none) (hy : y.tRet.isSome) :
    cmpKey (retKey x) (retKey y) = .gt := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hy
  simp [retKey, hx, ht, cmpKey, cmpOpt]
  rfl

theorem joinRow_ret_cases (x y : TripleRow) :
    ((joinRow x y).tRet = x.tRet ∧ (joinRow x y).retKind = x.retKind ∧ (x.tRet = none → y.tRet = none)) ∨
    ((joinRow x y).tRet = y.tRet ∧ (joinRow x y).retKind = y.retKind ∧ (y.tRet = none → x.tRet = none)) := by
  have hr := joinRow_ret x y
  by_cases h : cmpKey (retKey x) (retKey y) = .gt
  · rw [if_pos h] at hr
    simp only [Prod.mk.injEq] at hr
    right
    refine ⟨hr.1, hr.2, fun hy => ?_⟩
    cases hx : x.tRet with
    | none => rfl
    | some t =>
      have := retKey_live_gt hy (show x.tRet.isSome by simp [hx])
      rw [cmpKey_swap, h] at this; cases this
  · rw [if_neg h] at hr
    simp only [Prod.mk.injEq] at hr
    left
    refine ⟨hr.1, hr.2, fun hx => ?_⟩
    cases hy : y.tRet with
    | none => rfl
    | some t => exact absurd (retKey_live_gt hx (by simp [hy])) h

/-- When both sides agree on the content of every shared eid, the merge keeps each eid's
content and every retraction: a statement is live in the merge exactly when it is live on every
side that holds it. -/
theorem merge_never_forget {a b : StmtSet} (ha : Sorted a) (hb : Sorted b)
    (agree : ∀ e x y, lookup a e = some x → lookup b e = some y → content x = content y) (e : Int) :
    (∀ x, lookup a e = some x → ∃ z, lookup (merge a b) e = some z ∧ content z = content x ∧
        (x.tRet.isSome → z.tRet.isSome)) ∧
    (∀ y, lookup b e = some y → ∃ z, lookup (merge a b) e = some z ∧ content z = content y ∧
        (y.tRet.isSome → z.tRet.isSome)) ∧
    (∀ z, lookup (merge a b) e = some z →
        (z.tRet = none ↔ (∀ x, lookup a e = some x → x.tRet = none) ∧
                         (∀ y, lookup b e = some y → y.tRet = none))) := by
  rw [lookup_merge ha hb]
  have contentJoin (x y : TripleRow) (h : content x = content y) : content (joinRow x y) = content x := by
    apply content_eq_of_key
    rw [contentKey_join, contentKey_eq_of_content h, kmin_self]
  have someOf {r : Option Int64} : r.isSome ↔ r ≠ none := by cases r <;> simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    cases hy : lookup b e with
    | none => exact ⟨x, by simp [hx, joinOpt], rfl, id⟩
    | some y =>
      refine ⟨joinRow x y, by simp [hx, joinOpt], contentJoin x y (agree e x y hx hy), ?_⟩
      intro hs
      rw [someOf] at hs ⊢
      rcases joinRow_ret_cases x y with ⟨h1, _, _⟩ | ⟨h1, _, h3⟩
      · rw [h1]; exact hs
      · rw [h1]; exact fun hn => hs (h3 hn)
  · intro y hy
    cases hx : lookup a e with
    | none => exact ⟨y, by simp [hy, joinOpt], rfl, id⟩
    | some x =>
      refine ⟨joinRow x y, by simp [hy, joinOpt], ?_, ?_⟩
      · rw [contentJoin x y (agree e x y hx hy)]; exact agree e x y hx hy
      · intro hs
        rw [someOf] at hs ⊢
        rcases joinRow_ret_cases x y with ⟨h1, _, h3⟩ | ⟨h1, _, _⟩
        · rw [h1]; exact fun hn => hs (h3 hn)
        · rw [h1]; exact hs
  · intro z hz
    cases hx : lookup a e <;> cases hy : lookup b e <;> rw [hx, hy] at hz <;> simp only [joinOpt] at hz
    · cases hz
    · cases hz; simp
    · cases hz; simp
    · rename_i x y
      cases hz
      rcases joinRow_ret_cases x y with ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩ <;> rw [h1] <;> simp only [Option.some.injEq, forall_eq'] <;>
        constructor <;> intro h <;> simp_all

/-- Row-level well-formedness: no self-reference, a nonempty interval, `t_add ≤ t_ret`, and
`t_ret` and `ret_kind` both absent or both present. -/
def RowWF (r : TripleRow) : Prop :=
  r.s ≠ r.eid ∧ r.o ≠ r.eid ∧
  (∀ a b, r.vFrom = some a → r.vTo = some b → a.toInt < b.toInt) ∧
  (∀ t, r.tRet = some t → r.tAdd.toInt ≤ t.toInt) ∧ (r.tRet.isSome = r.retKind.isSome)

/-- Merge preserves row-level well-formedness when the sides agree on content. -/
theorem merge_rowWF {a b : StmtSet} (ha : Sorted a) (hb : Sorted b)
    (agree : ∀ e x y, lookup a e = some x → lookup b e = some y → content x = content y)
    (wa : ∀ r ∈ a, RowWF r) (wb : ∀ r ∈ b, RowWF r) : ∀ e z, lookup (merge a b) e = some z → RowWF z := by
  intro e z hz
  rw [lookup_merge ha hb] at hz
  cases hx : lookup a e <;> cases hy : lookup b e <;> simp_all [joinOpt]
  · subst hz; exact wb _ (mem_of_lookup hy)
  · subst hz; exact wa _ (mem_of_lookup hx)
  · rename_i x y
    subst hz
    have wx := wa x (mem_of_lookup hx)
    have wy := wb y (mem_of_lookup hy)
    have hc := agree e x y hx hy
    have cj : content (joinRow x y) = content x := by
      apply content_eq_of_key
      rw [contentKey_join, contentKey_eq_of_content hc, kmin_self]
    have keys : contentKey (joinRow x y) = contentKey x := by
      rw [contentKey_join, contentKey_eq_of_content hc, kmin_self]
    have ckx : contentKey y = contentKey x := (contentKey_eq_of_content hc).symm
    rcases joinRow_ret_cases x y with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · have : joinRow x y = x := row_ext keys (by simp [retKey, h1, h2])
      rw [this]; exact wx
    · have : joinRow x y = y := row_ext (by rw [keys, ckx]) (by simp [retKey, h1, h2])
      rw [this]; exact wy

end Tiramemsu.Model
