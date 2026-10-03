/-
Erasure of the annotated bag operators: dropping the eid lists of an annotated operator's output
gives the plain operator on the inputs without eid lists. Pure list facts; used by the
provenance erasure theorem (`TiramemsuProofs.Prov.Erasure`).
-/
import Tiramemsu.Prov.EvalProv
import TiramemsuProofs.Query.Aggregate

namespace Tiramemsu.Prov

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Exec

--# @lat: [[verification#Proven Query Semantics#Provenance Erasure]]

/-- The rows of an annotated bag, without their eid lists. -/
def er (xs : ABag) : Bag := xs.map (·.1)

@[simp] theorem er_nil : er [] = [] := rfl
@[simp] theorem er_cons (a : ARow) (xs : ABag) : er (a :: xs) = a.1 :: er xs := rfl
theorem er_append (xs ys : ABag) : er (xs ++ ys) = er xs ++ er ys := List.map_append
theorem er_flatten (xss : List ABag) : er xss.flatten = (xss.map er).flatten := by
  induction xss with
  | nil => rfl
  | cons x xs ih => simp only [List.flatten_cons, er_append, ih, List.map_cons]

theorem er_filter (p : Row → Bool) (xs : ABag) : er (xs.filter fun r => p r.1) = (er xs).filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : p x.1 <;> simp [h, er] <;> simp_all [er]

/-- A conditional pairing erases to the conditional on rows. -/
theorem er_filterMap (f : Row → Bool) (g : Row → Row) (h : List Int64 → List Int64) (ys : ABag) :
    er (ys.filterMap fun y => if f y.1 then some (g y.1, h y.2) else none) =
      (er ys).filterMap fun b => if f b then some (g b) else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih => by_cases hc : f y.1 = true <;> simp [hc, er] <;> simp_all [er]

theorem joinAB_er (m : Missing) (P Q : Schema) (xs ys : ABag) :
    er (joinAB m P Q xs ys) = joinB m P Q (er xs) (er ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [joinAB, joinB, List.flatMap_cons, er_append, er_cons] at ih ⊢
    rw [ih]
    congr 1
    exact er_filterMap (compat m P Q x.1) (merge x.1) (cite x.2) ys

theorem joinAllAB_go (m : Missing) : ∀ (xs : List (Schema × ABag)) (P : Schema) (acc : ABag),
    (xs.foldl (fun (P, acc) (Q, ys) => (Schema.union P Q, joinAB m P Q acc ys)) (P, acc)).1 =
      ((xs.map fun (Q, ys) => (Q, er ys)).foldl (joinSB m) (P, er acc)).1 ∧
    er (xs.foldl (fun (P, acc) (Q, ys) => (Schema.union P Q, joinAB m P Q acc ys)) (P, acc)).2 =
      ((xs.map fun (Q, ys) => (Q, er ys)).foldl (joinSB m) (P, er acc)).2
  | [], _, _ => ⟨rfl, rfl⟩
  | (Q, ys) :: xs, P, acc => by
    simp only [List.foldl_cons, List.map_cons]
    have := joinAllAB_go m xs (Schema.union P Q) (joinAB m P Q acc ys)
    rw [joinAB_er] at this
    exact this

/-- The annotated n-ary join erases to the plain one. -/
theorem joinAllAB_er (m : Missing) (n : Nat) (xs : List (Schema × ABag)) :
    (joinAllAB m xs).1 = (joinAll m n (xs.map fun (Q, ys) => (Q, er ys))).1 ∧
    er (joinAllAB m xs).2 = (joinAll m n (xs.map fun (Q, ys) => (Q, er ys))).2 :=
  joinAllAB_go m xs [] [([], [])]

theorem er_filterMap2 (f g : Row → Bool) (k : Row → Row) (h : List Int64 → List Int64) (ys : ABag) :
    er (ys.filterMap fun y => if f y.1 then (if g y.1 then some (k y.1, h y.2) else none) else none) =
      (er ys).filterMap fun b => if f b then (if g b then some (k b) else none) else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    by_cases hc : f y.1 = true <;> by_cases hg : g y.1 = true <;> simp [hc, hg, er] <;> simp_all [er]

theorem er_isEmpty (xs : ABag) : (er xs).isEmpty = xs.isEmpty := by cases xs <;> rfl

theorem leftJoinAB_er (m : Missing) (P Q : Schema) (c : Option RExpr) (xs ys : ABag) :
    er (leftJoinAB m P Q c xs ys) = leftJoinB m P Q c (er xs) (er ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [leftJoinAB, leftJoinB, List.flatMap_cons, er_append, er_cons] at ih ⊢
    rw [ih]
    congr 1
    cases c with
    | none =>
      simp only [ite_true]
      have key := er_filterMap (compat m P Q x.1) (merge x.1) (cite x.2) ys
      rw [← key, ← er_isEmpty]
      split <;> simp_all [er]
    | some e =>
      simp only []
      have key := er_filterMap2 (compat m P Q x.1) (fun b => e.holds (merge x.1 b)) (merge x.1) (cite x.2) ys
      rw [← key, ← er_isEmpty]
      split <;> simp_all [er]

theorem isoFilterAB_er (cols : List (Nat × Nat)) (xs : ABag) : er (isoFilterAB cols xs) = isoFilter cols (er xs) := by
  unfold isoFilterAB isoFilter
  split
  · rfl
  · exact er_filter _ xs

theorem er_map_snd {κ : Type} (f : κ × ABag → Row) (g : κ × ABag → List Int64) (xs : List (κ × ABag)) :
    er (xs.map fun x => (f x, g x)) = xs.map f := by
  simp [er, List.map_map, Function.comp_def]

/-- The groups of an annotated bag, without eid lists. -/
theorem groupCites_er {κ : Type} [BEq κ] (key : Row → κ) (xs : ABag) :
    (groupCites (fun r => key r.1) xs).map (fun kg => (kg.1, er kg.2)) =
      ((er xs).map key).eraseDups.map fun k => (k, (er xs).filter fun r => key r == k) := by
  unfold groupCites
  simp only [List.map_map, Function.comp_def]
  have hk : (xs.map fun r => key r.1) = (er xs).map key := by simp [er, List.map_map, Function.comp_def]
  rw [hk]
  congr 1
  funext k
  congr 1
  exact er_filter (fun r => key r == k) xs

theorem projectAB_er (keep : List Nat) (d : Bool) (xs : ABag) :
    er (projectAB keep d xs) = projectB keep d (er xs) := by
  unfold projectAB projectB
  have hys : er (xs.map fun (r, e) => (Row.restrict keep.contains r, e)) = (er xs).map (Row.restrict keep.contains) := by
    simp [er, List.map_map, Function.comp_def]
  cases d
  · simpa using hys
  · simp only [ite_true]
    rw [er_map_snd (fun kg => kg.1) (fun kg => unionCites kg.2)]
    have := congrArg (List.map Prod.fst) (groupCites_er (fun r : Row => r)
      (xs.map fun (r, e) => (Row.restrict keep.contains r, e)))
    simp only [List.map_map, Function.comp_def, List.map_id'] at this
    rw [hys] at this
    exact this

theorem aggregateAB_er (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool)) (xs : ABag) :
    er (aggregateAB n g aggs xs) = aggregateB n g aggs (er xs) := by
  unfold aggregateAB aggregateB
  have he : (er xs).isEmpty = xs.isEmpty := er_isEmpty xs
  by_cases h : (g.isEmpty && xs.isEmpty) = true
  · have h' : (g.isEmpty && (er xs).isEmpty) = true := by rw [he]; exact h
    simp only [h, h', ite_true]
    rfl
  · have h' : (g.isEmpty && (er xs).isEmpty) = false := by rw [he]; simpa using h
    simp only [h, h', Bool.false_eq_true, ite_false]
    rw [er_map_snd (fun kg => aggregateAB.groupRow' n g aggs (kg.1, kg.2.map (·.1))) (fun kg => unionCites kg.2)]
    have := groupCites_er (groupKey g) xs
    unfold groupBy
    rw [← this, List.map_map]
    rfl

theorem orderLimitAB_er (m : Missing) (keys : List (RExpr × Bool)) (s l : Option Nat) (xs : ABag) :
    er (orderLimitAB m keys s l xs) = orderLimitB m keys s l (er xs) := by
  unfold orderLimitAB orderLimitB
  have hs : ((((xs.map fun ar => (keys.map fun (e, _) => e.eval ar.1, ar)).mergeSort fun a b =>
        orderLe m (keys.map (·.2)) (a.1, a.2.1) (b.1, b.2.1)).map (·.2)).map (·.1)) =
      (((er xs).map fun r => (keys.map fun (e, _) => e.eval r, r)).mergeSort (orderLe m (keys.map (·.2)))).map (·.2) := by
    have hm := List.map_mergeSort (r := fun (a b : List (Option Value) × ARow) =>
        orderLe m (keys.map (·.2)) (a.1, a.2.1) (b.1, b.2.1)) (s := orderLe m (keys.map (·.2)))
      (f := fun (a : List (Option Value) × ARow) => (a.1, a.2.1))
      (l := xs.map fun ar => (keys.map fun (e, _) => e.eval ar.1, ar)) (fun _ _ _ _ => rfl)
    have hl : ((xs.map fun ar => (keys.map fun (e, _) => e.eval ar.1, ar)).map
        fun (a : List (Option Value) × ARow) => (a.1, a.2.1)) =
        (er xs).map fun r => (keys.map fun (e, _) => e.eval r, r) := by
      simp [er, List.map_map, Function.comp_def]
    rw [hl] at hm
    rw [← hm, List.map_map, List.map_map]
    rfl
  cases l <;> simp only [] <;> rw [← hs] <;> simp [er, List.map_drop, List.map_take]

theorem extendAB_er (f : Row → Row) (xs : ABag) : er (xs.map fun (r, es) => (f r, es)) = (er xs).map f := by
  simp [er, List.map_map, Function.comp_def]

end Tiramemsu.Prov
