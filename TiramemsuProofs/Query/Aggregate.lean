/-
Aggregates are functions of the multiset of their group (query-semantics "Machine-checked
order independence of aggregates"): every fold runs over the group's values in the canonical
value order, which is a linear order, so a permuted group gives the same value; and grouping
a permuted input gives a permuted output.
-/
import TiramemsuProofs.Query.Order

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[verification#Proven Query Semantics]]

/-- One aggregate depends only on the multiset of its group. -/
theorem aggregateOne_perm (f : AggFunc) (arg : Option RExpr) (d : Bool) {xs ys : Bag} (h : xs.Perm ys) :
    aggregateOne f arg d xs = aggregateOne f arg d ys := by
  unfold aggregateOne
  cases arg with
  | none => simp [h.length_eq]
  | some e =>
    simp only
    rw [sortValues_perm (h.filterMap _)]

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have : (as.filter fun b => !b == a).length < as.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ as)
    refine List.nodup_cons.2 ⟨?_, nodup_eraseDups _⟩
    rw [List.mem_eraseDups, List.mem_filter]
    simp
termination_by l => l.length

theorem eraseDups_perm {α : Type} [BEq α] [LawfulBEq α] {xs ys : List α} (h : xs.Perm ys) :
    xs.eraseDups.Perm ys.eraseDups :=
  (List.perm_ext_iff_of_nodup (nodup_eraseDups xs) (nodup_eraseDups ys)).2 fun a => by
    rw [List.mem_eraseDups, List.mem_eraseDups]; exact h.mem_iff

/-- The output row of one group. -/
def groupRow (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool))
    (kg : List (Option Value) × Bag) : Row :=
  aggs.foldl (fun (r : Row) (i, f, a, d) => r.set i (aggregateOne f a d kg.2))
    ((g.zip kg.1).foldl (fun (r : Row) (i, c) => r.set i c) (Row.empty n))

theorem groupRow_perm (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool))
    (k : List (Option Value)) {xs ys : Bag} (h : xs.Perm ys) : groupRow n g aggs (k, xs) = groupRow n g aggs (k, ys) := by
  unfold groupRow
  simp only
  generalize (g.zip k).foldl (fun (r : Row) (i, c) => r.set i c) (Row.empty n) = r0
  induction aggs generalizing r0 with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨i, f, arg, d⟩ := a
    simp only [List.foldl_cons]
    rw [aggregateOne_perm f arg d h, ih]

theorem aggregateB_eq (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool)) (xs : Bag) :
    aggregateB n g aggs xs =
      (if g.isEmpty && xs.isEmpty then [([], [])] else groupBy g xs).map (groupRow n g aggs) := rfl

/-- query-semantics: `Aggregate` maps permuted inputs to permuted outputs (each aggregate is a
function of its group's multiset). -/
theorem aggregateB_perm (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool))
    {xs ys : Bag} (h : xs.Perm ys) : (aggregateB n g aggs xs).Perm (aggregateB n g aggs ys) := by
  rw [aggregateB_eq, aggregateB_eq]
  have he : xs.isEmpty = ys.isEmpty := by
    cases xs <;> cases ys <;> simp_all [List.Perm.nil_eq, List.Perm.eq_nil] <;>
      first | exact absurd h.length_eq (by simp) | rfl
  rw [he]
  split
  · exact List.Perm.refl _
  · unfold groupBy
    simp only [List.map_map]
    have hk := eraseDups_perm (h.map (groupKey g))
    refine List.Perm.trans (List.Perm.of_eq ?_) (hk.map _)
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp]
    exact groupRow_perm n g aggs k (h.filter _)

end Tiramemsu.Sem
