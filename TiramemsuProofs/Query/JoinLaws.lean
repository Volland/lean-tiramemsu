/-
The join algebra (query-semantics "Relational operators"): the binary bag join is commutative,
associative and has the unit relation as unit, each up to permutation of the bag; hence the
n-ary join (a left fold) is invariant under permutation of its inputs. The schema of a join is
the union of its inputs' schemas, so it is invariant too.
-/
import TiramemsuProofs.Query.Rows

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[verification#Proven Query Semantics]]

/-- Equal schemas and permuted bags. -/
def SRel (a b : SBag) : Prop := a.1 = b.1 ∧ a.2.Perm b.2

theorem SRel.refl (a : SBag) : SRel a a := ⟨rfl, List.Perm.refl _⟩
theorem SRel.symm {a b : SBag} (h : SRel a b) : SRel b a := ⟨h.1.symm, h.2.symm⟩
theorem SRel.trans {a b c : SBag} (h1 : SRel a b) (h2 : SRel b c) : SRel a c := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-! ## Lists -/

theorem filterMap_eq_flatMap {α β : Type} (f : α → Option β) (xs : List α) :
    xs.filterMap f = xs.flatMap fun a => (f a).toList := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [List.filterMap_cons, h, ih]

theorem flatMap_append_perm {α β : Type} (xs : List α) (F G : α → List β) :
    (xs.flatMap fun a => F a ++ G a).Perm (xs.flatMap F ++ xs.flatMap G) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left _ ?_
    refine (List.Perm.append_left _ ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

theorem flatMap_swap {α β γ : Type} (xs : List α) (ys : List β) (F : α → β → List γ) :
    (xs.flatMap fun a => ys.flatMap (F a)).Perm (ys.flatMap fun b => xs.flatMap fun a => F a b) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    refine (List.Perm.append_left _ ih).trans ?_
    exact (flatMap_append_perm ys (F x) (fun b => xs.flatMap fun a => F a b)).symm

theorem flatMap_congr {α β : Type} {xs : List α} {F G : α → List β} (h : ∀ a ∈ xs, F a = G a) :
    xs.flatMap F = xs.flatMap G := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem flatMap_perm_congr {α β : Type} {xs : List α} {F G : α → List β} (h : ∀ a ∈ xs, (F a).Perm (G a)) :
    (xs.flatMap F).Perm (xs.flatMap G) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact List.Perm.append (h x (List.mem_cons_self ..)) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

/-! ## The binary join -/

/-- The joined rows of one pair. -/
def jcell (m : Missing) (P Q : Schema) (a b : Row) : List Row := if compat m P Q a b then [merge a b] else []

theorem joinB_eq (m : Missing) (P Q : Schema) (xs ys : Bag) :
    joinB m P Q xs ys = xs.flatMap fun a => ys.flatMap fun b => jcell m P Q a b := by
  unfold joinB
  congr 1; funext a
  rw [filterMap_eq_flatMap]
  congr 1; funext b
  unfold jcell; split <;> rfl

theorem joinB_perm_left {m : Missing} {P Q : Schema} {xs xs' : Bag} (ys : Bag) (h : xs.Perm xs') :
    (joinB m P Q xs ys).Perm (joinB m P Q xs' ys) := by
  rw [joinB_eq, joinB_eq]; exact h.flatMap_right _

theorem joinB_perm_right {m : Missing} {P Q : Schema} (xs : Bag) {ys ys' : Bag} (h : ys.Perm ys') :
    (joinB m P Q xs ys).Perm (joinB m P Q xs ys') := by
  rw [joinB_eq, joinB_eq]
  exact flatMap_perm_congr fun a _ => h.flatMap_right _

/-- Commutativity. -/
theorem joinB_comm (m : Missing) (P Q : Schema) (xs ys : Bag) :
    (joinB m P Q xs ys).Perm (joinB m Q P ys xs) := by
  rw [joinB_eq, joinB_eq]
  refine (flatMap_swap xs ys _).trans (List.Perm.of_eq ?_)
  refine flatMap_congr fun b _ => flatMap_congr fun a _ => ?_
  unfold jcell
  rw [compat_symm m P Q a b]
  split
  · rename_i h; rw [merge_comm h]
  · rfl

theorem joinSB_comm (m : Missing) (x y : SBag) : SRel (joinSB m x y) (joinSB m y x) :=
  ⟨union_comm _ _, joinB_comm m _ _ _ _⟩

theorem jcell_bind_assoc (m : Missing) (P Q R : Schema) (a b c : Row) :
    ((jcell m P Q a b).flatMap fun r => jcell m (Schema.union P Q) R r c) =
      ((jcell m Q R b c).flatMap fun r => jcell m P (Schema.union Q R) a r) := by
  have e := compat_assoc m P Q R a b c
  unfold jcell
  by_cases h1 : compat m P Q a b = true <;> by_cases h2 : compat m (Schema.union P Q) R (merge a b) c = true <;>
    by_cases h3 : compat m Q R b c = true <;> by_cases h4 : compat m P (Schema.union Q R) a (merge b c) = true <;>
    simp_all [merge_assoc]

/-- A singleton or empty bag commutes with a flat map. -/
theorem jcell_out (m : Missing) (P Q : Schema) (a b : Row) (zs : Bag) (G : Row → Row → List Row) :
    ((jcell m P Q a b).flatMap fun r => zs.flatMap (G r)) =
      zs.flatMap fun c => (jcell m P Q a b).flatMap fun r => G r c := by
  unfold jcell
  split
  · simp
  · simp

/-- Associativity (as lists, hence as bags). -/
theorem joinB_assoc (m : Missing) (P Q R : Schema) (xs ys zs : Bag) :
    joinB m (Schema.union P Q) R (joinB m P Q xs ys) zs = joinB m P (Schema.union Q R) xs (joinB m Q R ys zs) := by
  simp only [joinB_eq, List.flatMap_assoc]
  refine flatMap_congr fun a _ => flatMap_congr fun b _ => ?_
  rw [jcell_out]
  exact flatMap_congr fun c _ => jcell_bind_assoc m P Q R a b c

theorem joinSB_assoc (m : Missing) (x y z : SBag) :
    SRel (joinSB m (joinSB m x y) z) (joinSB m x (joinSB m y z)) :=
  ⟨union_assoc _ _ _, List.Perm.of_eq (joinB_assoc m _ _ _ _ _ _)⟩

theorem jcell_bind_rcomm (m : Missing) (P Q R : Schema) (a b c : Row) :
    ((jcell m P Q a b).flatMap fun r => jcell m (Schema.union P Q) R r c) =
      ((jcell m P R a c).flatMap fun r => jcell m (Schema.union P R) Q r b) := by
  have e := compat_rcomm m P Q R a b c
  unfold jcell
  by_cases h1 : compat m P Q a b = true <;> by_cases h2 : compat m (Schema.union P Q) R (merge a b) c = true
  · have hm := merge_rcomm h1 h2
    by_cases h3 : compat m P R a c = true <;> by_cases h4 : compat m (Schema.union P R) Q (merge a c) b = true <;>
      simp_all
  all_goals
    by_cases h3 : compat m P R a c = true <;> by_cases h4 : compat m (Schema.union P R) Q (merge a c) b = true <;>
      simp_all

/-- Right commutativity: the order of the last two inputs of a fold does not matter. -/
theorem joinSB_rcomm (m : Missing) (a x y : SBag) :
    SRel (joinSB m (joinSB m a x) y) (joinSB m (joinSB m a y) x) := by
  refine ⟨by simp only [joinSB]; rw [union_assoc, union_comm x.1, ← union_assoc], ?_⟩
  simp only [joinSB, joinB_eq, List.flatMap_assoc]
  refine flatMap_perm_congr fun r _ => ?_
  simp only [jcell_out]
  refine (flatMap_swap _ _ _).trans (List.Perm.of_eq ?_)
  exact flatMap_congr fun c _ => flatMap_congr fun b _ => jcell_bind_rcomm m _ _ _ r b c

theorem joinSB_congr (m : Missing) {a a' : SBag} (x : SBag) (h : SRel a a') :
    SRel (joinSB m a x) (joinSB m a' x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [joinSB, h1], ?_⟩
  simp only [joinSB, h1]
  exact joinB_perm_left _ h2

theorem joinSB_congr_right (m : Missing) (a : SBag) {x x' : SBag} (h : SRel x x') :
    SRel (joinSB m a x) (joinSB m a x') := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [joinSB, h1], ?_⟩
  simp only [joinSB, h1]
  exact joinB_perm_right _ h2

theorem foldl_congr (m : Missing) (xs : List SBag) : ∀ {a a' : SBag}, SRel a a' →
    SRel (xs.foldl (joinSB m) a) (xs.foldl (joinSB m) a') := by
  induction xs with
  | nil => intro a a' h; exact h
  | cons x xs ih => intro a a' h; exact ih (joinSB_congr m x h)

theorem foldl_perm (m : Missing) {xs ys : List SBag} (h : xs.Perm ys) :
    ∀ a : SBag, SRel (xs.foldl (joinSB m) a) (ys.foldl (joinSB m) a) := by
  induction h with
  | nil => intro a; exact SRel.refl _
  | cons x _ ih => intro a; exact ih _
  | swap x y l => intro a; exact foldl_congr m l (joinSB_rcomm m a y x)
  | trans _ _ ih1 ih2 => intro a; exact (ih1 a).trans (ih2 a)

/-- The n-ary join is invariant under permutation of its inputs. -/
theorem joinAll_perm (m : Missing) (n : Nat) {xs ys : List SBag} (h : xs.Perm ys) :
    SRel (joinAll m n xs) (joinAll m n ys) := foldl_perm m h _

/-- The unit relation is a left unit. -/
theorem joinSB_unit_left (m : Missing) (n : Nat) (x : SBag) : SRel (joinSB m (unitSB n) x) x := by
  refine ⟨by simp [joinSB, unitSB], List.Perm.of_eq ?_⟩
  simp only [joinSB, unitSB, joinB_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  conv => rhs; rw [← List.flatMap_singleton' x.2]
  refine flatMap_congr fun b _ => ?_
  simp [jcell, compat_unit_left]

theorem compat_unit_right (m : Missing) (P : Schema) (a : Row) : compat m P [] a [] = true := by
  rw [compat_symm]; exact compat_unit_left m P a

/-- The unit relation is a right unit. -/
theorem joinSB_unit_right (m : Missing) (n : Nat) (x : SBag) : SRel (joinSB m x (unitSB n)) x := by
  refine ⟨by simp [joinSB, unitSB], List.Perm.of_eq ?_⟩
  simp only [joinSB, unitSB, joinB_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  conv => rhs; rw [← List.flatMap_singleton' x.2]
  refine flatMap_congr fun a _ => ?_
  simp [jcell, compat_unit_right]

/-- Joining two folds: the fold over a concatenation is the join of the two folds. -/
theorem joinAll_append (m : Missing) (n : Nat) (xs ys : List SBag) :
    SRel (joinAll m n (xs ++ ys)) (joinSB m (joinAll m n xs) (joinAll m n ys)) := by
  unfold joinAll
  rw [List.foldl_append]
  generalize xs.foldl (joinSB m) (unitSB n) = a
  induction ys using List.reverseRecOn generalizing a with
  | nil => exact (joinSB_unit_right m n a).symm
  | append_singleton ys y ih =>
    rw [List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact (joinSB_congr m y (ih a)).trans ((joinSB_assoc m _ _ _))

end Tiramemsu.Sem
