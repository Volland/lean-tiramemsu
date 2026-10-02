/-
Rows as padded functions: `getD`-extensionality, merge and compatibility pointwise, and the
cell laws (symmetry, associativity, right commutativity) behind the join algebra.
-/
import Tiramemsu.Sem.Row
import Mathlib.Tactic

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[verification#Proven Query Semantics]]

/-- The cell of a row (unbound past its end). -/
def cell (r : Row) (i : Nat) : Option Value := r.getD i none

/-- The bit of a schema (false past its end). -/
def bit (P : Schema) (i : Nat) : Bool := P.getD i false

theorem getD_ext {α : Type} {d : α} : ∀ {l₁ l₂ : List α}, l₁.length = l₂.length →
    (∀ i, l₁.getD i d = l₂.getD i d) → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hl, h => by
    have h0 := h 0
    simp at h0
    rw [h0, getD_ext (l₁ := as) (l₂ := bs) (by simpa using hl) (fun i => by simpa using h (i + 1))]

theorem getD_eq_default {α : Type} {d : α} {l : List α} {i : Nat} (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

@[simp] theorem merge_length : ∀ (a b : Row), (merge a b).length = max a.length b.length
  | a :: as, b :: bs => by simp [merge, merge_length as bs, Nat.succ_max_succ]
  | [], bs => by simp [merge]
  | a :: as, [] => by simp [merge]

theorem merge_cell : ∀ (a b : Row) (i : Nat), cell (merge a b) i = (cell a i <|> cell b i)
  | a :: as, b :: bs, 0 => by simp [merge, cell]
  | a :: as, b :: bs, i + 1 => by simpa [merge, cell] using merge_cell as bs i
  | [], bs, i => by simp [merge, cell]
  | a :: as, [], i => by cases i <;> simp [merge, cell] <;> cases (as.getD _ none) <;> rfl

@[simp] theorem union_length : ∀ (P Q : Schema), (Schema.union P Q).length = max P.length Q.length
  | a :: as, b :: bs => by simp [Schema.union, union_length as bs, Nat.succ_max_succ]
  | [], bs => by simp [Schema.union]
  | a :: as, [] => by simp [Schema.union]

theorem union_bit : ∀ (P Q : Schema) (i : Nat), bit (Schema.union P Q) i = (bit P i || bit Q i)
  | a :: as, b :: bs, 0 => by simp [Schema.union, bit]
  | a :: as, b :: bs, i + 1 => by simpa [Schema.union, bit] using union_bit as bs i
  | [], bs, i => by simp [Schema.union, bit]
  | a :: as, [], i => by cases i <;> simp [Schema.union, bit]

theorem cellCompat_none_none (m : Missing) (p q : Bool) : cellCompat m p q none none = true ∨
    (m = .null3VL ∧ p = true ∧ q = true) := by
  cases m <;> cases p <;> cases q <;> simp [cellCompat]

theorem compat_iff {m : Missing} {P Q : Schema} {a b : Row} :
    compat m P Q a b = true ↔ ∀ i, cellCompat m (bit P i) (bit Q i) (cell a i) (cell b i) = true := by
  unfold compat
  rw [List.all_eq_true]
  constructor
  · intro h i
    by_cases hi : i < max (max P.length Q.length) (max a.length b.length)
    · exact h i (List.mem_range.2 hi)
    · push_neg at hi
      simp only [bit, cell]
      rw [getD_eq_default (by omega), getD_eq_default (by omega), getD_eq_default (by omega),
        getD_eq_default (by omega)]
      cases m <;> simp [cellCompat]
  · intro h i _
    exact h i

/-! ## Cell laws -/

theorem cell_symm (m : Missing) (p q : Bool) (a b : Option Value) :
    cellCompat m p q a b = cellCompat m q p b a := by
  cases a <;> cases b <;> simp [cellCompat, Bool.and_comm, eq_comm]

theorem cell_merge_comm {m : Missing} {p q : Bool} {a b : Option Value}
    (h : cellCompat m p q a b = true) : (a <|> b) = (b <|> a) := by
  cases a <;> cases b <;> simp_all [cellCompat]

theorem cell_assoc (m : Missing) (p q r : Bool) (a b c : Option Value) :
    (cellCompat m p q a b && cellCompat m (p || q) r (a <|> b) c) =
      (cellCompat m q r b c && cellCompat m p (q || r) a (b <|> c)) := by
  cases m <;> cases p <;> cases q <;> cases r <;> cases a <;> cases b <;> cases c <;>
    simp [cellCompat] <;> grind

theorem cell_rcomm (m : Missing) (p q r : Bool) (a b c : Option Value) :
    (cellCompat m p q a b && cellCompat m (p || q) r (a <|> b) c) =
      (cellCompat m p r a c && cellCompat m (p || r) q (a <|> c) b) := by
  cases m <;> cases p <;> cases q <;> cases r <;> cases a <;> cases b <;> cases c <;>
    simp [cellCompat] <;> grind

/-- Compatible cells of a three-way join make the second and third cells agree. -/
theorem cell_bc {m : Missing} {p q r : Bool} {a b c : Option Value}
    (h1 : cellCompat m p q a b = true) (h2 : cellCompat m (p || q) r (a <|> b) c = true) :
    (b <|> c) = (c <|> b) := by
  cases a <;> cases b <;> cases c <;> simp_all [cellCompat]

theorem and_split {x y u v : Bool} (e : (x && y) = (u && v)) (hx : x = true) (hy : y = true) :
    u = true ∧ v = true := by
  subst hx hy; cases u <;> cases v <;> simp_all

/-! ## Rows -/

theorem compat_symm (m : Missing) (P Q : Schema) (a b : Row) : compat m P Q a b = compat m Q P b a := by
  apply Bool.eq_iff_iff.2
  rw [compat_iff, compat_iff]
  exact forall_congr' fun i => by rw [cell_symm]

theorem merge_comm {m : Missing} {P Q : Schema} {a b : Row} (h : compat m P Q a b = true) :
    merge a b = merge b a := by
  apply getD_ext (d := none) (by simp [Nat.max_comm])
  intro i
  have := cell_merge_comm (compat_iff.1 h i)
  show cell _ i = cell _ i
  rw [merge_cell, merge_cell]; exact this

theorem merge_assoc (a b c : Row) : merge (merge a b) c = merge a (merge b c) := by
  apply getD_ext (d := none) (by simp [Nat.max_assoc])
  intro i
  show cell _ i = cell _ i
  simp only [merge_cell]
  cases cell a i <;> cases cell b i <;> rfl

theorem compat_assoc (m : Missing) (P Q R : Schema) (a b c : Row) :
    (compat m P Q a b && compat m (Schema.union P Q) R (merge a b) c) =
      (compat m Q R b c && compat m P (Schema.union Q R) a (merge b c)) := by
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, compat_iff, union_bit, merge_cell]
  constructor
  · rintro ⟨h1, h2⟩
    have e := fun i => cell_assoc m (bit P i) (bit Q i) (bit R i) (cell a i) (cell b i) (cell c i)
    exact ⟨fun i => (and_split (e i) (h1 i) (h2 i)).1, fun i => (and_split (e i) (h1 i) (h2 i)).2⟩
  · rintro ⟨h1, h2⟩
    have e := fun i => cell_assoc m (bit P i) (bit Q i) (bit R i) (cell a i) (cell b i) (cell c i)
    exact ⟨fun i => (and_split (e i).symm (h1 i) (h2 i)).1, fun i => (and_split (e i).symm (h1 i) (h2 i)).2⟩

theorem compat_rcomm (m : Missing) (P Q R : Schema) (a b c : Row) :
    (compat m P Q a b && compat m (Schema.union P Q) R (merge a b) c) =
      (compat m P R a c && compat m (Schema.union P R) Q (merge a c) b) := by
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, compat_iff, union_bit, merge_cell]
  constructor
  · rintro ⟨h1, h2⟩
    have e := fun i => cell_rcomm m (bit P i) (bit Q i) (bit R i) (cell a i) (cell b i) (cell c i)
    exact ⟨fun i => (and_split (e i) (h1 i) (h2 i)).1, fun i => (and_split (e i) (h1 i) (h2 i)).2⟩
  · rintro ⟨h1, h2⟩
    have e := fun i => cell_rcomm m (bit P i) (bit Q i) (bit R i) (cell a i) (cell b i) (cell c i)
    exact ⟨fun i => (and_split (e i).symm (h1 i) (h2 i)).1, fun i => (and_split (e i).symm (h1 i) (h2 i)).2⟩

theorem merge_rcomm {m : Missing} {P Q R : Schema} {a b c : Row} (h1 : compat m P Q a b = true)
    (h2 : compat m (Schema.union P Q) R (merge a b) c = true) :
    merge (merge a b) c = merge (merge a c) b := by
  rw [merge_assoc, merge_assoc]
  congr 1
  apply getD_ext (d := none) (by simp [Nat.max_comm])
  intro i
  have h2' := compat_iff.1 h2 i
  rw [union_bit, merge_cell] at h2'
  have := cell_bc (compat_iff.1 h1 i) h2'
  show cell _ i = cell _ i
  rw [merge_cell, merge_cell]; exact this

theorem compat_unit_left (m : Missing) (Q : Schema) (b : Row) : compat m [] Q [] b = true := by
  rw [compat_iff]; intro i
  have h1 : bit [] i = false := by simp [bit]
  have h2 : cell [] i = none := by simp [cell]
  rw [h1, h2]; cases m <;> cases cell b i <;> simp [cellCompat]

@[simp] theorem merge_nil_left (b : Row) : merge [] b = b := by simp [merge]
@[simp] theorem merge_nil_right (a : Row) : merge a [] = a := by cases a <;> simp [merge]
@[simp] theorem union_nil_left (Q : Schema) : Schema.union [] Q = Q := by simp [Schema.union]
@[simp] theorem union_nil_right (P : Schema) : Schema.union P [] = P := by cases P <;> simp [Schema.union]

theorem union_comm : ∀ (P Q : Schema), Schema.union P Q = Schema.union Q P
  | a :: as, b :: bs => by simp [Schema.union, union_comm as bs, Bool.or_comm]
  | [], bs => by simp
  | a :: as, [] => by simp

theorem union_assoc : ∀ (P Q R : Schema), Schema.union (Schema.union P Q) R = Schema.union P (Schema.union Q R)
  | a :: as, b :: bs, c :: cs => by simp [Schema.union, union_assoc as bs cs, Bool.or_assoc]
  | [], bs, cs => by simp
  | a :: as, [], cs => by simp
  | a :: as, b :: bs, [] => by simp

end Tiramemsu.Sem
