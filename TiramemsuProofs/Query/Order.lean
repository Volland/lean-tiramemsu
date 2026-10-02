/-
The canonical value order is a linear order: lexicographic comparison of natural-number lists
is total, transitive and antisymmetric, and the canonical key of a value is injective (the
sort key and the total key are both written self-delimiting). Sorting is therefore a function
of the multiset: permuted inputs sort to equal lists.
-/
import Tiramemsu.Sem.Ops
import Mathlib.Tactic

namespace Tiramemsu.Sem

open Tiramemsu.Codec

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Lexicographic order on natural lists -/

theorem cmpNats_swap : ∀ (a b : List Nat), cmpNats b a = (cmpNats a b).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [cmpNats]
    by_cases h1 : x < y
    · have : ¬ y < x := by omega
      simp [h1, this, Ordering.swap]
    · by_cases h2 : y < x
      · simp [h1, h2, Ordering.swap]
      · simp [h1, h2, cmpNats_swap xs ys]

theorem cmpNats_eq_iff : ∀ (a b : List Nat), cmpNats a b = .eq ↔ a = b
  | [], [] => by simp [cmpNats]
  | [], _ :: _ => by simp [cmpNats]
  | _ :: _, [] => by simp [cmpNats]
  | x :: xs, y :: ys => by
    simp only [cmpNats]
    by_cases h1 : x < y
    · simp [h1]; all_goals omega
    · by_cases h2 : y < x
      · simp [h1, h2]; all_goals omega
      · have : x = y := by omega
        subst this; simp [cmpNats_eq_iff xs ys]

theorem cmpNats_trans : ∀ (a b c : List Nat), cmpNats a b ≠ .gt → cmpNats b c ≠ .gt → cmpNats a c ≠ .gt
  | [], _, [] => by simp [cmpNats]
  | [], _, _ :: _ => by simp [cmpNats]
  | _ :: _, [], _ => by simp [cmpNats]
  | _ :: _, _ :: _, [] => by simp [cmpNats]
  | x :: xs, y :: ys, z :: zs => by
    simp only [cmpNats]
    intro h1 h2
    by_cases a1 : x < y <;> by_cases a2 : y < x <;> by_cases b1 : y < z <;> by_cases b2 : z < y <;>
      simp only [a1, a2, b1, b2, if_true, if_false, ne_eq, reduceCtorEq, not_false_eq_true,
        not_true_eq_false] at h1 h2 ⊢ <;>
      first
      | (have : x < z := by omega
         simp [this])
      | (have : x = y := by omega
         have : y = z := by omega
         subst_vars
         simp [cmpNats_trans xs ys zs h1 h2])
      | (have : x = y := by omega
         subst_vars
         simp [b1, b2])
      | (have : y = z := by omega
         subst_vars
         simp [a1, a2])
      | omega

theorem cmpNats_total (a b : List Nat) : cmpNats a b ≠ .gt ∨ cmpNats b a ≠ .gt := by
  rw [cmpNats_swap a b]
  cases cmpNats a b <;> simp [Ordering.swap]

/-! ## Injectivity of the canonical key -/

theorem encNats_append_inj : ∀ {l₁ l₂ r₁ r₂ : List Nat}, encNats l₁ ++ r₁ = encNats l₂ ++ r₂ → l₁ = l₂ ∧ r₁ = r₂
  | [], [], r₁, r₂, h => by simpa [encNats] using h
  | [], b :: bs, r₁, r₂, h => by simp [encNats] at h
  | a :: as, [], r₁, r₂, h => by simp [encNats] at h
  | a :: as, b :: bs, r₁, r₂, h => by
    simp only [encNats, List.map_cons, List.cons_append, List.cons.injEq, Nat.add_right_cancel_iff] at h
    obtain ⟨rfl, h⟩ := h
    have := encNats_append_inj (l₁ := as) (l₂ := bs) (r₁ := r₁) (r₂ := r₂) (by simpa [encNats] using h)
    exact ⟨by rw [this.1], this.2⟩

theorem charsKey_length (s : String) : (charsKey s).length = s.length := by
  simp [charsKey, String.length]

theorem charsKey_inj {s t : String} (h : charsKey s = charsKey t) : s = t := by
  have hinj : Function.Injective Char.toNat := fun a b hab => Char.ext (UInt32.toNat_inj.1 hab)
  have : s.toList = t.toList := (List.map_injective_iff.2 hinj) h
  exact String.toList_inj.1 this

theorem strTKey_append_inj {s t : String} {r₁ r₂ : List Nat} (h : strTKey s ++ r₁ = strTKey t ++ r₂) :
    s = t ∧ r₁ = r₂ := by
  simp only [strTKey, List.cons_append, List.cons.injEq] at h
  obtain ⟨hl, h⟩ := h
  have hlen : (charsKey s).length = (charsKey t).length := by rw [charsKey_length, charsKey_length, hl]
  have := List.append_inj h hlen
  exact ⟨charsKey_inj this.1, this.2⟩

theorem zig_inj {a b : Int} (h : zig a = zig b) : a = b := by
  unfold zig at h; split_ifs at h <;> omega

theorem tzKey_inj {t1 t2 : Option Int}
    (h : (match t1 with | none => 0 | some z => zig z + 1) = (match t2 with | none => 0 | some z => zig z + 1)) :
    t1 = t2 := by
  cases t1 <;> cases t2 <;> simp at h
  · rfl
  · rw [zig_inj h]

theorem totalKey_inj {a b : Value} (h : totalKey a = totalKey b) : a = b := by
  cases a <;> cases b <;> simp only [totalKey, strTKey, List.cons_append, List.cons.injEq] at h <;>
    (try omega) <;> (try (simp at h; done))
  all_goals first
    | (obtain ⟨-, h1, h2⟩ := h
       have e := List.append_inj h2 (by rw [charsKey_length, charsKey_length, h1])
       simp only [List.cons.injEq] at e
       rw [charsKey_inj e.1, charsKey_inj e.2.2])
    | (obtain ⟨-, -, h2⟩ := h; rw [charsKey_inj h2])
    | (obtain ⟨-, h1, -⟩ := h; rw [zig_inj h1]; done)
    | (obtain ⟨-, h1, h2, -⟩ := h
       rw [zig_inj h1, tzKey_inj h2])
    | (obtain ⟨-, h1, -⟩ := h; rw [h1]; done)
    | (obtain ⟨-, h1, -⟩ := h; rename_i x y; cases x; cases y; simp_all [UInt64.toNat_inj]; done)
    | (obtain ⟨-, h1, -⟩ := h; rename_i x y; cases x <;> cases y <;> simp_all)

theorem cellKey_inj {a b : Value} (h : cellKey (some a) = cellKey (some b)) : a = b := by
  simp only [cellKey, List.cons.injEq, true_and] at h
  exact totalKey_inj (encNats_append_inj (r₁ := []) (r₂ := []) (by simpa using (encNats_append_inj h).2)).1

/-! ## The canonical value order -/

/-- The canonical value order as a boolean comparator. -/
def valueLe (a b : Value) : Bool := cmpValue a b != .gt

theorem valueLe_total (a b : Value) : valueLe a b || valueLe b a := by
  unfold valueLe cmpValue
  rcases cmpNats_total (cellKey (some a)) (cellKey (some b)) with h | h <;> simp [h]

theorem valueLe_trans (a b c : Value) : valueLe a b → valueLe b c → valueLe a c := by
  unfold valueLe cmpValue
  simp only [bne_iff_ne, ne_eq]
  exact cmpNats_trans _ _ _

theorem valueLe_antisymm (a b : Value) : valueLe a b → valueLe b a → a = b := by
  unfold valueLe cmpValue
  simp only [bne_iff_ne, ne_eq]
  intro h1 h2
  rw [cmpNats_swap] at h2
  have : cmpNats (cellKey (some a)) (cellKey (some b)) = .eq := by
    cases h : cmpNats (cellKey (some a)) (cellKey (some b)) <;> simp_all [Ordering.swap]
  exact cellKey_inj ((cmpNats_eq_iff _ _).1 this)

/-- Sorting in a linear order is a function of the multiset. -/
theorem mergeSort_perm_eq {α : Type} (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (antisymm : ∀ a b, le a b → le b a → a = b)
    {xs ys : List α} (h : xs.Perm ys) : xs.mergeSort le = ys.mergeSort le := by
  apply List.Perm.eq_of_pairwise (le := fun a b => le a b = true)
  · intro a b _ _ h1 h2; exact antisymm a b h1 h2
  · exact List.pairwise_mergeSort trans total xs
  · exact List.pairwise_mergeSort trans total ys
  · exact (List.mergeSort_perm xs le).trans (h.trans (List.mergeSort_perm ys le).symm)

theorem sortValues_perm {xs ys : List Value} (h : xs.Perm ys) : sortValues xs = sortValues ys :=
  mergeSort_perm_eq valueLe valueLe_trans valueLe_total valueLe_antisymm h

end Tiramemsu.Sem
