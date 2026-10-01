/-
Key order of the index families: a strict order, total on rows with distinct statement ids.
Requirement: store-contract / "The model store is exact and ordered".
-/
import Mathlib.Order.Basic
import Tiramemsu.Store.Order

namespace Tiramemsu.Store

--# @lat: [[verification#Proven Store Properties]]

/-! ## Comparison of optional integers -/

theorem cmpOpt_swap (a b : Option Int) : cmpOpt b a = (cmpOpt a b).swap := by
  cases a <;> cases b <;> simp only [cmpOpt, Ordering.swap]
  rw [← Int.compare_swap]; rfl

theorem cmpOpt_eq_iff {a b : Option Int} : cmpOpt a b = .eq ↔ a = b := by
  cases a <;> cases b <;> simp [cmpOpt]

theorem cmpOpt_lt_trans {a b c : Option Int} :
    cmpOpt a b = .lt → cmpOpt b c = .lt → cmpOpt a c = .lt := by
  intro h₁ h₂
  match a, b, c, h₁, h₂ with
  | none, some _, some _, _, _ => rfl
  | some x, some y, some z, h₁, h₂ =>
    simp only [cmpOpt] at h₁ h₂ ⊢
    exact Int.compare_eq_lt.2 (Int.lt_trans (Int.compare_eq_lt.1 h₁) (Int.compare_eq_lt.1 h₂))

/-! ## Lexicographic comparison of keys -/

theorem cmpKey_swap : ∀ (a b : List (Option Int)), cmpKey b a = (cmpKey a b).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [cmpKey]
    rw [cmpOpt_swap x y]
    cases h : cmpOpt x y <;> simp [Ordering.swap, cmpKey_swap xs ys]

theorem cmpKey_eq_iff : ∀ {a b : List (Option Int)}, cmpKey a b = .eq ↔ a = b
  | [], [] => by simp [cmpKey]
  | [], _ :: _ => by simp [cmpKey]
  | _ :: _, [] => by simp [cmpKey]
  | x :: xs, y :: ys => by
    simp only [cmpKey, List.cons.injEq]
    cases h : cmpOpt x y with
    | eq => simp [cmpOpt_eq_iff.1 h, cmpKey_eq_iff]
    | lt =>
      have : x ≠ y := fun e => by rw [e, cmpOpt_eq_iff.2 rfl] at h; cases h
      simp [this]
    | gt =>
      have : x ≠ y := fun e => by rw [e, cmpOpt_eq_iff.2 rfl] at h; cases h
      simp [this]

theorem cmpKey_refl (a : List (Option Int)) : cmpKey a a = .eq := cmpKey_eq_iff.2 rfl

theorem cmpKey_cons_lt_iff {x y : Option Int} {xs ys : List (Option Int)} :
    cmpKey (x :: xs) (y :: ys) = .lt ↔ cmpOpt x y = .lt ∨ (x = y ∧ cmpKey xs ys = .lt) := by
  simp only [cmpKey]
  cases h : cmpOpt x y with
  | lt => simp
  | eq => simp [cmpOpt_eq_iff.1 h]
  | gt =>
    have : x ≠ y := by rintro rfl; rw [cmpOpt_eq_iff.2 rfl] at h; cases h
    simp [this]

theorem cmpKey_lt_trans : ∀ {a b c : List (Option Int)},
    cmpKey a b = .lt → cmpKey b c = .lt → cmpKey a c = .lt
  | [], [], _, h, _ => by simp [cmpKey] at h
  | [], _ :: _, [], _, h => by simp [cmpKey] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [cmpKey] at h
  | _ :: _, _ :: _, [], _, h => by simp [cmpKey] at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    rw [cmpKey_cons_lt_iff] at h₁ h₂ ⊢
    rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
    · exact Or.inl (cmpOpt_lt_trans h₁ h₂)
    · exact Or.inl h₁
    · exact Or.inl h₂
    · exact Or.inr ⟨rfl, cmpKey_lt_trans h₁ h₂⟩

/-! ## Family keys -/

/-- The key of a row, split into the columns before `eid` and the `eid` itself. -/
def keyInit (f : Family) (r : TripleRow) : List (Option Int) :=
  (f.cols.dropLast).map fun (c, d) => keyComp d (c.get r)

theorem cols_split (f : Family) : f.cols = f.cols.dropLast ++ [(.eid, false)] := by
  cases f <;> simp [Family.cols, Family.perm]

theorem keyOf_split (f : Family) (r : TripleRow) :
    keyOf f r = keyInit f r ++ [some r.eid.toInt] := by
  unfold keyOf keyInit
  conv => lhs; rw [cols_split f]
  simp [keyComp, Col.get]

theorem keyOf_inj {f : Family} {a b : TripleRow} (h : keyOf f a = keyOf f b) : a.eid = b.eid := by
  rw [keyOf_split, keyOf_split] at h
  have h' : [some a.eid.toInt] = [some b.eid.toInt] := (List.append_inj' h (by simp)).2
  simp only [List.cons.injEq, Option.some.injEq, and_true] at h'
  exact Int64.toInt_inj.1 h'

theorem keyCmp_swap (f : Family) (a b : TripleRow) : keyCmp f b a = (keyCmp f a b).swap :=
  cmpKey_swap _ _

theorem keyCmp_self (f : Family) (a : TripleRow) : keyCmp f a a = .eq := cmpKey_refl _

theorem keyLt_irrefl (f : Family) (a : TripleRow) : ¬ keyLt f a a := by
  simp [keyLt, keyCmp_self]

theorem keyLt_trans (f : Family) {a b c : TripleRow} :
    keyLt f a b → keyLt f b c → keyLt f a c :=
  cmpKey_lt_trans

/-- The key order of every family is a strict order. -/
theorem keyLt_strictOrder (f : Family) : IsStrictOrder TripleRow (keyLt f) where
  irrefl := keyLt_irrefl f
  trans _ _ _ := keyLt_trans f

/-- Rows with distinct statement ids are comparable: the key order is total on them. -/
theorem keyLt_total (f : Family) {a b : TripleRow} (h : a.eid ≠ b.eid) :
    keyLt f a b ∨ keyLt f b a := by
  unfold keyLt
  rw [keyCmp_swap f a b]
  cases hc : keyCmp f a b with
  | lt => exact Or.inl rfl
  | gt => exact Or.inr rfl
  | eq => exact absurd (keyOf_inj (cmpKey_eq_iff.1 hc)) h

/-- `keyLe` is the reflexive closure of `keyLt` on keys. -/
theorem keyLe_iff (f : Family) (a b : TripleRow) :
    keyLe f a b = true ↔ keyCmp f a b = .lt ∨ keyCmp f a b = .eq := by
  unfold keyLe
  cases keyCmp f a b <;> simp

theorem keyLe_trans (f : Family) (a b c : TripleRow) :
    keyLe f a b = true → keyLe f b c = true → keyLe f a c = true := by
  simp only [keyLe_iff]
  rintro (h₁ | h₁) (h₂ | h₂)
  · exact Or.inl (cmpKey_lt_trans h₁ h₂)
  · rw [keyCmp, cmpKey_eq_iff] at h₂; rw [keyCmp, ← h₂]; exact Or.inl h₁
  · rw [keyCmp, cmpKey_eq_iff] at h₁; rw [keyCmp, h₁]; exact Or.inl h₂
  · rw [keyCmp, cmpKey_eq_iff] at h₁ h₂; rw [keyCmp, h₁, h₂]; exact Or.inr (cmpKey_refl _)

theorem keyLe_total (f : Family) (a b : TripleRow) : (keyLe f a b || keyLe f b a) = true := by
  simp only [Bool.or_eq_true, keyLe_iff]
  rw [keyCmp_swap f a b]
  cases keyCmp f a b <;> simp [Ordering.swap]

/-- A non-strict key comparison between rows with distinct ids is strict. -/
theorem keyLt_of_keyLe (f : Family) {a b : TripleRow} (hle : keyLe f a b = true)
    (h : a.eid ≠ b.eid) : keyLt f a b := by
  rcases (keyLe_iff f a b).1 hle with h' | h'
  · exact h'
  · exact absurd (keyOf_inj (cmpKey_eq_iff.1 h')) h

end Tiramemsu.Store
