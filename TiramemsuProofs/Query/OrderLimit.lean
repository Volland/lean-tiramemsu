/-
`OrderLimit` is a function of the multiset of its input: the order of `ORDER BY` (keys
compared lexicographically, each ascending or descending, missing values placed by the
semantics) refined by the canonical row order is a linear order, because the canonical row key
is injective; so permuted inputs sort, skip and limit to equal lists.
-/
import TiramemsuProofs.Query.Order

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[verification#Proven Query Semantics]]

/-! ## Byte lists as natural lists -/

theorem cmpBytes_eq_cmpNats : ∀ (a b : List UInt8), cmpBytes a b = cmpNats (a.map UInt8.toNat) (b.map UInt8.toNat)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [cmpBytes, cmpNats, List.map_cons]
    have h1 : (x < y) ↔ (x.toNat < y.toNat) := UInt8.lt_iff_toNat_lt
    have h2 : (y < x) ↔ (y.toNat < x.toNat) := UInt8.lt_iff_toNat_lt
    by_cases a1 : x < y
    · rw [if_pos a1, if_pos (h1.1 a1)]
    · rw [if_neg a1, if_neg (fun h => a1 (h1.2 h))]
      by_cases a2 : y < x
      · rw [if_pos a2, if_pos (h2.1 a2)]
      · rw [if_neg a2, if_neg (fun h => a2 (h2.2 h))]
        exact cmpBytes_eq_cmpNats xs ys

/-! ## Key cells -/

/-- An encoding of a key cell whose natural-list order is the cell order. -/
def cellEnc (m : Missing) : Option Value → List Nat
  | none => if m == .unbound then [0] else [2]
  | some v => 1 :: (sortKey v).map UInt8.toNat

theorem cmpKeyCell_eq (m : Missing) (a b : Option Value) : cmpKeyCell m a b = cmpNats (cellEnc m a) (cellEnc m b) := by
  cases a <;> cases b <;> cases m <;> simp [cmpKeyCell, cellEnc, cmpNats, cmpBytes_eq_cmpNats]

/-- One key component, with its direction. -/
def compK (m : Missing) (d : Bool) (a b : Option Value) : Ordering :=
  if d then (cmpNats (cellEnc m a) (cellEnc m b)).swap else cmpNats (cellEnc m a) (cellEnc m b)

theorem compK_swap (m : Missing) (d : Bool) (a b : Option Value) : compK m d b a = (compK m d a b).swap := by
  unfold compK; cases d <;> simp [cmpNats_swap (cellEnc m a)]

theorem compK_eq {m : Missing} {d : Bool} {a b : Option Value} : compK m d a b = .eq ↔ cellEnc m a = cellEnc m b := by
  unfold compK
  rw [← cmpNats_eq_iff]
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    cases cmpNats (cellEnc m a) (cellEnc m b) <;> simp [Ordering.swap]

theorem compK_trans {m : Missing} {d : Bool} {a b c : Option Value} :
    compK m d a b ≠ .gt → compK m d b c ≠ .gt → compK m d a c ≠ .gt := by
  unfold compK
  cases d
  · exact cmpNats_trans _ _ _
  · simp only [ite_true]
    intro h1 h2
    have g1 : cmpNats (cellEnc m b) (cellEnc m a) ≠ .gt := by
      rw [cmpNats_swap]; revert h1; cases cmpNats (cellEnc m a) (cellEnc m b) <;> simp [Ordering.swap]
    have g2 : cmpNats (cellEnc m c) (cellEnc m b) ≠ .gt := by
      rw [cmpNats_swap]; revert h2; cases cmpNats (cellEnc m b) (cellEnc m c) <;> simp [Ordering.swap]
    have := cmpNats_trans _ _ _ g2 g1
    rw [cmpNats_swap] at this; revert this; cases cmpNats (cellEnc m a) (cellEnc m c) <;> simp [Ordering.swap]

theorem cmpKeys_cons (m : Missing) (d : Bool) (ds : List Bool) (a : Option Value) (as : List (Option Value))
    (b : Option Value) (bs : List (Option Value)) :
    cmpKeys m (d :: ds) (a :: as) (b :: bs) = match compK m d a b with
      | .eq => cmpKeys m ds as bs
      | o => o := by
  simp only [cmpKeys, cmpKeyCell_eq, compK]
  cases d <;> cases cmpNats (cellEnc m a) (cellEnc m b) <;> rfl

/-! ## Key vectors -/

theorem cmpKeys_swap (m : Missing) : ∀ (ds : List Bool) (as bs : List (Option Value)),
    cmpKeys m ds bs as = (cmpKeys m ds as bs).swap
  | d :: ds, a :: as, b :: bs => by
    rw [cmpKeys_cons, cmpKeys_cons, compK_swap m d a b]
    cases h : compK m d a b <;> simp [Ordering.swap, cmpKeys_swap m ds as bs]
  | [], _, _ => by simp [cmpKeys, Ordering.swap]
  | _ :: _, [], _ => by cases ‹List (Option Value)› <;> simp [cmpKeys, Ordering.swap]
  | _ :: _, _ :: _, [] => by simp [cmpKeys, Ordering.swap]

theorem compK_congr_left {m : Missing} {d : Bool} {a c : Option Value} (h : cellEnc m a = cellEnc m c)
    (b : Option Value) : compK m d a b = compK m d c b := by
  unfold compK; rw [h]

theorem cmpKeys_trans (m : Missing) : ∀ (ds : List Bool) (as bs cs : List (Option Value)),
    as.length = ds.length → bs.length = ds.length → cs.length = ds.length →
    cmpKeys m ds as bs ≠ .gt → cmpKeys m ds bs cs ≠ .gt → cmpKeys m ds as cs ≠ .gt
  | [], _, _, _, _, _, _, _, _ => by simp [cmpKeys]
  | d :: ds, a :: as, b :: bs, c :: cs, la, lb, lc, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at la lb lc
    rw [cmpKeys_cons] at h1 h2 ⊢
    have hx : compK m d a b ≠ .gt := by intro h; rw [h] at h1; exact h1 rfl
    have hy : compK m d b c ≠ .gt := by intro h; rw [h] at h2; exact h2 rfl
    have hz := compK_trans hx hy
    cases hzc : compK m d a c with
    | lt => simp
    | gt => exact absurd hzc hz
    | eq =>
      simp only
      have he := compK_eq.1 hzc
      have hxy : compK m d a b = (compK m d b c).swap := by
        rw [compK_congr_left he, compK_swap]
      have hyeq : compK m d b c = .eq := by
        cases h : compK m d b c with
        | eq => rfl
        | gt => exact absurd h hy
        | lt => exfalso; apply hx; rw [hxy, h]; rfl
      have hxeq : compK m d a b = .eq := by rw [hxy, hyeq]; rfl
      rw [hxeq] at h1; rw [hyeq] at h2
      exact cmpKeys_trans m ds as bs cs la lb lc h1 h2
  | _ :: _, [], _, _, la, _, _, _, _ => by simp at la
  | _ :: _, _ :: _, [], _, _, lb, _, _, _ => by simp at lb
  | _ :: _, _ :: _, _ :: _, [], _, _, lc, _, _ => by simp at lc

/-! ## The order of `OrderLimit` -/

theorem rowKey_inj : ∀ {a b : Row}, rowKey a = rowKey b → a = b
  | [], [], _ => rfl
  | [], x :: xs, h => by
    cases x <;> simp [rowKey, cellKey] at h
  | x :: xs, [], h => by
    cases x <;> simp [rowKey, cellKey] at h
  | x :: xs, y :: ys, h => by
    simp only [rowKey, List.flatMap_cons] at h
    cases x <;> cases y <;> simp only [cellKey, List.cons_append, List.cons.injEq] at h
    · rw [rowKey_inj h.2]
    · omega
    · omega
    · next u w =>
      rw [List.append_assoc, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := encNats_append_inj h.2
      obtain ⟨h3, h4⟩ := encNats_append_inj h2
      have : u = w := cellKey_inj (by simp [cellKey, h1, h3])
      rw [this, rowKey_inj h4]

theorem rowLe_antisymm {a b : Row} (h1 : rowLe a b = true) (h2 : rowLe b a = true) : a = b := by
  unfold rowLe at h1 h2
  simp only [bne_iff_ne, ne_eq] at h1 h2
  have : cmpNats (rowKey a) (rowKey b) = .eq := by
    rw [cmpNats_swap] at h2
    cases h : cmpNats (rowKey a) (rowKey b) <;> simp_all [Ordering.swap]
  exact rowKey_inj ((cmpNats_eq_iff _ _).1 this)

theorem rowLe_total (a b : Row) : rowLe a b || rowLe b a := by
  unfold rowLe
  rcases cmpNats_total (rowKey a) (rowKey b) with h | h <;> simp [h]

theorem rowLe_trans {a b c : Row} (h1 : rowLe a b = true) (h2 : rowLe b c = true) : rowLe a c = true := by
  unfold rowLe at *
  simp only [bne_iff_ne, ne_eq] at *
  exact cmpNats_trans _ _ _ h1 h2

/-- The sort keys of a row. -/
def keysOf (keys : List (RExpr × Bool)) (r : Row) : List (Option Value) := keys.map fun (e, _) => e.eval r

/-- The order of `OrderLimit` on rows. -/
def rowOrd (m : Missing) (keys : List (RExpr × Bool)) (a b : Row) : Bool :=
  orderLe m (keys.map (·.2)) (keysOf keys a, a) (keysOf keys b, b)

theorem rowOrd_total (m : Missing) (keys : List (RExpr × Bool)) (a b : Row) :
    rowOrd m keys a b || rowOrd m keys b a := by
  unfold rowOrd orderLe
  rw [cmpKeys_swap m _ (keysOf keys a)]
  cases h : cmpKeys m (keys.map (·.2)) (keysOf keys a) (keysOf keys b) <;> simp [Ordering.swap, rowLe_total]

theorem keysOf_length (keys : List (RExpr × Bool)) (r : Row) : (keysOf keys r).length = (keys.map (·.2)).length := by
  simp [keysOf]

theorem rowOrd_trans (m : Missing) (keys : List (RExpr × Bool)) (a b c : Row) :
    rowOrd m keys a b = true → rowOrd m keys b c = true → rowOrd m keys a c = true := by
  unfold rowOrd orderLe
  set ds := keys.map (·.2)
  have tr := fun (x y z : Row) => cmpKeys_trans m ds (keysOf keys x) (keysOf keys y) (keysOf keys z)
    (keysOf_length keys x) (keysOf_length keys y) (keysOf_length keys z)
  have sw := fun (x y : Row) => cmpKeys_swap m ds (keysOf keys x) (keysOf keys y)
  have ngt : ∀ x y : Row, (match cmpKeys m ds (keysOf keys x) (keysOf keys y) with
      | .lt => true | .gt => false | .eq => rowLe x y) = true → cmpKeys m ds (keysOf keys x) (keysOf keys y) ≠ .gt := by
    intro x y h e; rw [e] at h; cases h
  intro h1 h2
  have hx := ngt a b h1
  have hy := ngt b c h2
  have hz := tr a b c hx hy
  cases ez : cmpKeys m ds (keysOf keys a) (keysOf keys c) with
  | lt => rfl
  | gt => exact absurd ez hz
  | eq =>
    simp only
    have eca : cmpKeys m ds (keysOf keys c) (keysOf keys a) = .eq := by rw [sw, ez]; rfl
    have hcb := tr c a b (by rw [eca]; simp) hx
    have hba := tr b c a hy (by rw [eca]; simp)
    have ey : cmpKeys m ds (keysOf keys b) (keysOf keys c) = .eq := by
      rw [sw] at hcb
      cases e : cmpKeys m ds (keysOf keys b) (keysOf keys c)
      · rw [e] at hcb; exact absurd rfl hcb
      · rfl
      · exact absurd e hy
    have ex : cmpKeys m ds (keysOf keys a) (keysOf keys b) = .eq := by
      rw [sw] at hba
      cases e : cmpKeys m ds (keysOf keys a) (keysOf keys b)
      · rw [e] at hba; exact absurd rfl hba
      · rfl
      · exact absurd e hx
    rw [ex] at h1; rw [ey] at h2
    exact rowLe_trans h1 h2

theorem rowOrd_antisymm (m : Missing) (keys : List (RExpr × Bool)) (a b : Row) :
    rowOrd m keys a b = true → rowOrd m keys b a = true → a = b := by
  unfold rowOrd orderLe
  intro h1 h2
  have sw := cmpKeys_swap m (keys.map (·.2)) (keysOf keys a) (keysOf keys b)
  cases e : cmpKeys m (keys.map (·.2)) (keysOf keys a) (keysOf keys b)
  · rw [e] at sw; rw [sw] at h2; cases h2
  · rw [e] at sw h1; rw [sw] at h2; exact rowLe_antisymm h1 h2
  · rw [e] at h1; cases h1

/-- `OrderLimit` is a function of the multiset of its input. -/
theorem orderLimitB_perm (m : Missing) (keys : List (RExpr × Bool)) (s l : Option Nat) {xs ys : Bag}
    (h : xs.Perm ys) : orderLimitB m keys s l xs = orderLimitB m keys s l ys := by
  unfold orderLimitB
  have hs : ∀ zs : Bag, ((zs.map fun r => (keys.map fun (e, _) => e.eval r, r)).mergeSort
      (orderLe m (keys.map (·.2)))).map (·.2) = zs.mergeSort (rowOrd m keys) := by
    intro zs
    have hm := List.map_mergeSort (r := rowOrd m keys) (s := orderLe m (keys.map (·.2)))
      (f := fun r => (keysOf keys r, r)) (l := zs) (fun a _ b _ => rfl)
    show List.map _ ((zs.map fun r => (keysOf keys r, r)).mergeSort _) = _
    rw [← hm, List.map_map]
    exact List.map_id _
  simp only [hs, mergeSort_perm_eq (rowOrd m keys) (rowOrd_trans m keys) (rowOrd_total m keys)
    (rowOrd_antisymm m keys) h]

end Tiramemsu.Sem
