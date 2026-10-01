/-
The walk behind the cascade and the dependents read, over any neighbour function: within
sufficient fuel it terminates, its result has no duplicates, starts with the root, and holds
exactly the reflexive-transitive closure of "stands on"; with a limit it fails exactly when the
closure is larger than the limit, and otherwise returns the same list as without a limit.
Requirements: retraction-cascade / "Cascade order, kinds and cycles", "Cascade size limit".
-/
import Tiramemsu.Engine.Walk
import TiramemsuProofs.Store.Reads
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The walk as a pure function -/

/-- The walk loop over a pure neighbour function. -/
def walkLoopP (N : Int64 → List Int64) (limit : Option Nat) :
    Nat → Array Int64 → Std.HashSet Int64 → Nat → WalkResult
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, order, seen, i =>
    if h : i < order.size then
      match walkPush limit (N order[i]) order seen with
      | (_, _, true) => .exceeded
      | (order', seen', false) => walkLoopP N limit fuel order' seen' (i + 1)
    else .done order

def walkP (N : Int64 → List Int64) (limit : Option Nat) (root : Int64) (fuel : Nat) : WalkResult :=
  if limit.any (1 > ·) then .exceeded
  else walkLoopP N limit fuel #[root] (({} : Std.HashSet Int64).insert root) 0

section
variable {σ : Type} (h : (r : ROp) → σ → Except StoreError r.Res) (s : σ)

theorem walkLoop_runPure (nb : Int64 → RProg (List Int64)) (N : Int64 → List Int64)
    (hN : ∀ x, RProg.runPure h s (nb x) = .ok (N x)) (limit : Option Nat) :
    ∀ fuel order seen i, RProg.runPure h s (walkLoop nb limit fuel order seen i) =
      .ok (walkLoopP N limit fuel order seen i)
  | 0, _, _, _ => rfl
  | fuel + 1, order, seen, i => by
    unfold walkLoop walkLoopP
    by_cases hi : i < order.size
    · rw [dif_pos hi, dif_pos hi, RProg.runPure_bind, hN]
      simp only [bind, Except.bind]
      rcases hp : walkPush limit (N order[i]) order seen with ⟨o', s', b⟩
      cases b
      · exact walkLoop_runPure nb N hN limit fuel o' s' (i + 1)
      · rfl
    · rw [dif_neg hi, dif_neg hi]; rfl

theorem walk_runPure (nb : Int64 → RProg (List Int64)) (N : Int64 → List Int64)
    (hN : ∀ x, RProg.runPure h s (nb x) = .ok (N x)) (limit : Option Nat) (root : Int64) (fuel : Nat) :
    RProg.runPure h s (walk nb limit root fuel) = .ok (walkP N limit root fuel) := by
  unfold walk walkP
  split
  · rfl
  · exact walkLoop_runPure h s nb N hN limit fuel _ _ 0

end

/-! ## One expansion -/

/-- The seen set holds exactly the order. -/
def SeenOk (order : Array Int64) (seen : Std.HashSet Int64) : Prop :=
  ∀ x, seen.contains x = true ↔ x ∈ order.toList

theorem seenOk_push {order : Array Int64} {seen : Std.HashSet Int64} (h : SeenOk order seen) (x : Int64) :
    SeenOk (order.push x) (seen.insert x) := by
  intro y
  rw [Std.HashSet.contains_insert, Array.toList_push, List.mem_append, ← h y]
  simp only [Bool.or_eq_true, beq_iff_eq, List.mem_singleton]
  tauto

/-- What one expansion does. -/
structure PushSpec (limit : Option Nat) (ns : List Int64) (order : Array Int64) (seen : Std.HashSet Int64)
    (order' : Array Int64) (seen' : Std.HashSet Int64) (ov : Bool) : Prop where
  pre : order.toList <+: order'.toList
  sub : ∀ x ∈ order'.toList, x ∈ order.toList ∨ x ∈ ns
  all : ov = false → ∀ x ∈ ns, x ∈ order'.toList
  nodup : order.toList.Nodup → order'.toList.Nodup
  seen : SeenOk order' seen'
  exceededSome : ov = true → ∃ L, limit = some L ∧ L < order'.size
  bound : ov = false → limit.all (order.size ≤ ·) → limit.all (order'.size ≤ ·)

theorem nodupApp {order : List Int64} {x : Int64} (hxo : x ∉ order) :
    ∀ a ∈ order, ∀ b ∈ [x], a ≠ b := by
  intro a ha b hb
  rw [List.mem_singleton] at hb
  subst hb
  intro h; subst h; exact hxo ha

theorem walkPush_spec (limit : Option Nat) :
    ∀ (ns : List Int64) (order : Array Int64) (seen : Std.HashSet Int64), SeenOk order seen →
      PushSpec limit ns order seen (walkPush limit ns order seen).1 (walkPush limit ns order seen).2.1
        (walkPush limit ns order seen).2.2
  | [], order, seen, hs => by
    simp only [walkPush]
    refine ⟨List.prefix_refl _, fun x hx => Or.inl hx, ?_, id, hs, ?_, fun _ h => h⟩
    · intro _ x hx; cases hx
    · intro h; cases h
  | x :: xs, order, seen, hs => by
    unfold walkPush
    by_cases hx : seen.contains x = true
    · rw [if_pos hx]
      have ih := walkPush_spec limit xs order seen hs
      refine ⟨ih.pre, fun y hy => (ih.sub y hy).imp id (List.mem_cons_of_mem _), ?_, ih.nodup, ih.seen,
        ih.exceededSome, ih.bound⟩
      intro hov y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ih.pre.subset ((hs y).1 hx)
      · exact ih.all hov y hy
    · rw [if_neg hx]
      have hxo : x ∉ order.toList := fun hm => hx ((hs x).2 hm)
      by_cases hl : limit.any (fun L => (order.push x).size > L) = true
      · rw [if_pos hl]
        refine ⟨?_, ?_, ?_, ?_, seenOk_push hs x, ?_, ?_⟩
        · show order.toList <+: (order.push x).toList
          rw [Array.toList_push]; exact List.prefix_append _ _
        · intro y hy
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact Or.inl hy
          · exact Or.inr (List.mem_cons_self ..)
        · intro h; cases h
        · intro hn
          show (order.push x).toList.Nodup
          rw [Array.toList_push]; exact List.nodup_append.2 ⟨hn, List.nodup_singleton _, nodupApp hxo⟩
        · intro _
          obtain ⟨L, hL, hgt⟩ := (Option.any_eq_true _ _).1 hl
          exact ⟨L, hL, by simpa using hgt⟩
        · intro h; cases h
      · rw [if_neg hl]
        have hs' := seenOk_push hs x
        have ih := walkPush_spec limit xs (order.push x) (seen.insert x) hs'
        have pre1 : order.toList <+: (order.push x).toList := by
          rw [Array.toList_push]; exact List.prefix_append _ _
        refine ⟨pre1.trans ih.pre, ?_, ?_, ?_, ih.seen, ih.exceededSome, ?_⟩
        · intro y hy
          rcases ih.sub y hy with hy | hy
          · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · exact Or.inl hy
            · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inr (List.mem_cons_of_mem _ hy)
        · intro hov y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ih.pre.subset (by rw [Array.toList_push]; exact List.mem_append_right _ (List.mem_singleton_self _))
          · exact ih.all hov y hy
        · intro hn
          apply ih.nodup
          rw [Array.toList_push]
          exact List.nodup_append.2 ⟨hn, List.nodup_singleton _, nodupApp hxo⟩
        · intro hov _
          apply ih.bound hov
          cases limit with
          | none => rfl
          | some L => simpa using hl

/-! ## The loop invariant -/

/-- `x` stands on `y` through the neighbour function. -/
def Edge (N : Int64 → List Int64) (x y : Int64) : Prop := x ∈ N y

/-- The closure: `x` reaches `root` through a chain of "stands on". -/
def Reach (N : Int64 → List Int64) (root x : Int64) : Prop := Relation.ReflTransGen (Edge N) x root

structure LoopInv (N : Int64 → List Int64) (limit : Option Nat) (root : Int64)
    (order : Array Int64) (seen : Std.HashSet Int64) (i : Nat) : Prop where
  seen : SeenOk order seen
  nodup : order.toList.Nodup
  head : order.toList.head? = some root
  reach : ∀ x ∈ order.toList, Reach N root x
  closed : ∀ j (hj : j < i), j < order.size → ∀ y ∈ N (order[j]!), y ∈ order.toList
  le : i ≤ order.size
  bound : limit.all (order.size ≤ ·)

theorem getElem!_of_prefix {a b : Array Int64} (h : a.toList <+: b.toList) {j : Nat} (hj : j < a.size) :
    b[j]! = a[j]! := by
  obtain ⟨t, ht⟩ := h
  have hj' : j < a.toList.length := by simpa using hj
  have hlen := congrArg List.length ht
  simp only [List.length_append, Array.length_toList] at hlen
  have hb : j < b.size := by omega
  rw [getElem!_pos b j hb, getElem!_pos a j hj, ← Array.getElem_toList (h := hb), ← Array.getElem_toList (h := hj)]
  have : b.toList[j]'(by simpa using hb) = (a.toList ++ t)[j]'(by simp; omega) := by
    congr 1 <;> simp [ht]
  rw [this, List.getElem_append_left hj']

theorem loop_step {N : Int64 → List Int64} {limit : Option Nat} {root : Int64} {order : Array Int64}
    {seen : Std.HashSet Int64} {i : Nat} (inv : LoopInv N limit root order seen i) (hi : i < order.size)
    {o' : Array Int64} {s' : Std.HashSet Int64}
    (hp : walkPush limit (N order[i]) order seen = (o', s', false)) :
    LoopInv N limit root o' s' (i + 1) := by
  have sp := walkPush_spec limit (N order[i]) order seen inv.seen
  rw [hp] at sp
  have hsize : order.size ≤ o'.size := by
    have := sp.pre.length_le; simpa using this
  refine ⟨sp.seen, sp.nodup inv.nodup, ?_, ?_, ?_, by omega, sp.bound rfl inv.bound⟩
  · obtain ⟨t, ht⟩ := sp.pre
    rw [← ht, List.head?_append, inv.head]; rfl
  · intro x hx
    rcases sp.sub x hx with hx | hx
    · exact inv.reach x hx
    · have hmem : order[i] ∈ order.toList := Array.getElem_mem_toList ..
      exact Relation.ReflTransGen.head hx (inv.reach _ hmem)
  · intro j hj hj'
    by_cases hji : j < i
    · intro y hy
      have hjo : j < order.size := by omega
      rw [getElem!_of_prefix sp.pre hjo] at hy
      exact sp.pre.subset (inv.closed j hji hjo y hy)
    · have : j = i := by omega
      subst this
      intro y hy
      rw [getElem!_of_prefix sp.pre hi, getElem!_pos order j hi] at hy
      exact sp.all rfl y hy

theorem loop_init (N : Int64 → List Int64) (limit : Option Nat) (root : Int64)
    (hl : limit.any (1 > ·) = false) :
    LoopInv N limit root #[root] (({} : Std.HashSet Int64).insert root) 0 := by
  refine ⟨?_, by simp, rfl, ?_, fun j hj => by omega, by simp, ?_⟩
  · intro x
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq]
    show root = x ↔ x ∈ [root]
    rw [List.mem_singleton]; exact eq_comm
  · intro x hx
    simp at hx; subst hx; exact Relation.ReflTransGen.refl
  · cases limit with
    | none => rfl
    | some L => simp at hl ⊢; omega

/-- A complete order holds the whole closure. -/
theorem closure_sub {N : Int64 → List Int64} {limit : Option Nat} {root : Int64} {order : Array Int64}
    {seen : Std.HashSet Int64} {i : Nat} (inv : LoopInv N limit root order seen i) (hi : ¬ i < order.size) :
    ∀ x, Reach N root x → x ∈ order.toList := by
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl => exact List.mem_of_mem_head? inv.head
  | head hab _ ih =>
    rename_i a b
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ih
    have hj' : j < order.size := by simpa using hj
    apply inv.closed j (by omega) hj'
    rw [getElem!_pos order j hj', ← Array.getElem_toList]
    exact hab

/-! ## Results -/

/-- The result of the loop when it completes: the closure, without duplicates, root first,
within the limit. -/
theorem loop_done {N : Int64 → List Int64} {limit : Option Nat} {root : Int64} :
    ∀ fuel order seen i o, LoopInv N limit root order seen i →
      walkLoopP N limit fuel order seen i = .done o →
      (∀ x, x ∈ o.toList ↔ Reach N root x) ∧ o.toList.Nodup ∧ o.toList.head? = some root ∧
        limit.all (o.size ≤ ·)
  | 0, _, _, _, _, _, h => by simp [walkLoopP] at h
  | fuel + 1, order, seen, i, o, inv, h => by
    unfold walkLoopP at h
    by_cases hi : i < order.size
    · rw [dif_pos hi] at h
      rcases hp : walkPush limit (N order[i]) order seen with ⟨o', s', b⟩
      rw [hp] at h
      cases b
      · exact loop_done fuel o' s' (i + 1) o (loop_step inv hi hp) h
      · cases h
    · rw [dif_neg hi] at h
      cases h
      exact ⟨fun x => ⟨inv.reach x, closure_sub inv hi x⟩, inv.nodup, inv.head, inv.bound⟩

/-- When the loop stops at the limit, the closure is larger than the limit. -/
theorem loop_over {N : Int64 → List Int64} {limit : Option Nat} {root : Int64} :
    ∀ fuel order seen i, LoopInv N limit root order seen i →
      walkLoopP N limit fuel order seen i = .exceeded →
      ∃ L, limit = some L ∧ ∃ l : List Int64, l.Nodup ∧ (∀ x ∈ l, Reach N root x) ∧ L < l.length
  | 0, _, _, _, _, h => by simp [walkLoopP] at h
  | fuel + 1, order, seen, i, inv, h => by
    unfold walkLoopP at h
    by_cases hi : i < order.size
    · rw [dif_pos hi] at h
      have sp := walkPush_spec limit (N order[i]) order seen inv.seen
      rcases hp : walkPush limit (N order[i]) order seen with ⟨o', s', b⟩
      rw [hp] at h sp
      cases b
      · exact loop_over fuel o' s' (i + 1) (loop_step inv hi hp) h
      · obtain ⟨L, hL, hlt⟩ := sp.exceededSome rfl
        refine ⟨L, hL, o'.toList, sp.nodup inv.nodup, ?_, by simpa using hlt⟩
        intro x hx
        rcases sp.sub x hx with hx | hx
        · exact inv.reach x hx
        · exact Relation.ReflTransGen.head hx (inv.reach _ (Array.getElem_mem_toList ..))
    · rw [dif_neg hi] at h; cases h

/-- With enough fuel the loop never runs out: fuel beyond the number of statements a walk can
reach suffices. -/
theorem loop_fuel {N : Int64 → List Int64} {limit : Option Nat} {root : Int64} (U : List Int64)
    (hU : ∀ x, Reach N root x → x ∈ U) :
    ∀ fuel order seen i, LoopInv N limit root order seen i → U.toFinset.card + 1 ≤ fuel + i →
      walkLoopP N limit fuel order seen i ≠ .outOfFuel
  | 0, order, seen, i, inv, hf => by
    exfalso
    have hsub : order.toList.toFinset ⊆ U.toFinset := by
      intro x hx; simp only [List.mem_toFinset] at hx ⊢; exact hU x (inv.reach x hx)
    have h1 := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup inv.nodup, Array.length_toList] at h1
    have h2 := inv.le
    omega
  | fuel + 1, order, seen, i, inv, hf => by
    unfold walkLoopP
    by_cases hi : i < order.size
    · rw [dif_pos hi]
      rcases hp : walkPush limit (N order[i]) order seen with ⟨o', s', b⟩
      cases b
      · exact loop_fuel U hU fuel o' s' (i + 1) (loop_step inv hi hp) (by omega)
      · simp
    · rw [dif_neg hi]; simp

/-- Without a limit the loop never stops at the limit. -/
theorem walkPush_none (ns : List Int64) (order : Array Int64) (seen : Std.HashSet Int64) :
    (walkPush none ns order seen).2.2 = false := by
  induction ns generalizing order seen with
  | nil => rfl
  | cons x xs ih =>
    unfold walkPush
    by_cases hx : seen.contains x = true
    · rw [if_pos hx]; exact ih _ _
    · rw [if_neg hx]; exact ih _ _

theorem walkPush_limit_none {limit : Option Nat} :
    ∀ (ns : List Int64) (order : Array Int64) (seen : Std.HashSet Int64) {o' : Array Int64}
      {s' : Std.HashSet Int64}, walkPush limit ns order seen = (o', s', false) →
      walkPush none ns order seen = (o', s', false)
  | [], _, _, _, _, h => by simpa [walkPush] using h
  | x :: xs, order, seen, o', s', h => by
    unfold walkPush at h ⊢
    by_cases hx : seen.contains x = true
    · rw [if_pos hx] at h ⊢; exact walkPush_limit_none xs order seen h
    · rw [if_neg hx] at h ⊢
      by_cases hl : limit.any (fun L => (order.push x).size > L) = true
      · simp only [hl, if_true] at h; cases h
      · simp only [hl, Bool.false_eq_true, if_false] at h
        exact walkPush_limit_none xs _ _ h

theorem loop_limit_none {N : Int64 → List Int64} {limit : Option Nat} :
    ∀ fuel order seen i o, walkLoopP N limit fuel order seen i = .done o →
      walkLoopP N none fuel order seen i = .done o
  | 0, _, _, _, _, h => by simp [walkLoopP] at h
  | fuel + 1, order, seen, i, o, h => by
    unfold walkLoopP at h ⊢
    by_cases hi : i < order.size
    · rw [dif_pos hi] at h ⊢
      rcases hp : walkPush limit (N order[i]) order seen with ⟨o', s', b⟩
      rw [hp] at h
      cases b
      · rw [walkPush_limit_none _ _ _ hp]; exact loop_limit_none fuel o' s' (i + 1) o h
      · cases h
    · rw [dif_neg hi] at h ⊢; exact h

/-- The walk, completely: with fuel above the number of statements the closure may hold, it
returns, root first and without duplicates, exactly the closure of "stands on"; with a limit it
fails exactly when the closure is larger, and otherwise returns the same list. -/
theorem walk_spec (N : Int64 → List Int64) (root : Int64) (fuel : Nat)
    (U : List Int64) (hU : ∀ x, Reach N root x → x ∈ U) (hfuel : U.toFinset.card < fuel) :
    ∃ o : List Int64, o.Nodup ∧ o.head? = some root ∧ (∀ x, x ∈ o ↔ Reach N root x) ∧
      ∀ limit, walkP N limit root fuel = (if limit.any (· < o.length) then .exceeded else .done o.toArray) := by
  -- the unlimited walk completes
  have init0 := loop_init N none root rfl
  have hne := loop_fuel (limit := none) U hU fuel _ _ 0 init0 (by omega)
  obtain ⟨o, ho⟩ : ∃ o, walkLoopP N none fuel #[root] (({} : Std.HashSet Int64).insert root) 0 = .done o := by
    cases hres : walkLoopP N none fuel #[root] (({} : Std.HashSet Int64).insert root) 0 with
    | done o => exact ⟨o, rfl⟩
    | exceeded =>
      obtain ⟨L, hL, _⟩ := loop_over fuel _ _ 0 init0 hres
      cases hL
    | outOfFuel => exact absurd hres hne
  obtain ⟨hmem, hnd, hhd, _⟩ := loop_done fuel _ _ 0 o init0 ho
  refine ⟨o.toList, hnd, hhd, hmem, fun limit => ?_⟩
  unfold walkP
  by_cases h0 : limit.any (1 > ·) = true
  · rw [if_pos h0]
    obtain ⟨L, hL, hL1⟩ := (Option.any_eq_true _ _).1 h0
    have : 1 ≤ o.toList.length := by
      cases hc : o.toList with
      | nil => rw [hc] at hhd; cases hhd
      | cons _ _ => simp
    subst hL
    rw [if_pos]
    simp only [Option.any_some, decide_eq_true_eq] at hL1 ⊢
    simp only [Array.length_toList] at *
    omega
  · rw [if_neg h0]
    have h0' : limit.any (1 > ·) = false := by simpa using h0
    have init := loop_init N limit root h0'
    have hne' := loop_fuel (limit := limit) U hU fuel _ _ 0 init (by omega)
    cases hres : walkLoopP N limit fuel #[root] (({} : Std.HashSet Int64).insert root) 0 with
    | done o' =>
      have := loop_limit_none fuel _ _ 0 o' hres
      rw [ho] at this
      cases this
      obtain ⟨_, _, _, hb⟩ := loop_done fuel _ _ 0 o init hres
      have hnot : limit.any (· < o.toList.length) = false := by
        cases limit with
        | none => rfl
        | some L =>
          simp at hb
          simp only [Option.any_some, decide_eq_false_iff_not, Array.length_toList]
          omega
      rw [hnot]; simp
    | exceeded =>
      obtain ⟨L, hL, l, hlnd, hlr, hlt⟩ := loop_over fuel _ _ 0 init hres
      rw [if_pos]
      subst hL
      simp only [Option.any_some, decide_eq_true_eq]
      have hsub : l.toFinset ⊆ o.toList.toFinset := by
        intro x hx; simp only [List.mem_toFinset] at hx ⊢; exact (hmem x).2 (hlr x hx)
      have := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hlnd, List.toFinset_card_of_nodup hnd] at this
      simp only [Array.length_toList] at *
      omega
    | outOfFuel => exact absurd hres hne'

end Tiramemsu.Engine
