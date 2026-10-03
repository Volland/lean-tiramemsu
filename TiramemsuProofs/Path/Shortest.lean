/-
path-evaluation "Shortest modes" (not time-respecting): on a model state, whenever the hop layer
lists exactly the hops of `R`, each once, and a hop determines its letter and target
(`HopFun`, true of a store view), a successful ALL_SHORTEST search from `x` returns, for each end,
every matching walk of minimal length within the bound, each path value once; ANY_SHORTEST returns
one row per end, a matching walk of minimal length. The fuel bound is sufficient.

The arena holds one node per search state, created in the layer of its distance; in ALL_SHORTEST
its predecessors are every (layer node, hop) reaching it from the previous layer, so the paths
spelled through predecessors are exactly the shortest walks to it.
-/
import TiramemsuProofs.Path.Timed

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Search states of the arena -/

/-- The search state of an arena node. -/
def skey (n : SNode) : SState := (n.node, n.state)

/-- A hop determines its letter and its target (true of a store view, whose statement ids are
unique). -/
def HopFun (R : HopRel) : Prop :=
  ∀ x l l' nb nb', R x l nb → R x l' nb' → nb.hop = nb'.hop → l = l' ∧ nb.to = nb'.to

theorem pstep_det {R : HopRel} (hF : HopFun R) {d : Dfa} {p : SState} {nb nb' : Nb} {t t' : Nat}
    (h : PStep R d p nb t) (h' : PStep R d p nb' t') (hh : nb.hop = nb'.hop) : nb.to = nb'.to ∧ t = t' := by
  obtain ⟨l, hR, hs⟩ := h
  obtain ⟨l', hR', hs'⟩ := h'
  obtain ⟨rfl, hto⟩ := hF _ _ _ _ _ hR hR' hh
  rw [hs] at hs'; cases hs'
  exact ⟨hto, rfl⟩

/-- The target search state of a processed transition `(parent, (nb, t))`. -/
def tgt (a : Nat × (Nb × Nat)) : SState := (a.2.1.to, a.2.2)

/-- The predecessor a processed transition records. -/
def recPred (a : Nat × (Nb × Nat)) : Nat × Hop := (a.1, a.2.1.hop)

/-- The predecessors a new node of search state `p` gets from the processed transitions `P`:
all of them (ALL_SHORTEST) or the first (ANY_SHORTEST). -/
def predsOf (all : Bool) (P : List (Nat × (Nb × Nat))) (p : SState) : List (Nat × Hop) :=
  if all then (P.filter fun a => tgt a == p).map recPred
  else ((P.find? fun a => tgt a == p).map recPred).toList

theorem getD_modify {α : Type} (A : Array α) (j : Nat) (f : α → α) (d : α) (i : Nat) :
    (A.modify j f).getD i d = if j = i ∧ i < A.size then f (A.getD i d) else A.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hj : j = i
  · subst hj
    by_cases hi : j < A.size
    · simp [hi, Array.getElem?_eq_getElem hi]
    · simp [hi, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
  · simp [hj]

theorem predsOf_append_ne (all : Bool) (P : List (Nat × (Nb × Nat))) (a : Nat × (Nb × Nat)) (p : SState)
    (h : tgt a ≠ p) : predsOf all (P ++ [a]) p = predsOf all P p := by
  unfold predsOf
  have hb : (tgt a == p) = false := by simpa using h
  split
  · simp [List.filter_append, hb]
  · rw [List.find?_append]
    cases hf : P.find? (fun a => tgt a == p) with
    | some b => rfl
    | none => simp [hb]

theorem predsOf_append_all (P : List (Nat × (Nb × Nat))) (a : Nat × (Nb × Nat)) :
    predsOf true (P ++ [a]) (tgt a) = predsOf true P (tgt a) ++ [recPred a] := by
  simp [predsOf, List.filter_append]

theorem predsOf_append_any (P : List (Nat × (Nb × Nat))) (a : Nat × (Nb × Nat)) (p : SState)
    (h : ∃ b ∈ P, tgt b = p) : predsOf false (P ++ [a]) p = predsOf false P p := by
  unfold predsOf
  simp only [Bool.false_eq_true, if_false, List.find?_append]
  obtain ⟨b, hb, hbp⟩ := h
  cases hf : P.find? (fun a => tgt a == p) with
  | some c => rfl
  | none => exact absurd (by simpa using hbp) (List.find?_eq_none.1 hf b hb)

theorem predsOf_append_first (all : Bool) (P : List (Nat × (Nb × Nat))) (a : Nat × (Nb × Nat))
    (h : ∀ b ∈ P, tgt b ≠ tgt a) : predsOf all (P ++ [a]) (tgt a) = [recPred a] := by
  have hf : P.filter (fun b => tgt b == tgt a) = [] := List.filter_eq_nil_iff.2 (fun b hb => by simpa using h b hb)
  have hn : P.find? (fun b => tgt b == tgt a) = none := List.find?_eq_none.2 (fun b hb => by simpa using h b hb)
  unfold predsOf
  split <;> simp [List.filter_append, hf, List.find?_append, hn]

/-- The fold state of one shortest-path layer at depth `k` (not time-respecting) after processing
the transitions `P` (each with its layer parent). -/
structure SLayer (c : Ctx) (all : Bool) (k : Nat) (A0 : Array SNode) (I0 : Std.HashMap SState Nat) (used0 : Nat)
    (P : List (Nat × (Nb × Nat))) (acc : SAcc) : Prop where
  old : ∀ i < A0.size, acc.arena.getD i default = A0.getD i default
  grow : A0.size ≤ acc.arena.size
  new : ∀ i, A0.size ≤ i → i < acc.arena.size →
    (acc.arena.getD i default).depth = k + 1 ∧ (acc.arena.getD i default).tau = none ∧
    I0[skey (acc.arena.getD i default)]? = none ∧ (∃ a ∈ P, tgt a = skey (acc.arena.getD i default)) ∧
    (acc.arena.getD i default).preds = predsOf all P (skey (acc.arena.getD i default))
  index : ∀ (p : SState) (i : Nat), acc.index[p]? = some i ↔
    I0[p]? = some i ∨ (A0.size ≤ i ∧ i < acc.arena.size ∧ skey (acc.arena.getD i default) = p)
  done : ∀ a ∈ P, ∃ i, acc.index[tgt a]? = some i
  next : acc.next = List.range' A0.size (acc.arena.size - A0.size)
  used : acc.used ≤ c.limit ∧ used0 + (acc.arena.size - A0.size) ≤ acc.used

/-- One transition of a shortest-path layer (not time-respecting) preserves the layer invariant. -/
theorem shortestStep_layer {st : ModelState} {c : Ctx} (hT : c.timed = none) {all : Bool}
    {best : Std.HashMap SState (Option Int)} {k parent : Nat} {pn : SNode}
    {A0 : Array SNode} {I0 : Std.HashMap SState Nat} {used0 : Nat}
    (hd0 : ∀ i < A0.size, (A0.getD i default).depth ≤ k) (hI0 : ∀ (p : SState) (i : Nat), I0[p]? = some i → i < A0.size)
    {P : List (Nat × (Nb × Nat))} {acc acc' : SAcc} {a : Nb × Nat}
    (hS : SLayer c all k A0 I0 used0 P acc)
    (h : ev st (shortestStep c all best k parent pn acc a) = .ok (.ok acc')) :
    SLayer c all k A0 I0 used0 (P ++ [(parent, a)]) acc' := by
  obtain ⟨nb, t⟩ := a
  obtain ⟨hold, hgrow, hnew, hidx, hdone, hnext, hused⟩ := hS
  have hkey_new : ∀ i, A0.size ≤ i → i < acc.arena.size → acc.index[skey (acc.arena.getD i default)]? = some i :=
    fun i h1 h2 => (hidx _ i).2 (.inr ⟨h1, h2, rfl⟩)
  unfold shortestStep at h
  simp only [hT] at h
  cases hj : acc.index.get? (nb.to, t) with
  | none =>
    rw [hj] at h; simp only at h
    rw [Std.HashMap.get?_eq_getElem?] at hj
    obtain ⟨u, hu, h⟩ := ev_bind_ok h
    obtain ⟨rfl, hul⟩ := charge_ok hu
    cases ev_pure_inj h
    have hI0p : I0[(nb.to, t)]? = none := by
      cases h0 : I0[(nb.to, t)]? with
      | none => rfl
      | some i0 => have := (hidx _ i0).2 (.inl h0); rw [hj] at this; cases this
    have hnotP : ∀ b ∈ P, tgt b ≠ tgt (parent, (nb, t)) := by
      intro b hb heq; obtain ⟨i, hi⟩ := hdone b hb; rw [heq] at hi
      simp only [tgt] at hi; rw [hj] at hi; cases hi
    have hkeyne : ∀ i, A0.size ≤ i → i < acc.arena.size → skey (acc.arena.getD i default) ≠ (nb.to, t) := by
      intro i h1 h2 heq; have := hkey_new i h1 h2; rw [heq, hj] at this; cases this
    have hins : ∀ q : SState, (acc.index.insert (nb.to, t) acc.arena.size)[q]? =
        if (nb.to, t) = q then some acc.arena.size else acc.index[q]? := by
      intro q; rw [Std.HashMap.getElem?_insert]; simp only [beq_iff_eq]
    refine ⟨fun i hi => ?_, by simp; omega, fun i h1 h2 => ?_, fun q i => ?_, fun b hb => ?_, ?_, ?_⟩
    · simp only; rw [getD_push_lt _ _ _ (by omega)]; exact hold i hi
    · simp only [Array.size_push] at h2 ⊢
      by_cases hlt : i < acc.arena.size
      · rw [getD_push_lt _ _ _ hlt]
        obtain ⟨r1, r2, r3, ⟨b, hb, hbt⟩, r5⟩ := hnew i h1 hlt
        refine ⟨r1, r2, r3, ⟨b, List.mem_append_left _ hb, hbt⟩, ?_⟩
        rw [r5, predsOf_append_ne _ _ _ _ (fun heq => hkeyne i h1 hlt (by rw [← heq]; rfl))]
      · have : i = acc.arena.size := by omega
        subst this
        rw [getD_push_eq]
        refine ⟨rfl, rfl, hI0p, ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, ?_⟩
        exact (predsOf_append_first all P (parent, (nb, t)) hnotP).symm
    · simp only [Array.size_push]
      rw [hins]
      by_cases hq : (nb.to, t) = q
      · subst hq
        rw [if_pos rfl, hI0p]
        constructor
        · rintro ⟨⟩; exact .inr ⟨hgrow, by omega, by rw [getD_push_eq]; rfl⟩
        · rintro (h0 | ⟨h1, h2, h3⟩)
          · cases h0
          · by_cases hlt : i < acc.arena.size
            · rw [getD_push_lt _ _ _ hlt] at h3; exact absurd h3 (hkeyne i h1 hlt)
            · have : i = acc.arena.size := by omega
              rw [this]
      · rw [if_neg hq, hidx]
        constructor
        · rintro (h0 | ⟨h1, h2, h3⟩)
          · exact .inl h0
          · exact .inr ⟨h1, by omega, by rw [getD_push_lt _ _ _ h2]; exact h3⟩
        · rintro (h0 | ⟨h1, h2, h3⟩)
          · exact .inl h0
          · by_cases hlt : i < acc.arena.size
            · exact .inr ⟨h1, hlt, by rw [getD_push_lt _ _ _ hlt] at h3; exact h3⟩
            · have : i = acc.arena.size := by omega
              subst this
              rw [getD_push_eq] at h3; exact absurd h3 hq
    · simp only
      rw [hins]
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨i, hi⟩ := hdone b hb
        split
        · exact ⟨_, rfl⟩
        · exact ⟨i, hi⟩
      · simp only [List.mem_singleton] at hb; subst hb
        exact ⟨acc.arena.size, by simp [tgt]⟩
    · simp only [Array.size_push]
      rw [hnext, show acc.arena.size + 1 - A0.size = (acc.arena.size - A0.size) + 1 by omega, List.range'_concat]
      congr 2; omega
    · simp only [Array.size_push]; omega
  | some j =>
    rw [hj] at h; simp only at h
    rw [Std.HashMap.get?_eq_getElem?] at hj
    have hkeyuniq : ∀ i, A0.size ≤ i → i < acc.arena.size → skey (acc.arena.getD i default) = (nb.to, t) → i = j := by
      intro i h1 h2 heq; have := hkey_new i h1 h2; rw [heq, hj] at this; cases this; rfl
    have hP' : ∀ i, A0.size ≤ i → i < acc.arena.size → skey (acc.arena.getD i default) ≠ (nb.to, t) →
        predsOf all (P ++ [(parent, (nb, t))]) (skey (acc.arena.getD i default)) =
          predsOf all P (skey (acc.arena.getD i default)) :=
      fun i _ _ hne => predsOf_append_ne _ _ _ _ (fun heq => hne (by rw [← heq]; rfl))
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hdep⟩ := hc
      obtain ⟨u, hu, h⟩ := ev_bind_ok h
      obtain ⟨rfl, hul⟩ := charge_ok hu
      cases ev_pure_inj h
      have hjnew : A0.size ≤ j ∧ j < acc.arena.size ∧ skey (acc.arena.getD j default) = (nb.to, t) := by
        rcases (hidx _ j).1 hj with h0 | h0
        · exfalso
          have hj0 := hI0 _ _ h0
          have := hd0 j hj0
          rw [← hold j hj0, hdep] at this; omega
        · exact h0
      obtain ⟨hj1, hj2, hj3⟩ := hjnew
      set f : SNode → SNode := fun n => { n with preds := n.preds ++ [(parent, nb.hop)] }
      have hmod : ∀ i, (acc.arena.modify j f).getD i default =
          if j = i then f (acc.arena.getD i default) else acc.arena.getD i default := by
        intro i; rw [getD_modify]
        by_cases hji : j = i
        · subst hji; simp [hj2]
        · simp [hji]
      have hskey : ∀ i, skey ((acc.arena.modify j f).getD i default) = skey (acc.arena.getD i default) := by
        intro i; rw [hmod]; split <;> rfl
      refine ⟨fun i hi => ?_, by simp only [Array.size_modify]; exact hgrow, fun i h1 h2 => ?_, fun q i => ?_,
        fun b hb => ?_, by simp only [Array.size_modify]; exact hnext, by simp only [Array.size_modify]; omega⟩
      · simp only; rw [hmod, if_neg (by omega)]; exact hold i hi
      · simp only [Array.size_modify] at h2 ⊢
        obtain ⟨r1, r2, r3, ⟨b, hb, hbt⟩, r5⟩ := hnew i h1 h2
        rw [hskey]
        by_cases hji : j = i
        · subst hji
          rw [hmod, if_pos rfl]
          refine ⟨r1, r2, r3, ⟨b, List.mem_append_left _ hb, hbt⟩, ?_⟩
          simp only [f]
          rw [r5, hj3]
          exact (predsOf_append_all P (parent, (nb, t))).symm
        · rw [hmod, if_neg hji]
          refine ⟨r1, r2, r3, ⟨b, List.mem_append_left _ hb, hbt⟩, ?_⟩
          rw [r5, hP' i h1 h2 (fun heq => hji (hkeyuniq i h1 h2 heq).symm)]
      · simp only [Array.size_modify]
        rw [hidx]
        simp only [hskey]
      · rcases List.mem_append.1 hb with hb | hb
        · exact hdone b hb
        · simp only [List.mem_singleton] at hb; subst hb; exact ⟨j, hj⟩
    · rename_i hc
      cases ev_pure_inj h
      refine ⟨hold, hgrow, fun i h1 h2 => ?_, hidx, fun b hb => ?_, hnext, hused⟩
      · obtain ⟨r1, r2, r3, ⟨b, hb, hbt⟩, r5⟩ := hnew i h1 h2
        refine ⟨r1, r2, r3, ⟨b, List.mem_append_left _ hb, hbt⟩, ?_⟩
        by_cases hk : skey (acc.arena.getD i default) = (nb.to, t)
        · have hij := hkeyuniq i h1 h2 hk
          subst hij
          cases all with
          | true => simp only [Bool.true_and, beq_iff_eq] at hc; exact absurd r1 hc
          | false => rw [r5, predsOf_append_any _ _ _ ⟨b, hb, hbt⟩]
        · rw [r5, hP' i h1 h2 hk]
      · rcases List.mem_append.1 hb with hb | hb
        · exact hdone b hb
        · simp only [List.mem_singleton] at hb; subst hb; exact ⟨j, hj⟩

/-- The transitions of a layer, each with its parent. -/
def layerTrans (layer : List Nat) (Ls : List (List (Nb × Nat))) : List (Nat × (Nb × Nat)) :=
  (List.zipWith (fun i L => L.map (i, ·)) layer Ls).flatten

theorem shortestExpand_fold {st : ModelState} {c : Ctx} (hT : c.timed = none) {all : Bool}
    {best : Std.HashMap SState (Option Int)} {k : Nat} {A0 : Array SNode} {I0 : Std.HashMap SState Nat}
    {used0 : Nat} (hd0 : ∀ i < A0.size, (A0.getD i default).depth ≤ k)
    (hI0 : ∀ (p : SState) (i : Nat), I0[p]? = some i → i < A0.size) :
    ∀ (layer : List Nat) (P : List (Nat × (Nb × Nat))) (acc res : SAcc),
      (∀ i ∈ layer, i < A0.size) → SLayer c all k A0 I0 used0 P acc →
      ev st (layer.foldlM (shortestExpand c all best k) acc) = .ok (.ok res) →
      ∃ Ls : List (List (Nb × Nat)),
        List.Forall₂ (fun i L => ev st (expandOne c (A0.getD i default).node (A0.getD i default).state) =
          .ok (.ok L)) layer Ls ∧
        SLayer c all k A0 I0 used0 (P ++ layerTrans layer Ls) res
  | [], P, acc, res, _, hS, h => by
    simp only [List.foldlM_nil] at h
    cases ev_pure_inj h
    exact ⟨[], .nil, by simpa [layerTrans] using hS⟩
  | i :: layer, P, acc, res, hl, hS, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h2⟩ := ev_bind_ok h
    have hi : i < A0.size := hl i (List.mem_cons_self ..)
    unfold shortestExpand at h1
    simp only at h1
    rw [hS.old i hi] at h1
    obtain ⟨L, hL, h1⟩ := ev_bind_ok h1
    have hS1 := ev_foldlM_pre st (shortestStep c all best k i (A0.getD i default))
      (fun done acc => SLayer c all k A0 I0 used0 (P ++ done.map (i, ·)) acc)
      (fun done b a b' hb hs => by
        have := shortestStep_layer hT hd0 hI0 hb hs
        simpa using this) L [] acc acc1 (by simpa using hS) h1
    simp only [List.nil_append] at hS1
    obtain ⟨Ls, hLs, hres⟩ := shortestExpand_fold hT hd0 hI0 layer _ acc1 res
      (fun j hj => hl j (List.mem_cons_of_mem _ hj)) hS1 h2
    refine ⟨L :: Ls, .cons hL hLs, ?_⟩
    simpa [layerTrans] using hres

/-! ## Paths through predecessors -/

/-- Two walks from a node spelling the same steps have the same word (a hop determines its letter). -/
theorem word_eq_of_stepPairs {R : HopRel} (hF : HopFun R) :
    ∀ {x y y' : Int64} {w w' : List Step}, IsWalk R x w y → IsWalk R x w' y' → stepPairs w = stepPairs w' →
      word w = word w'
  | _, _, _, [], [], _, _, _ => rfl
  | _, _, _, [], _ :: _, _, _, h => by simp [stepPairs] at h
  | _, _, _, _ :: _, [], _, _, h => by simp [stepPairs] at h
  | x, y, y', s :: w, s' :: w', h, h', he => by
    simp only [stepPairs, List.map_cons, List.cons.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨hh, hto⟩, hrest⟩ := he
    obtain ⟨hl, -⟩ := hF _ _ _ _ _ h.1 h'.1 hh
    have h2 : IsWalk R s.2.to w' y' := by rw [hto]; exact h'.2
    simp only [word_cons, hl, word_eq_of_stepPairs hF h.2 h2 hrest]

/-- The predecessors of an arena node: from the previous layer, over hops into it; in ALL_SHORTEST
every such (node, hop), once each. -/
structure PredsOK (R : HopRel) (d : Dfa) (all : Bool) (A : Array SNode) (i : Nat) : Prop where
  ne : (A.getD i default).preds ≠ []
  sound : ∀ j h, (j, h) ∈ (A.getD i default).preds → j < i ∧
    (A.getD j default).depth + 1 = (A.getD i default).depth ∧
    ∃ nb, PStep R d (skey (A.getD j default)) nb (A.getD i default).state ∧ nb.to = (A.getD i default).node ∧
      nb.hop = h
  complete : all = true → ∀ j < A.size, (A.getD j default).depth + 1 = (A.getD i default).depth →
    ∀ nb, PStep R d (skey (A.getD j default)) nb (A.getD i default).state → nb.to = (A.getD i default).node →
      (j, nb.hop) ∈ (A.getD i default).preds
  nodup : all = true → (A.getD i default).preds.Nodup

theorem atDist_unique {R : HopRel} {d : Dfa} {x : Int64} {n m : Nat} {p : SState}
    (h1 : AtDist R d x n p) (h2 : AtDist R d x m p) : n = m := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact h2.2 n h h1.1
  · exact h1.2 m h h2.1

/-- The arena facts the paths through predecessors rely on. -/
structure ArenaOK (R : HopRel) (d : Dfa) (all : Bool) (x : Int64) (A : Array SNode) (I : Std.HashMap SState Nat)
    (k : Nat) : Prop where
  pos : 0 < A.size
  root : skey (A.getD 0 default) = (x, 0) ∧ (A.getD 0 default).depth = 0 ∧ (A.getD 0 default).preds = []
  preds : ∀ i < A.size, 0 < i → PredsOK R d all A i
  dist : ∀ i < A.size, AtDist R d x (A.getD i default).depth (skey (A.getD i default))
  depthLe : ∀ i < A.size, (A.getD i default).depth ≤ k
  index : ∀ (p : SState) (i : Nat), I[p]? = some i ↔ i < A.size ∧ skey (A.getD i default) = p
  complete : ∀ n ≤ k, ∀ p, Rch R d x n p → ∃ i, I[p]? = some i

theorem ArenaOK.key_inj {R : HopRel} {d : Dfa} {all : Bool} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat}
    {k : Nat} (hA : ArenaOK R d all x A I k) {i j : Nat} (hi : i < A.size) (hj : j < A.size)
    (h : skey (A.getD i default) = skey (A.getD j default)) : i = j := by
  have h1 := (hA.index _ i).2 ⟨hi, rfl⟩
  have h2 := (hA.index _ j).2 ⟨hj, h.symm⟩
  rw [h1] at h2; cases h2; rfl

/-- Every path through predecessors spells a walk to the node's search state, of its depth. -/
theorem paths_sound {R : HopRel} {d : Dfa} {all : Bool} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat}
    {k : Nat} (hA : ArenaOK R d all x A I k) :
    ∀ i, i < A.size → ∀ f, (A.getD i default).depth + 1 ≤ f → ∀ s ∈ pathsTo A f i,
      ∃ w : List Step, w.length = (A.getD i default).depth ∧ IsWalk R x w (A.getD i default).node ∧
        d.runL 0 (word w) = some (A.getD i default).state ∧ stepPairs w = s := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf s hs
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [pathsTo] at hs
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hA.root.2.2] at hs
      simp only [List.isEmpty_nil, if_true, List.mem_singleton] at hs
      subst hs
      have hk := hA.root.1
      simp only [skey, Prod.mk.injEq] at hk
      exact ⟨[], by rw [hA.root.2.1]; rfl, hk.1.symm, by rw [hk.2]; rfl, rfl⟩
    · have hP := hA.preds i hi hpos
      rw [if_neg (by simpa using hP.ne)] at hs
      obtain ⟨⟨j, h⟩, hjh, hs⟩ := List.mem_flatMap.1 hs
      obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
      obtain ⟨hji, hdep, nb, ⟨l, hR, hst⟩, hto, hh⟩ := hP.sound j h hjh
      obtain ⟨w', hw1, hw2, hw3, hw4⟩ := ih j hji (by omega) f (by omega) s' hs'
      refine ⟨w' ++ [(l, nb)], by rw [List.length_append, hw1, List.length_singleton]; omega,
        (isWalk_snoc ..).2 ⟨_, hw2, hR, hto⟩, ?_, ?_⟩
      · rw [word_append, runL_append, hw3]
        simp only [Option.bind_some, word_cons, word_nil, Dfa.runL, skey] at hst ⊢
        rw [hst]; rfl
      · rw [stepPairs_append, hw4]; simp [stepPairs, hh, hto]

theorem paths_ne {R : HopRel} {d : Dfa} {all : Bool} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat}
    {k : Nat} (hA : ArenaOK R d all x A I k) :
    ∀ i, i < A.size → ∀ f, (A.getD i default).depth + 1 ≤ f → pathsTo A f i ≠ [] := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [pathsTo]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hA.root.2.2]; simp
    · have hP := hA.preds i hi hpos
      rw [if_neg (by simpa using hP.ne)]
      obtain ⟨⟨j, h⟩, hjh⟩ := List.exists_mem_of_ne_nil _ hP.ne
      obtain ⟨hji, hdep, -⟩ := hP.sound j h hjh
      obtain ⟨s', hs'⟩ := List.exists_mem_of_ne_nil _ (ih j hji (by omega) f (by omega))
      intro hnil
      have : s' ++ [(h, (A.getD i default).node)] ∈ (A.getD i default).preds.flatMap fun (p, h) =>
          (pathsTo A f p).map (· ++ [(h, (A.getD i default).node)]) :=
        List.mem_flatMap.2 ⟨(j, h), hjh, List.mem_map.2 ⟨s', hs', rfl⟩⟩
      rw [hnil] at this; cases this

/-- In ALL_SHORTEST every walk to a node's search state of its depth is spelled by a path through
predecessors. -/
theorem paths_complete {R : HopRel} {d : Dfa} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat}
    {k : Nat} (hA : ArenaOK R d true x A I k) :
    ∀ i, i < A.size → ∀ f, (A.getD i default).depth + 1 ≤ f → ∀ w : List Step,
      w.length = (A.getD i default).depth → IsWalk R x w (A.getD i default).node →
      d.runL 0 (word w) = some (A.getD i default).state → stepPairs w ∈ pathsTo A f i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf w hw1 hw2 hw3
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [pathsTo]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hA.root.2.2, hA.root.2.1] at *
      rw [List.length_eq_zero_iff] at hw1; subst hw1
      simp [stepPairs]
    · have hP := hA.preds i hi hpos
      rw [if_neg (by simpa using hP.ne)]
      obtain ⟨⟨j0, h0⟩, hj0⟩ := List.exists_mem_of_ne_nil _ hP.ne
      obtain ⟨-, hdep0, -⟩ := hP.sound j0 h0 hj0
      have hne : w ≠ [] := by rintro rfl; rw [List.length_nil] at hw1; omega
      obtain ⟨w', s, rfl⟩ : ∃ w' s, w = w' ++ [s] := ⟨w.dropLast, w.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      obtain ⟨y', hw', hR, hto⟩ := (isWalk_snoc ..).1 hw2
      rw [word_append, runL_append] at hw3
      cases hq : d.runL 0 (word w') with
      | none => rw [hq] at hw3; cases hw3
      | some q' =>
        rw [hq] at hw3
        simp only [Option.bind_some, word_cons, word_nil, Dfa.runL] at hw3
        have hst : d.stepL q' s.1 = some (A.getD i default).state := by
          cases hs : d.stepL q' s.1 with
          | none => rw [hs] at hw3; cases hw3
          | some q'' => rw [hs] at hw3; simpa using hw3
        simp only [List.length_append, List.length_singleton] at hw1
        have hrch : Rch R d x w'.length (y', q') := ⟨w', rfl, hw', hq⟩
        have hdist := hA.dist i hi
        have hat : AtDist R d x w'.length (y', q') := by
          refine ⟨hrch, fun m hm hr => hdist.2 (m + 1) (by omega) ?_⟩
          exact (rch_succ R d x m _).2 ⟨_, hr, s.2, ⟨s.1, hR, hst⟩, hto⟩
        obtain ⟨j, hj⟩ := hA.complete w'.length (by have := hA.depthLe i hi; omega) _ hrch
        obtain ⟨hjA, hjk⟩ := (hA.index _ j).1 hj
        have hdj : (A.getD j default).depth = w'.length := atDist_unique (hjk ▸ hA.dist j hjA) hat
        have hmem := hP.complete rfl j hjA (by omega) s.2 (by rw [hjk]; exact ⟨s.1, hR, hst⟩) hto
        have hjk' : skey (A.getD j default) = (y', q') := hjk
        simp only [skey, Prod.mk.injEq] at hjk'
        have hji : j < i := (hP.sound j s.2.hop hmem).1
        have := ih j hji hjA f (by omega) w' hdj.symm (by rw [hjk'.1]; exact hw') (by rw [hjk'.2]; exact hq)
        refine List.mem_flatMap.2 ⟨(j, s.2.hop), hmem, List.mem_map.2 ⟨stepPairs w', this, ?_⟩⟩
        rw [stepPairs_append]; simp [stepPairs, hto]

/-- Two arena nodes with a common path through predecessors are the same node. -/
theorem paths_inj {R : HopRel} (hF : HopFun R) {d : Dfa} {all : Bool} {x : Int64} {A : Array SNode}
    {I : Std.HashMap SState Nat} {k : Nat} (hA : ArenaOK R d all x A I k) {i j f g : Nat} (hi : i < A.size)
    (hj : j < A.size) (hf : (A.getD i default).depth + 1 ≤ f) (hg : (A.getD j default).depth + 1 ≤ g)
    {s : List (Hop × Int64)} (hsi : s ∈ pathsTo A f i) (hsj : s ∈ pathsTo A g j) : i = j := by
  obtain ⟨w, -, hw2, hw3, hw4⟩ := paths_sound hA i hi f hf s hsi
  obtain ⟨w', -, hw2', hw3', hw4'⟩ := paths_sound hA j hj g hg s hsj
  have hs : stepPairs w = stepPairs w' := hw4.trans hw4'.symm
  have hn := end_of_stepPairs hw2 hw2' hs
  have hwd := word_eq_of_stepPairs hF hw2 hw2' hs
  rw [hwd, hw3'] at hw3
  have hq := Option.some.inj hw3
  exact hA.key_inj hi hj (by simp only [skey, hn, hq])

theorem paths_nodup {R : HopRel} (hF : HopFun R) {d : Dfa} {x : Int64} {A : Array SNode}
    {I : Std.HashMap SState Nat} {k : Nat} (hA : ArenaOK R d true x A I k) :
    ∀ i, i < A.size → ∀ f, (A.getD i default).depth + 1 ≤ f → (pathsTo A f i).Nodup := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [pathsTo]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hA.root.2.2]; simp
    · have hP := hA.preds i hi hpos
      rw [if_neg (by simpa using hP.ne)]
      rw [List.nodup_flatMap]
      refine ⟨fun ⟨j, h⟩ hjh => ?_, ?_⟩
      · obtain ⟨hji, hdep, -⟩ := hP.sound j h hjh
        exact (ih j hji (by omega) f (by omega)).map (fun a b hab => List.append_cancel_right hab)
      · refine (hP.nodup rfl).imp_of_mem fun {a b} ha hb hab => ?_
        obtain ⟨j, h⟩ := a
        obtain ⟨j', h'⟩ := b
        obtain ⟨hji, hdep, -⟩ := hP.sound j h ha
        obtain ⟨hji', hdep', -⟩ := hP.sound j' h' hb
        intro s hs1 hs2
        obtain ⟨s1, hm1, rfl⟩ := List.mem_map.1 hs1
        obtain ⟨s2, hm2, he⟩ := List.mem_map.1 hs2
        obtain ⟨hs12, hhh⟩ := List.append_inj' he rfl
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hhh
        rw [hs12] at hm2
        have := paths_inj hF hA (i := j') (j := j) (f := f) (g := f) (by omega) (by omega)
          (by have := hdep'; omega) (by have := hdep; omega) hm2 hm1
        exact hab (by rw [this, hhh])

/-! ## Collecting the rows of a layer -/

theorem collectAll_spec {st : ModelState} {c : Ctx} {arena : Array SNode} {depth : Nat} {targets : List Nat}
    {used used' : Nat} {found : List (List (Hop × Int64) × Option Int)} (hu : used ≤ c.limit)
    (h : ev st (collectAll c arena depth targets used) = .ok (.ok (found, used'))) :
    found.Perm (targets.flatMap fun i => (pathsTo arena (depth + 2) i).map (·, (arena.getD i default).tau)) ∧
      used' ≤ c.limit ∧ used ≤ used' := by
  unfold collectAll at h
  obtain ⟨⟨f0, u0⟩, h1, h2⟩ := ev_bind_ok h
  simp only at h2
  cases ev_pure_inj h2
  have hfold := ev_foldlM_pre st _ (fun (done : List Nat) (acc : List (List (Hop × Int64) × Option Int) × Nat) =>
      acc.1 = done.flatMap (fun i => (pathsTo arena (depth + 2) i).map (·, (arena.getD i default).tau)) ∧
        acc.2 ≤ c.limit ∧ used ≤ acc.2)
    (fun done b i b' hb hs => by
      have hin := ev_foldlM_pre st _ (fun (dp : List (List (Hop × Int64))) (acc : List (List (Hop × Int64) × Option Int) × Nat) =>
          acc.1 = b.1 ++ dp.map (·, (arena.getD i default).tau) ∧ acc.2 ≤ c.limit ∧ used ≤ acc.2)
        (fun dp a p a' ha hs' => by
          obtain ⟨u, hu', hs'⟩ := ev_bind_ok hs'
          obtain ⟨rfl, hul⟩ := charge_ok hu'
          cases ev_pure_inj hs'
          refine ⟨by simp [ha.1], hul, by omega⟩)
        _ [] b b' ⟨by simp, hb.2.1, hb.2.2⟩ hs
      simp only [List.nil_append] at hin
      refine ⟨by rw [hin.1, hb.1]; simp, hin.2.1, hin.2.2⟩)
    targets [] _ _ ⟨by simp, hu, le_refl _⟩ h1
  simp only [List.nil_append] at hfold
  exact ⟨(List.mergeSort_perm _ _).trans (by rw [hfold.1]), hfold.2.1, hfold.2.2⟩

theorem foldl_inv {α β : Type} (F : β → α → β) (Inv : List α → β → Prop) (S : List α)
    (hF : ∀ D acc i, i ∈ S → Inv D acc → Inv (D ++ [i]) (F acc i)) :
    ∀ (l D : List α) (acc : β), (∀ i ∈ l, i ∈ S) → Inv D acc → Inv (D ++ l) (l.foldl F acc)
  | [], D, acc, _, h => by simpa using h
  | i :: l, D, acc, hS, h => by
    have := foldl_inv F Inv S hF l (D ++ [i]) (F acc i) (fun j hj => hS j (List.mem_cons_of_mem _ hj))
      (hF D acc i (hS i (List.mem_cons_self ..)) h)
    simpa using this

/-- ANY_SHORTEST collects, per end, one path of one target of that end, each end once. -/
theorem collectAny_spec (arena : Array SNode) (depth : Nat) (targets : List Nat)
    (endOf : List (Hop × Int64) → Int64)
    (hend : ∀ i ∈ targets, ∀ p ∈ pathsTo arena (depth + 2) i, endOf p = (arena.getD i default).node)
    (hne : ∀ i ∈ targets, pathsTo arena (depth + 2) i ≠ []) :
    (∀ z ∈ collectAny arena depth targets, ∃ i ∈ targets, z.1 ∈ pathsTo arena (depth + 2) i ∧
      z.2 = (arena.getD i default).tau) ∧
    (∀ i ∈ targets, ∃ z ∈ collectAny arena depth targets, endOf z.1 = (arena.getD i default).node) ∧
    ((collectAny arena depth targets).map (endOf ·.1)).Nodup := by
  unfold collectAny
  have := foldl_inv (anyStep arena depth) (fun (D : List Nat) (acc : List (List (Hop × Int64) × Option Int) × Std.HashSet Int64) =>
      (∀ y, acc.2.contains y = true ↔ ∃ i ∈ D, (arena.getD i default).node = y) ∧
      (∀ z ∈ acc.1, ∃ i ∈ D, z.1 ∈ pathsTo arena (depth + 2) i ∧ z.2 = (arena.getD i default).tau) ∧
      (∀ i ∈ D, ∃ z ∈ acc.1, endOf z.1 = (arena.getD i default).node) ∧
      (acc.1.map (endOf ·.1)).Nodup ∧ (∀ z ∈ acc.1, acc.2.contains (endOf z.1) = true))
    targets ?_ targets [] ([], ∅) (fun i hi => hi) ⟨by simp, by simp, by simp, by simp, by simp⟩
  · simp only [List.nil_append] at this
    exact ⟨this.2.1, this.2.2.1, this.2.2.2.1⟩
  · intro D acc i hi ⟨h1, h2, h3, h4, h5⟩
    unfold anyStep
    simp only
    split
    · rename_i hc
      obtain ⟨j, hj, hjn⟩ := (h1 _).1 hc
      refine ⟨fun y => ?_, fun z hz => ?_, fun i' hi' => ?_, h4, h5⟩
      · rw [h1]; constructor
        · rintro ⟨i', hi', h'⟩; exact ⟨i', List.mem_append_left _ hi', h'⟩
        · rintro ⟨i', hi', h'⟩
          rcases List.mem_append.1 hi' with hi' | hi'
          · exact ⟨i', hi', h'⟩
          · simp only [List.mem_singleton] at hi'; subst hi'; exact ⟨j, hj, hjn.trans h'⟩
      · obtain ⟨i', hi', h'⟩ := h2 z hz; exact ⟨i', List.mem_append_left _ hi', h'⟩
      · rcases List.mem_append.1 hi' with hi' | hi'
        · exact h3 i' hi'
        · simp only [List.mem_singleton] at hi'; subst hi'
          obtain ⟨z, hz, hze⟩ := h3 j hj; exact ⟨z, hz, hze.trans hjn⟩
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      obtain ⟨p, ps, hps⟩ := List.exists_cons_of_ne_nil (hne i hi)
      rw [hps]
      simp only
      have hpe : endOf p = (arena.getD i default).node := hend i hi p (by rw [hps]; exact List.mem_cons_self ..)
      refine ⟨fun y => ?_, fun z hz => ?_, fun i' hi' => ?_, ?_, fun z hz => ?_⟩
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, h1]
        constructor
        · rintro (h' | ⟨i', hi', h'⟩)
          · exact ⟨i, List.mem_append_right _ (List.mem_singleton_self _), h'⟩
          · exact ⟨i', List.mem_append_left _ hi', h'⟩
        · rintro ⟨i', hi', h'⟩
          rcases List.mem_append.1 hi' with hi' | hi'
          · exact .inr ⟨i', hi', h'⟩
          · simp only [List.mem_singleton] at hi'; subst hi'; exact .inl h'
      · rcases List.mem_append.1 hz with hz | hz
        · obtain ⟨i', hi', h'⟩ := h2 z hz; exact ⟨i', List.mem_append_left _ hi', h'⟩
        · simp only [List.mem_singleton] at hz; subst hz
          exact ⟨i, List.mem_append_right _ (List.mem_singleton_self _), by rw [hps]; exact List.mem_cons_self .., rfl⟩
      · rcases List.mem_append.1 hi' with hi' | hi'
        · obtain ⟨z, hz, h'⟩ := h3 i' hi'; exact ⟨z, List.mem_append_left _ hz, h'⟩
        · simp only [List.mem_singleton] at hi'; subst hi'
          exact ⟨(p, (arena.getD i' default).tau), List.mem_append_right _ (List.mem_singleton_self _), hpe⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨h4, List.nodup_singleton _, fun a ha b hb hab => ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
        have := h5 z hz
        rw [hab, hb, hpe, hc] at this; cases this
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
        rcases List.mem_append.1 hz with hz | hz
        · exact .inr (h5 z hz)
        · simp only [List.mem_singleton] at hz; subst hz; exact .inl hpe.symm

/-! ## The shortest-path loop invariant -/

theorem mem_layerTrans {P : Nat → List (Nb × Nat) → Prop} (hfun : ∀ j L L', P j L → P j L' → L = L') :
    ∀ {layer : List Nat} {Ls : List (List (Nb × Nat))}, List.Forall₂ P layer Ls → ∀ a,
      a ∈ layerTrans layer Ls ↔ ∃ j ∈ layer, ∃ L, P j L ∧ a.1 = j ∧ a.2 ∈ L
  | _, _, .nil, a => by simp [layerTrans]
  | j :: layer, L :: Ls, .cons hp hr, a => by
    have ih := mem_layerTrans hfun hr a
    simp only [layerTrans, List.zipWith_cons_cons, List.flatten_cons, List.mem_append] at ih ⊢
    rw [ih]
    constructor
    · rintro (h | ⟨j', hj', L', hL', h1, h2⟩)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
        exact ⟨j, List.mem_cons_self .., L, hp, rfl, hb⟩
      · exact ⟨j', List.mem_cons_of_mem _ hj', L', hL', h1, h2⟩
    · rintro ⟨j', hj', L', hL', h1, h2⟩
      rcases List.mem_cons.1 hj' with rfl | hj'
      · have := hfun _ _ _ hL' hp
        subst this
        exact .inl (List.mem_map.2 ⟨a.2, h2, by rw [← h1]⟩)
      · exact .inr ⟨j', hj', L', hL', h1, h2⟩

theorem layerTrans_parent : ∀ (layer : List Nat) (Ls : List (List (Nb × Nat))) (a : Nat × (Nb × Nat)),
    a ∈ layerTrans layer Ls → a.1 ∈ layer
  | [], _, a, h => by simp [layerTrans] at h
  | _ :: _, [], a, h => by simp [layerTrans] at h
  | j :: layer, L :: Ls, a, h => by
    simp only [layerTrans, List.zipWith_cons_cons, List.flatten_cons, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (layerTrans_parent layer Ls a h)

/-- The recorded predecessors of a layer's transitions are distinct. -/
theorem layerTrans_recPred_nodup {P : Nat → List (Nb × Nat) → Prop} (hP : ∀ j L, P j L → (L.map (·.1.hop)).Nodup) :
    ∀ {layer : List Nat} {Ls : List (List (Nb × Nat))}, List.Forall₂ P layer Ls → layer.Nodup →
      ((layerTrans layer Ls).map recPred).Nodup
  | _, _, .nil, _ => by simp [layerTrans]
  | j :: layer, L :: Ls, .cons hp hr, hnd => by
    simp only [layerTrans, List.zipWith_cons_cons, List.flatten_cons, List.map_append]
    refine List.nodup_append.2 ⟨?_, layerTrans_recPred_nodup hP hr (List.nodup_cons.1 hnd).2, ?_⟩
    · rw [List.map_map]
      have := (hP j L hp).map (f := fun h : Hop => (j, h)) (fun a b hab => by simpa using hab)
      simpa [Function.comp_def, recPred] using this
    · intro u hu v hv huv
      subst huv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
      obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hv
      obtain ⟨a', -, rfl⟩ := List.mem_map.1 ha
      have hj := layerTrans_parent layer Ls b hb
      simp only [recPred, Prod.mk.injEq] at hbe
      rw [hbe.1] at hj
      exact (List.nodup_cons.1 hnd).1 hj

/-- A matching walk of minimal length to `y` (an accepting run, no accepting walk to `y` shorter). -/
def MinW (R : HopRel) (d : Dfa) (x y : Int64) (w : List Step) : Prop :=
  IsWalk R x w y ∧ (∃ q, d.runL 0 (word w) = some q ∧ d.accepts q = true) ∧ ∀ n < w.length, ¬ AccR R d x n y

/-- The state of the shortest-path search (not time-respecting) after `k` layers. -/
structure ShInv (R : HopRel) (c : Ctx) (all : Bool) (x : Int64) (A : Array SNode) (I : Std.HashMap SState Nat)
    (E : Std.HashSet Int64) (layer : List Nat) (k used : Nat) (rows : List PathRow) : Prop where
  arena : ArenaOK R c.dfa all x A I k
  layerEq : ∃ lo, layer = List.range' lo (A.size - lo) ∧ ∀ i < A.size, (lo ≤ i ↔ (A.getD i default).depth = k)
  tau : ∀ i < A.size, (A.getD i default).tau = none
  emitted : ∀ y, E.contains y = true ↔ ∃ n ≤ k, AccR R c.dfa x n y
  rowsAll : all = true → (∀ r, r ∈ rows ↔ ∃ y w, MinW R c.dfa x y w ∧ w.length ≤ k ∧ r = walkRow c x w none) ∧
    (rows.map PathRow.path).Nodup
  rowsAny : all = false → (∀ r ∈ rows, ∃ y w, MinW R c.dfa x y w ∧ w.length ≤ k ∧ r = walkRow c x w none) ∧
    (∀ y, E.contains y = true → ∃ r ∈ rows, r.end = y) ∧ (rows.map PathRow.end).Nodup
  bound : Within c.maxHops k
  usedLe : used ≤ c.limit
  fuel : layer ≠ [] → k + 1 ≤ used

theorem mem_predsOf {all : Bool} {P : List (Nat × (Nb × Nat))} {p : SState} {jh : Nat × Hop}
    (h : jh ∈ predsOf all P p) : ∃ a ∈ P, tgt a = p ∧ recPred a = jh := by
  unfold predsOf at h
  split at h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
    obtain ⟨ha, hp⟩ := List.mem_filter.1 ha
    exact ⟨a, ha, by simpa using hp, rfl⟩
  · cases hf : P.find? (fun a => tgt a == p) with
    | none => rw [hf] at h; cases h
    | some a =>
      rw [hf] at h
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at h
      subst h
      exact ⟨a, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl⟩

theorem mem_predsOf_all {P : List (Nat × (Nb × Nat))} {a : Nat × (Nb × Nat)} (ha : a ∈ P) :
    recPred a ∈ predsOf true P (tgt a) := by
  simp only [predsOf, if_true]
  exact List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, by simp⟩, rfl⟩

theorem predsOf_ne {all : Bool} {P : List (Nat × (Nb × Nat))} {p : SState} (h : ∃ a ∈ P, tgt a = p) :
    predsOf all P p ≠ [] := by
  obtain ⟨a, ha, hp⟩ := h
  unfold predsOf
  split
  · intro he
    have : recPred a ∈ (P.filter fun a => tgt a == p).map recPred :=
      List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, by simp [hp]⟩, rfl⟩
    rw [he] at this; cases this
  · cases hf : P.find? (fun a => tgt a == p) with
    | none => exact absurd (by simp [hp]) (List.find?_eq_none.1 hf a ha)
    | some b => simp

theorem predsOf_nodup {P : List (Nat × (Nb × Nat))} (h : (P.map recPred).Nodup) (p : SState) :
    (predsOf true P p).Nodup := by
  simp only [predsOf, if_true]
  exact ((List.filter_sublist (l := P)).map recPred).nodup h

/-- The arena after one layer: the next layer's nodes are the search states at distance `k + 1`,
with their predecessors. -/
theorem layer_arena {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hn : HopsNodup st c)
    {all : Bool} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat} {k lo : Nat}
    (hA : ArenaOK R c.dfa all x A I k) (hlo : ∀ i < A.size, (lo ≤ i ↔ (A.getD i default).depth = k))
    (htau : ∀ i < A.size, (A.getD i default).tau = none)
    {Ls : List (List (Nb × Nat))}
    (hLs : List.Forall₂ (fun i L => ev st (expandOne c (A.getD i default).node (A.getD i default).state) =
      .ok (.ok L)) (List.range' lo (A.size - lo)) Ls)
    {used0 : Nat} {acc : SAcc} (hS : SLayer c all k A I used0 (layerTrans (List.range' lo (A.size - lo)) Ls) acc) :
    ArenaOK R c.dfa all x acc.arena acc.index (k + 1) ∧
      (∀ i < acc.arena.size, (A.size ≤ i ↔ (acc.arena.getD i default).depth = k + 1)) ∧
      (∀ i < acc.arena.size, (acc.arena.getD i default).tau = none) := by
  obtain ⟨hold, hgrow, hnew, hidx, hdone, -, -⟩ := hS
  set layer := List.range' lo (A.size - lo)
  have hfun : ∀ j L L', ev st (expandOne c (A.getD j default).node (A.getD j default).state) = .ok (.ok L) →
      ev st (expandOne c (A.getD j default).node (A.getD j default).state) = .ok (.ok L') → L = L' := by
    intro j L L' h1 h2; rw [h1] at h2; cases h2; rfl
  have hmemP := mem_layerTrans hfun hLs
  have hlay : ∀ j, j ∈ layer ↔ j < A.size ∧ (A.getD j default).depth = k := by
    intro j; rw [List.mem_range'_1]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, (hlo j (by omega)).1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hlo j h1).2 h2, by omega⟩
  -- transitions of the layer are search steps from layer nodes, and all of them are there
  have hPstep : ∀ a ∈ layerTrans layer Ls, a.1 ∈ layer ∧ PStep R c.dfa (skey (A.getD a.1 default)) a.2.1 a.2.2 := by
    intro a ha
    obtain ⟨j, hj, L, hL, h1, h2⟩ := (hmemP a).1 ha
    subst h1
    exact ⟨hj, (hx _ _ L hL a.2.1 a.2.2).1 h2⟩
  have hPall : ∀ j ∈ layer, ∀ nb t, PStep R c.dfa (skey (A.getD j default)) nb t → (j, (nb, t)) ∈ layerTrans layer Ls := by
    intro j hj nb t hs
    obtain ⟨L, -, hL⟩ := forall₂_mem_left hLs j hj
    exact (hmemP _).2 ⟨j, hj, L, hL, rfl, (hx _ _ L hL nb t).2 hs⟩
  have hdepNew : ∀ i, A.size ≤ i → i < acc.arena.size → (acc.arena.getD i default).depth = k + 1 :=
    fun i h1 h2 => (hnew i h1 h2).1
  have hdepOld : ∀ i < A.size, (acc.arena.getD i default).depth ≤ k := fun i hi => by
    rw [hold i hi]; exact hA.depthLe i hi
  have hidx' : ∀ (p : SState) (i : Nat), acc.index[p]? = some i ↔ i < acc.arena.size ∧ skey (acc.arena.getD i default) = p := by
    intro p i
    rw [hidx, hA.index]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨by omega, by rw [hold i h1]; exact h2⟩
      · exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      by_cases hlt : i < A.size
      · exact .inl ⟨hlt, by rw [← hold i hlt]; exact h2⟩
      · exact .inr ⟨by omega, h1, h2⟩
  have hnoRch : ∀ i, A.size ≤ i → i < acc.arena.size → ∀ m ≤ k, ¬ Rch R c.dfa x m (skey (acc.arena.getD i default)) := by
    intro i h1 h2 m hm hr
    obtain ⟨j, hj⟩ := hA.complete m hm _ hr
    rw [(hnew i h1 h2).2.2.1] at hj; cases hj
  refine ⟨⟨by have := hA.pos; omega, by rw [hold 0 hA.pos]; exact hA.root, fun i hi hpos => ?_, fun i hi => ?_, fun i hi => ?_,
    hidx', fun n hn p hr => ?_⟩, fun i hi => ?_, fun i hi => ?_⟩
  · by_cases hlt : i < A.size
    · have hP := hA.preds i hlt hpos
      have hgi := hold i hlt
      refine ⟨by rw [hgi]; exact hP.ne, fun j h hjh => ?_, fun hall j hj hdj nb hs hto => ?_,
        fun hall => by rw [hgi]; exact hP.nodup hall⟩
      · rw [hgi] at hjh ⊢
        obtain ⟨hji, r⟩ := hP.sound j h hjh
        rw [hold j (by omega)]; exact ⟨hji, r⟩
      · rw [hgi] at hdj hs hto ⊢
        have hjA : j < A.size := by
          by_contra hge
          have := hdepNew j (by omega) hj
          have := hA.depthLe i hlt
          omega
        rw [hold j hjA] at hdj hs
        exact hP.complete hall j hjA hdj nb hs hto
    · obtain ⟨hd, -, -, hex, hpr⟩ := hnew i (by omega) hi
      refine ⟨by rw [hpr]; exact predsOf_ne hex, fun j h hjh => ?_, fun hall j hj hdj nb hs hto => ?_,
        fun hall => ?_⟩
      · rw [hpr] at hjh
        obtain ⟨a, ha, hta, hra⟩ := mem_predsOf hjh
        obtain ⟨hal, hst⟩ := hPstep a ha
        simp only [recPred, Prod.mk.injEq] at hra
        obtain ⟨rfl, rfl⟩ := hra
        obtain ⟨hjA, hjk⟩ := (hlay _).1 hal
        rw [hold _ hjA, hjk, hd]
        simp only [tgt, skey, Prod.mk.injEq] at hta
        refine ⟨by omega, rfl, a.2.1, ?_, hta.1, rfl⟩
        rw [← hta.2]; exact hst
      · have hjA : j < A.size := by
          by_contra hge
          have := hdepNew j (by omega) hj
          omega
        rw [hold j hjA] at hdj hs
        have hjl : j ∈ layer := (hlay j).2 ⟨hjA, by omega⟩
        have := mem_predsOf_all (hPall j hjl nb _ hs)
        rw [hpr, hall]
        simpa [tgt, recPred, skey, hto] using this
      · subst hall
        rw [hpr]
        exact predsOf_nodup (layerTrans_recPred_nodup (fun j L hL => hn _ _ L hL) hLs List.nodup_range') _
  · by_cases hlt : i < A.size
    · rw [hold i hlt]; exact hA.dist i hlt
    · obtain ⟨hd, -, -, ⟨a, ha, hta⟩, -⟩ := hnew i (by omega) hi
      obtain ⟨hal, hst⟩ := hPstep a ha
      obtain ⟨hjA, hjk⟩ := (hlay _).1 hal
      rw [hd]
      refine ⟨(rch_succ R c.dfa x k _).2 ⟨_, hjk ▸ (hA.dist _ hjA).1, a.2.1, ?_, ?_⟩, fun m hm hr =>
        hnoRch i (by omega) hi m (by omega) hr⟩
      · rw [← hta]; exact hst
      · rw [← hta]; rfl
  · by_cases hlt : i < A.size
    · have := hdepOld i hlt; omega
    · rw [hdepNew i (by omega) hi]
  · by_cases hnk : n ≤ k
    · obtain ⟨i, hi⟩ := hA.complete n hnk p hr
      exact ⟨i, (hidx p i).2 (.inl hi)⟩
    · by_cases hlow : ∃ m ≤ k, Rch R c.dfa x m p
      · obtain ⟨m, hm, hr'⟩ := hlow
        obtain ⟨i, hi⟩ := hA.complete m hm p hr'
        exact ⟨i, (hidx p i).2 (.inl hi)⟩
      · push Not at hlow
        have hn1 : n = k + 1 := by omega
        subst hn1
        obtain ⟨a', ha', nb, hs, hto⟩ := (rch_succ R c.dfa x k p).1 hr
        obtain ⟨j, hj⟩ := hA.complete k (le_refl _) a' ha'
        obtain ⟨hjA, hjk⟩ := (hA.index _ j).1 hj
        have hdj : (A.getD j default).depth = k := by
          have hd := hA.dist j hjA
          rw [hjk] at hd
          by_contra hne
          have hlt : (A.getD j default).depth < k := by have := hA.depthLe j hjA; omega
          exact hlow _ (by omega) ((rch_succ R c.dfa x _ p).2 ⟨a', hd.1, nb, hs, hto⟩)
        have hjl : j ∈ layer := (hlay j).2 ⟨hjA, hdj⟩
        obtain ⟨i, hi⟩ := hdone _ (hPall j hjl nb p.2 (by rw [hjk]; exact hs))
        refine ⟨i, ?_⟩
        have : tgt (j, (nb, p.2)) = p := by simp [tgt, hto]
        rw [← this]; exact hi
  · constructor
    · intro h1; exact hdepNew i h1 hi
    · intro h1
      by_contra hlt; push Not at hlt
      have := hdepOld i hlt; omega
  · by_cases hlt : i < A.size
    · rw [hold i hlt]; exact htau i hlt
    · exact (hnew i (by omega) hi).2.1

theorem foldl_insert_contains (A : Array SNode) :
    ∀ (l : List Nat) (E : Std.HashSet Int64) (y : Int64),
      (l.foldl (fun e i => e.insert (A.getD i default).node) E).contains y = true ↔
        E.contains y = true ∨ ∃ i ∈ l, (A.getD i default).node = y
  | [], E, y => by simp
  | i :: l, E, y => by
    rw [List.foldl_cons, foldl_insert_contains A l, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro ((h | h) | ⟨j, hj, h⟩)
      · exact .inr ⟨i, List.mem_cons_self .., h⟩
      · exact .inl h
      · exact .inr ⟨j, List.mem_cons_of_mem _ hj, h⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact .inl (.inr h)
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact .inl (.inl h)
        · exact .inr ⟨j, hj, h⟩

/-- A minimal matching walk is exactly a matching walk no longer than any other. -/
theorem minW_iff {R : HopRel} {e : PathExpr} {d : Dfa} (hd : buildDfa (toRE false e) = .ok d) (x y : Int64)
    (w : List Step) :
    MinW R d x y w ↔ IsWalk R x w y ∧ word w ∈ lang e ∧
      ∀ w', IsWalk R x w' y → word w' ∈ lang e → w.length ≤ w'.length := by
  constructor
  · rintro ⟨h1, ⟨q, hq, ha⟩, h3⟩
    refine ⟨h1, (match_iff_run hd w).2 ⟨q, hq, ha⟩, fun w' hw' hl' => ?_⟩
    by_contra hlt; push Not at hlt
    exact h3 w'.length hlt ((accR_iff hd x y _).2 ⟨w', hw', hl', rfl⟩)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, (match_iff_run hd w).1 h2, fun n hn ha => ?_⟩
    obtain ⟨w', hw', hl', rfl⟩ := (accR_iff hd x y n).1 ha
    have := h3 w' hw' hl'; omega

/-- One shortest-path layer (not time-respecting) preserves the invariant, one hop deeper. -/
theorem shInv_step {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hn : HopsNodup st c)
    (hF : HopFun R) (hT : c.timed = none) {all : Bool} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat}
    {best : Std.HashMap SState (Option Int)} {E : Std.HashSet Int64} {layer : List Nat} {k used : Nat}
    {rows : List PathRow} (hI : ShInv R c all x A I E layer k used rows) (hne : layer ≠ [])
    (hok : c.depthOk k = true) {acc : SAcc}
    (hacc : ev st (layer.foldlM (shortestExpand c all best k)
      { arena := A, index := I, used, next := [], tindex := ∅ }) = .ok (.ok acc))
    {found : List (List (Hop × Int64) × Option Int)} {used' : Nat}
    (hcol : ev st (if all then collectAll c acc.arena k (acc.next.filter fun i =>
        c.dfa.accepts (acc.arena.getD i default).state && !E.contains (acc.arena.getD i default).node) acc.used
      else pure (collectAny acc.arena k (acc.next.filter fun i =>
        c.dfa.accepts (acc.arena.getD i default).state && !E.contains (acc.arena.getD i default).node), acc.used)) =
      .ok (.ok (found, used'))) :
    ShInv R c all x acc.arena acc.index
      ((acc.next.filter fun i => c.dfa.accepts (acc.arena.getD i default).state &&
        !E.contains (acc.arena.getD i default).node).foldl (fun e i => e.insert (acc.arena.getD i default).node) E)
      acc.next (k + 1) used' (rows ++ found.map fun (p, tau) => rowOf c x p tau) := by
  obtain ⟨lo, hlay, hlo⟩ := hI.layerEq
  subst hlay
  have hS0 : SLayer c all k A I used [] { arena := A, index := I, used, next := [], tindex := ∅ } := by
    refine ⟨fun _ _ => rfl, le_refl _, fun i h1 h2 => ?_, fun p i => ?_, fun a ha => (by cases ha), ?_, ?_⟩
    · exact absurd h2 (by simp only; omega)
    · simp only
      constructor
      · intro h; exact .inl h
      · rintro (h | ⟨h1, h2, -⟩); exact h; omega
    · simp
    · simp only [Nat.sub_self, Nat.add_zero]; exact ⟨hI.usedLe, le_refl _⟩
  obtain ⟨Ls, hLs, hS⟩ := shortestExpand_fold (all := all) (best := best) hT hI.arena.depthLe
    (fun p i h => ((hI.arena.index p i).1 h).1) _ [] _ acc
    (fun i hi => by rw [List.mem_range'_1] at hi; omega) hS0 hacc
  simp only [List.nil_append] at hS
  obtain ⟨hA', hlo', htau'⟩ := layer_arena hx hn hI.arena hlo hI.tau hLs hS
  have hnext := hS.next
  have hused := hS.used
  set A' := acc.arena
  set targets := acc.next.filter fun i =>
    c.dfa.accepts (A'.getD i default).state && !E.contains (A'.getD i default).node
  have htarg : ∀ i, i ∈ targets ↔ A.size ≤ i ∧ i < A'.size ∧ c.dfa.accepts (A'.getD i default).state = true ∧
      E.contains (A'.getD i default).node = false := by
    intro i
    simp only [targets, List.mem_filter, hnext, List.mem_range'_1, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, by omega, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, by omega⟩, h3, h4⟩
  have hskey : ∀ i (y : Int64) (q : Nat), skey (A'.getD i default) = (y, q) →
      (A'.getD i default).node = y ∧ (A'.getD i default).state = q := by
    intro i y q h; simpa [skey] using h
  -- a target spells minimal matching walks of `k + 1` hops
  have htw : ∀ i ∈ targets, ∀ p ∈ pathsTo A' (k + 2) i, ∃ w, MinW R c.dfa x (A'.getD i default).node w ∧
      w.length = k + 1 ∧ stepPairs w = p := by
    intro i hi p hp
    obtain ⟨h1, h2, h3, h4⟩ := (htarg i).1 hi
    have hd := (hlo' i h2).1 h1
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ := paths_sound hA' i h2 (k + 2) (by omega) p hp
    refine ⟨w, ⟨hw2, ⟨_, hw3, h3⟩, fun n hn ha => ?_⟩, by omega, hw4⟩
    have := (hI.emitted _).2 ⟨n, by omega, ha⟩
    rw [h4] at this; cases this
  -- a minimal matching walk of `k + 1` hops ends at a target
  have hwt : ∀ y w, MinW R c.dfa x y w → w.length = k + 1 →
      ∃ i ∈ targets, (A'.getD i default).node = y ∧ (A'.getD i default).depth = k + 1 ∧
        c.dfa.runL 0 (word w) = some (A'.getD i default).state := by
    intro y w ⟨hw1, ⟨q, hq, ha⟩, hmin⟩ hl
    have hr : Rch R c.dfa x (k + 1) (y, q) := ⟨w, hl, hw1, hq⟩
    have hat : AtDist R c.dfa x (k + 1) (y, q) := ⟨hr, fun m hm hr' => hmin m (by omega) ⟨q, ha, hr'⟩⟩
    obtain ⟨i, hi⟩ := hA'.complete (k + 1) (le_refl _) (y, q) hr
    obtain ⟨hiA, hik⟩ := (hA'.index _ i).1 hi
    have hdi : (A'.getD i default).depth = k + 1 := atDist_unique (hik ▸ hA'.dist i hiA) hat
    obtain ⟨hy, hqq⟩ := hskey i y q hik
    refine ⟨i, (htarg i).2 ⟨(hlo' i hiA).2 hdi, hiA, by rw [hqq]; exact ha, ?_⟩, hy, hdi, by rw [hqq]; exact hq⟩
    cases he : E.contains (A'.getD i default).node
    · rfl
    · obtain ⟨n, hn, hacc⟩ := (hI.emitted _).1 he
      rw [hy] at hacc; exact absurd hacc (hmin n (by omega))
  have hem : ∀ y, (targets.foldl (fun e i => e.insert (A'.getD i default).node) E).contains y = true ↔
      ∃ n ≤ k + 1, AccR R c.dfa x n y := by
    intro y
    rw [foldl_insert_contains, hI.emitted]
    constructor
    · rintro (⟨n, hn, h⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨n, by omega, h⟩
      · obtain ⟨h1, h2, h3, -⟩ := (htarg i).1 hi
        have hd := (hlo' i h2).1 h1
        exact ⟨k + 1, le_refl _, (A'.getD i default).state, h3, hd ▸ (hA'.dist i h2).1⟩
    · rintro ⟨n, hn, t, ht, hr⟩
      by_cases hlow : ∃ m ≤ k, AccR R c.dfa x m y
      · exact .inl hlow
      · push Not at hlow
        have hn1 : n = k + 1 := by
          by_contra hne'; exact hlow n (by omega) ⟨t, ht, hr⟩
        subst hn1
        obtain ⟨w, hw1, hw2, hw3⟩ := hr
        obtain ⟨i, hi, hy, -, -⟩ := hwt y w ⟨hw2, ⟨t, hw3, ht⟩, fun m hm => hlow m (by omega)⟩ hw1
        exact .inr ⟨i, hi, hy⟩
  have htnd : targets.Nodup := (List.filter_sublist (l := acc.next)).nodup (by rw [hnext]; exact List.nodup_range')
  have htau0 : ∀ i ∈ targets, (A'.getD i default).tau = none := fun i hi => htau' i ((htarg i).1 hi).2.1
  have hrowf : ∀ z : List (Hop × Int64) × Option Int,
      (match z with | (p, tau) => rowOf c x p tau) = rowOf c x z.1 z.2 := fun z => by obtain ⟨p, tau⟩ := z; rfl
  have hacc_used : acc.used ≤ c.limit ∧ used + (A'.size - A.size) ≤ acc.used := hused
  have hgrow : A.size ≤ A'.size := hS.grow
  refine ⟨hA', ⟨A.size, hnext, hlo'⟩, htau', hem, fun hall => ?_, fun hall => ?_, within_succ hok, ?_, ?_⟩
  · subst hall
    rw [if_pos rfl] at hcol
    obtain ⟨hperm, -, -⟩ := collectAll_spec hacc_used.1 hcol
    obtain ⟨hold1, hold2⟩ := hI.rowsAll rfl
    have hmemF : ∀ z, z ∈ found ↔ ∃ i ∈ targets, ∃ p ∈ pathsTo A' (k + 2) i, z = (p, none) := by
      intro z; rw [hperm.mem_iff, List.mem_flatMap]
      constructor
      · rintro ⟨i, hi, hz⟩
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
        exact ⟨i, hi, p, hp, by rw [htau0 i hi]⟩
      · rintro ⟨i, hi, p, hp, rfl⟩
        exact ⟨i, hi, List.mem_map.2 ⟨p, hp, by rw [htau0 i hi]⟩⟩
    refine ⟨fun r => ?_, ?_⟩
    · rw [List.mem_append, hold1, List.mem_map]
      constructor
      · rintro (⟨y, w, h1, h2, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact ⟨y, w, h1, by omega, rfl⟩
        · obtain ⟨i, hi, p, hp, rfl⟩ := (hmemF z).1 hz
          obtain ⟨w, hw1, hw2, hw3⟩ := htw i hi p hp
          exact ⟨_, w, hw1, by omega, by rw [walkRow, hw3]⟩
      · rintro ⟨y, w, h1, h2, rfl⟩
        by_cases hl : w.length ≤ k
        · exact .inl ⟨y, w, h1, hl, rfl⟩
        · obtain ⟨i, hi, hy, hdi, hrun⟩ := hwt y w h1 (by omega)
          have hiA := ((htarg i).1 hi).2.1
          have hp := paths_complete hA' i hiA (k + 2) (by omega) w (by omega) (by rw [hy]; exact h1.1) hrun
          exact .inr ⟨(stepPairs w, none), (hmemF _).2 ⟨i, hi, stepPairs w, hp, rfl⟩, rfl⟩
    · have hfst : (found.map Prod.fst).Nodup := by
        rw [(hperm.map Prod.fst).nodup_iff, List.map_flatMap]
        simp only [List.map_map, Function.comp_def, List.map_id']
        refine List.nodup_flatMap.2 ⟨fun i hi => ?_, htnd.imp_of_mem fun {i j} hi hj hij p hp1 hp2 => ?_⟩
        · exact paths_nodup hF hA' i ((htarg i).1 hi).2.1 (k + 2)
            (by have := (hlo' i ((htarg i).1 hi).2.1).1 ((htarg i).1 hi).1; omega)
        · have hi' := (htarg i).1 hi
          have hj' := (htarg j).1 hj
          exact hij (paths_inj hF hA' hi'.2.1 hj'.2.1 (by have := (hlo' i hi'.2.1).1 hi'.1; omega)
            (by have := (hlo' j hj'.2.1).1 hj'.1; omega) hp1 hp2)
      have hfnd : found.Nodup := List.Nodup.of_map Prod.fst hfst
      rw [List.map_append, List.nodup_append]
      refine ⟨hold2, ?_, fun a ha b hb hab => ?_⟩
      · rw [List.map_map]
        refine hfnd.map_on fun z1 hz1 z2 hz2 heq => ?_
        simp only [Function.comp_apply, hrowf] at heq
        have h1 := rowOf_path_inj heq
        obtain ⟨i1, -, p1, -, rfl⟩ := (hmemF z1).1 hz1
        obtain ⟨i2, -, p2, -, rfl⟩ := (hmemF z2).1 hz2
        simp only at h1; rw [h1]
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hr'
        obtain ⟨y, w, hw, hwl, rfl⟩ := (hold1 r).1 hr
        obtain ⟨i, hi, p, hp, rfl⟩ := (hmemF z).1 hz
        obtain ⟨w', -, hw'l, rfl⟩ := htw i hi p hp
        have := rowOf_path_inj hab
        have := congrArg List.length this
        rw [length_stepPairs, length_stepPairs] at this
        omega
  · subst hall
    rw [if_neg (by simp)] at hcol
    cases ev_pure_inj hcol
    obtain ⟨hold1, hold2, hold3⟩ := hI.rowsAny rfl
    have hend : ∀ i ∈ targets, ∀ p ∈ pathsTo A' (k + 2) i,
        (fun p : List (Hop × Int64) => (p.getLast?.map (·.2)).getD x) p = (A'.getD i default).node := by
      intro i hi p hp
      obtain ⟨w, hw1, -, rfl⟩ := htw i hi p hp
      exact isWalk_end hw1.1
    have hne' : ∀ i ∈ targets, pathsTo A' (k + 2) i ≠ [] := fun i hi => by
      have hi' := (htarg i).1 hi
      exact paths_ne hA' i hi'.2.1 (k + 2) (by have := (hlo' i hi'.2.1).1 hi'.1; omega)
    obtain ⟨hc1, hc2, hc3⟩ := collectAny_spec A' k targets _ hend hne'
    refine ⟨fun r hr => ?_, fun y hy => ?_, ?_⟩
    · rcases List.mem_append.1 hr with hr | hr
      · obtain ⟨y, w, h1, h2, h3⟩ := hold1 r hr; exact ⟨y, w, h1, by omega, h3⟩
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hr
        obtain ⟨i, hi, hp, hτ⟩ := hc1 z hz
        obtain ⟨w, hw1, hw2, hw3⟩ := htw i hi z.1 hp
        refine ⟨_, w, hw1, by omega, ?_⟩
        rw [hrowf, hτ, htau0 i hi, walkRow, hw3]
    · rw [foldl_insert_contains] at hy
      rcases hy with hy | ⟨i, hi, rfl⟩
      · obtain ⟨r, hr, hre⟩ := hold2 y hy; exact ⟨r, List.mem_append_left _ hr, hre⟩
      · obtain ⟨z, hz, hze⟩ := hc2 i hi
        exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨z, hz, rfl⟩), by rw [hrowf]; exact hze⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hold3, ?_, fun a ha b hb hab => ?_⟩
      · rw [List.map_map]
        have hfe : (PathRow.end ∘ fun (z : List (Hop × Int64) × Option Int) => match z with
            | (p, tau) => rowOf c x p tau) = fun z => (z.1.getLast?.map (·.2)).getD x := by
          funext z; obtain ⟨p, t⟩ := z; rfl
        rw [hfe]; exact hc3
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hr'
        obtain ⟨y, w, hw, hwl, rfl⟩ := hold1 r hr
        obtain ⟨i, hi, hp, -⟩ := hc1 z hz
        have hyE : E.contains y = true := by
          obtain ⟨hw1, ⟨q, hq, hacc⟩, -⟩ := hw
          exact (hI.emitted y).2 ⟨w.length, hwl, q, hacc, w, rfl, hw1, hq⟩
        have h1 : (walkRow c x w none).end = y := by rw [walkRow_eq hw.1]
        have h2 : (match z with | (p, tau) => rowOf c x p tau).end = (A'.getD i default).node := by
          rw [hrowf]; exact hend i hi z.1 hp
        rw [h1, h2] at hab
        rw [hab, ((htarg i).1 hi).2.2.2] at hyE
        cases hyE
  · split at hcol
    · exact (collectAll_spec hacc_used.1 hcol).2.1
    · cases ev_pure_inj hcol; exact hacc_used.1
  · intro hne'
    have hlt : A.size < A'.size := by
      rw [hnext] at hne'
      by_contra h; apply hne'; rw [show A'.size - A.size = 0 by omega]; rfl
    have h1 := hI.fuel hne
    have h2 : acc.used ≤ used' := by
      split at hcol
      · exact (collectAll_spec hacc_used.1 hcol).2.2
      · cases ev_pure_inj hcol; exact le_refl _
    omega

/-- The shortest-path loop (not time-respecting) ends in a state satisfying the invariant whose
layer is empty or whose depth is the hop bound; the fuel never runs out first. -/
theorem shortestLoop_inv {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hn : HopsNodup st c)
    (hF : HopFun R) (hT : c.timed = none) {all : Bool} {x : Int64} :
    ∀ (fuel : Nat) (A : Array SNode) (I : Std.HashMap SState Nat) (best : Std.HashMap SState (Option Int))
      (E : Std.HashSet Int64) (layer : List Nat) (k used : Nat) (rows res : List PathRow),
      ShInv R c all x A I E layer k used rows → c.limit + 1 ≤ fuel + k →
      ev st (shortestLoop c x all fuel A I best E layer k used rows) = .ok (.ok res) →
      ∃ A' I' E' layer' k' used', ShInv R c all x A' I' E' layer' k' used' res ∧
        (layer' = [] ∨ c.depthOk k' = false)
  | 0, A, I, best, E, layer, k, used, rows, res, hI, hf, h => by
    simp only [shortestLoop] at h
    cases ev_pure_inj h
    refine ⟨A, I, E, layer, k, used, hI, .inl ?_⟩
    by_contra hne
    have := hI.fuel hne; have := hI.usedLe; omega
  | fuel + 1, A, I, best, E, layer, k, used, rows, res, hI, hf, h => by
    rw [shortestLoop.eq_2] at h
    split at h
    · rename_i hc
      cases ev_pure_inj h
      refine ⟨A, I, E, layer, k, used, hI, ?_⟩
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hc
      exact hc
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      obtain ⟨acc, hacc, h⟩ := ev_bind_ok h
      dsimp only at h
      cases all with
      | false =>
        rw [if_neg (by simp)] at h
        obtain ⟨⟨found, used'⟩, hcol, h⟩ := ev_bind_ok h
        exact shortestLoop_inv hx hn hF hT fuel _ _ _ _ _ _ _ _ res
          (shInv_step hx hn hF hT hI hc.1 hc.2 hacc (by rw [if_neg (by simp)]; exact hcol)) (by omega) h
      | true =>
        rw [if_pos rfl] at h
        obtain ⟨⟨found, used'⟩, hcol, h⟩ := ev_bind_ok h
        exact shortestLoop_inv hx hn hF hT fuel _ _ _ _ _ _ _ _ res
          (shInv_step hx hn hF hT hI hc.1 hc.2 hacc (by rw [if_pos rfl]; exact hcol)) (by omega) h

/-- The initial state of the shortest-path search (not time-respecting). -/
theorem shInv_init (R : HopRel) (c : Ctx) (all : Bool) (x : Int64) (hul : 0 + 1 ≤ c.limit) :
    ShInv R c all x #[{ node := x, state := 0, depth := 0, tau := none, preds := [] }]
      ((∅ : Std.HashMap SState Nat).insert (x, 0) 0)
      (if c.dfa.accepts 0 then (∅ : Std.HashSet Int64).insert x else ∅) [0] 0 (0 + 1)
      (if c.dfa.accepts 0 then [rowOf c x [] none] else []) := by
  set A0 : Array SNode := #[{ node := x, state := 0, depth := 0, tau := none, preds := [] }]
  have hI0 : ∀ (p : SState) (i : Nat), ((∅ : Std.HashMap SState Nat).insert (x, 0) 0)[p]? = some i ↔
      i < A0.size ∧ skey (A0.getD i default) = p := by
    intro p i
    rw [Std.HashMap.getElem?_insert]
    simp only [beq_iff_eq, A0]
    by_cases hp : (x, 0) = p
    · subst hp
      rw [if_pos rfl]
      constructor
      · rintro ⟨⟩; exact ⟨by simp, rfl⟩
      · rintro ⟨h1, -⟩
        have : i = 0 := by simp at h1; omega
        rw [this]
    · rw [if_neg hp]
      simp only [Std.HashMap.getElem?_empty, reduceCtorEq, false_iff, not_and]
      intro hi; have : i = 0 := by simp at hi; omega
      subst this; exact fun h' => hp (by simp [skey] at h'; exact h')
  have hA0 : ArenaOK R c.dfa all x A0 ((∅ : Std.HashMap SState Nat).insert (x, 0) 0) 0 := by
    refine ⟨by simp [A0], ⟨rfl, rfl, rfl⟩, fun i hi hpos => absurd hi (by simp [A0]; omega), fun i hi => ?_,
      fun i hi => ?_, hI0, fun n hn p hp => ?_⟩
    · have : i = 0 := by simp [A0] at hi; omega
      subst this
      exact ⟨(rch_zero ..).2 rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    · have : i = 0 := by simp [A0] at hi; omega
      subst this; exact le_refl _
    · have : n = 0 := by omega
      subst this
      rw [rch_zero] at hp; subst hp
      exact ⟨0, (hI0 _ 0).2 ⟨by simp [A0], rfl⟩⟩
  have hrow0 : rowOf c x [] none = walkRow c x [] none := rfl
  have hmin0 : ∀ y w, MinW R c.dfa x y w → w.length ≤ 0 → c.dfa.accepts 0 = true ∧ y = x ∧ w = [] := by
    rintro y w ⟨h1, ⟨q, hq, ha⟩, -⟩ hl
    have : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    simp only [isWalk_nil, word_nil, Dfa.runL, Option.some.injEq] at h1 hq
    subst hq; exact ⟨ha, h1.symm, rfl⟩
  have hminx : c.dfa.accepts 0 = true → MinW R c.dfa x x [] := fun ha =>
    ⟨rfl, ⟨0, rfl, ha⟩, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  have hInit : ShInv R c all x A0 ((∅ : Std.HashMap SState Nat).insert (x, 0) 0)
      (if c.dfa.accepts 0 then (∅ : Std.HashSet Int64).insert x else ∅) [0] 0 (0 + 1)
      (if c.dfa.accepts 0 then [rowOf c x [] none] else []) := by
    refine ⟨hA0, ⟨0, rfl, fun i hi => ?_⟩, fun i hi => ?_, fun y => ?_, fun _ => ⟨fun r => ?_, ?_⟩,
      fun _ => ⟨fun r hr => ?_, fun y hy => ?_, ?_⟩, fun m _ => Nat.zero_le m, hul, fun _ => le_refl _⟩
    · have : i = 0 := by simp [A0] at hi; omega
      subst this; simp [A0]
    · have : i = 0 := by simp [A0] at hi; omega
      subst this; rfl
    · rw [show (∃ n ≤ 0, AccR R c.dfa x n y) ↔ AccR R c.dfa x 0 y from
        ⟨fun ⟨n, hn, h⟩ => (Nat.le_zero.1 hn) ▸ h, fun h => ⟨0, le_refl _, h⟩⟩, accR_zero]
      split
      · rename_i ha
        simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq, ha, true_and]
        exact eq_comm
      · rename_i ha; simp [ha]
    · split
      · rename_i ha
        simp only [List.mem_singleton]
        constructor
        · rintro rfl; exact ⟨x, [], hminx ha, le_refl _, hrow0⟩
        · rintro ⟨y, w, hw, hl, rfl⟩
          obtain ⟨-, -, rfl⟩ := hmin0 y w hw hl; exact hrow0.symm
      · rename_i ha
        simp only [List.not_mem_nil, false_iff, not_exists, not_and]
        intro y w hw hl; exact absurd (hmin0 y w hw hl).1 ha
    · split <;> simp
    · split at hr
      · rename_i ha
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨x, [], hminx ha, le_refl _, hrow0⟩
      · cases hr
    · split at hy
      · rename_i ha
        simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq] at hy
        subst hy
        rw [if_pos ha]
        exact ⟨_, List.mem_singleton_self _, by simp [rowOf]⟩
      · simp at hy
    · split <;> simp
  exact hInit

/-- A successful shortest-path search (not time-respecting) ends in the invariant, every minimal
matching walk within the bound being at most the final depth. -/
theorem shortest_final {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hn : HopsNodup st c)
    (hF : HopFun R) (hT : c.timed = none) {all : Bool} {x : Int64} {rows : List PathRow}
    (h : ev st (shortest c x all) = .ok (.ok rows)) :
    ∃ A I E layer k used, ShInv R c all x A I E layer k used rows ∧
      ∀ y n, AccR R c.dfa x n y → Within c.maxHops n → ∃ m ≤ k, m ≤ n ∧ AccR R c.dfa x m y := by
  unfold shortest at h
  rw [hT] at h
  obtain ⟨u, hu, h⟩ := ev_bind_ok h
  obtain ⟨rfl, hul⟩ := charge_ok hu
  simp only [Option.getD_none] at h
  obtain ⟨A, I, E, layer, k, used, hF', hend⟩ := shortestLoop_inv hx hn hF hT _ _ _ _ _ _ _ _ _ rows
    (shInv_init R c all x hul) (by omega) h
  refine ⟨A, I, E, layer, k, used, hF', fun y n ha hb => ?_⟩
  by_cases hnk : n ≤ k
  · exact ⟨n, hnk, le_refl _, ha⟩
  · rcases hend with hl | hd
    · obtain ⟨lo, hlay, hlo⟩ := hF'.layerEq
      have hnone : ∀ p, ¬ AtDist R c.dfa x k p := by
        intro p hp
        obtain ⟨i, hi⟩ := hF'.arena.complete k (le_refl _) p hp.1
        obtain ⟨hiA, hik⟩ := (hF'.arena.index _ i).1 hi
        have hdi : (A.getD i default).depth = k := atDist_unique (hik ▸ hF'.arena.dist i hiA) hp
        have h1 := (hlo i hiA).2 hdi
        rw [hl] at hlay
        have : A.size - lo = 0 := by
          by_contra hne
          have : List.range' lo (A.size - lo) ≠ [] := by
            obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne; rw [hm]; simp
          exact this hlay.symm
        omega
      obtain ⟨t, ht, hr⟩ := ha
      obtain ⟨m, hm, hr'⟩ := rch_lt_of_empty R c.dfa x k hnone n (y, t) hr
      exact ⟨m, by omega, by omega, t, ht, hr'⟩
    · cases hm : c.maxHops with
      | none => simp [Ctx.depthOk, hm] at hd
      | some m =>
        simp only [Ctx.depthOk, hm, Option.all_some, decide_eq_false_iff_not, Nat.not_lt] at hd
        have := hb m hm; have := hF'.bound m hm; omega

/-- A matching walk no longer than any other matching walk to its end. -/
def Shortest (R : HopRel) (e : PathExpr) (x y : Int64) (w : List Step) : Prop :=
  IsWalk R x w y ∧ word w ∈ lang e ∧ ∀ w', IsWalk R x w' y → word w' ∈ lang e → w.length ≤ w'.length

theorem minW_len {c : Ctx} {R : HopRel} {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat}
    {E : Std.HashSet Int64} {layer : List Nat} {k used : Nat} {all : Bool} {rows : List PathRow}
    (hI : ShInv R c all x A I E layer k used rows)
    (hk : ∀ y n, AccR R c.dfa x n y → Within c.maxHops n → ∃ m ≤ k, m ≤ n ∧ AccR R c.dfa x m y)
    {y : Int64} {w : List Step} (hw : MinW R c.dfa x y w) (hb : Within c.maxHops w.length) : w.length ≤ k := by
  obtain ⟨h1, ⟨q, hq, ha⟩, hmin⟩ := hw
  obtain ⟨m, hm, hmn, hacc⟩ := hk y w.length ⟨q, ha, w, rfl, h1, hq⟩ hb
  by_contra hlt
  exact hmin m (by omega) hacc

/-- path-evaluation "Shortest modes" (ALL_SHORTEST, not time-respecting): when the hop layer lists
exactly the hops of `R`, each once, a hop determines its letter and target, and the automaton is
compiled from `e`, a successful ALL_SHORTEST search from `x` returns exactly the rows of the walks
of `R` from `x` matching `e` within the bound that are no longer than any matching walk to their
end; no path value repeats. -/
theorem allShortest_spec {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hx : HopsExact st c R) (hn : HopsNodup st c) (hF : HopFun R) (hT : c.timed = none)
    (hd : buildDfa (toRE false e) = .ok c.dfa) {rows : List PathRow}
    (h : ev st (shortest c x true) = .ok (.ok rows)) :
    (∀ r, r ∈ rows ↔ ∃ y w, Shortest R e x y w ∧ Within c.maxHops w.length ∧ r = walkRow c x w none) ∧
    (rows.map PathRow.path).Nodup := by
  obtain ⟨A, I, E, layer, k, used, hI, hk⟩ := shortest_final hx hn hF hT h
  obtain ⟨h1, h2⟩ := hI.rowsAll rfl
  refine ⟨fun r => ?_, h2⟩
  rw [h1]
  constructor
  · rintro ⟨y, w, hw, hl, rfl⟩
    exact ⟨y, w, (minW_iff hd x y w).1 hw, fun m hm => by have := hI.bound m hm; omega, rfl⟩
  · rintro ⟨y, w, hw, hb, rfl⟩
    have hw' := (minW_iff hd x y w).2 hw
    exact ⟨y, w, hw', minW_len hI hk hw' hb, rfl⟩

/-- path-evaluation "Shortest modes" (ANY_SHORTEST, not time-respecting): a successful
ANY_SHORTEST search returns one row per end of a matching walk within the bound, each a matching
walk no longer than any other to that end; no end repeats. -/
theorem anyShortest_spec {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hx : HopsExact st c R) (hn : HopsNodup st c) (hF : HopFun R) (hT : c.timed = none)
    (hd : buildDfa (toRE false e) = .ok c.dfa) {rows : List PathRow}
    (h : ev st (shortest c x false) = .ok (.ok rows)) :
    (∀ r ∈ rows, ∃ y w, Shortest R e x y w ∧ Within c.maxHops w.length ∧ r = walkRow c x w none) ∧
    (∀ y w, IsWalk R x w y → word w ∈ lang e → Within c.maxHops w.length → ∃ r ∈ rows, r.end = y) ∧
    (rows.map PathRow.end).Nodup := by
  obtain ⟨A, I, E, layer, k, used, hI, hk⟩ := shortest_final hx hn hF hT h
  obtain ⟨h1, h2, h3⟩ := hI.rowsAny rfl
  refine ⟨fun r hr => ?_, fun y w hw hl hb => ?_, h3⟩
  · obtain ⟨y, w, hw, hwl, rfl⟩ := h1 r hr
    exact ⟨y, w, (minW_iff hd x y w).1 hw, fun m hm => by have := hI.bound m hm; omega, rfl⟩
  · have hacc : AccR R c.dfa x w.length y := (accR_iff hd x y _).2 ⟨w, hw, hl, rfl⟩
    obtain ⟨m, hm, -, hm'⟩ := hk y w.length hacc hb
    exact h2 y ((hI.emitted y).2 ⟨m, hm, hm'⟩)

/-! ## Fuel -/

theorem shortestStep_used {st : ModelState} {c : Ctx} {all : Bool} {best : Std.HashMap SState (Option Int)}
    {k parent used0 : Nat} {pn : SNode} {acc acc' : SAcc} {a : Nb × Nat}
    (hP : acc.used ≤ c.limit ∧ used0 + acc.next.length ≤ acc.used)
    (h : ev st (shortestStep c all best k parent pn acc a) = .ok (.ok acc')) :
    acc'.used ≤ c.limit ∧ used0 + acc'.next.length ≤ acc'.used := by
  obtain ⟨nb, t⟩ := a
  unfold shortestStep at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases ev_pure_inj h; exact hP)
    | (obtain ⟨u, hu, h⟩ := ev_bind_ok h
       obtain ⟨rfl, hul⟩ := charge_ok hu
       cases ev_pure_inj h
       simp only [List.length_append, List.length_singleton]
       omega)

theorem shortestLayer_used {st : ModelState} {c : Ctx} {all : Bool} {best : Std.HashMap SState (Option Int)}
    {k used0 : Nat} (layer : List Nat) {acc acc' : SAcc}
    (hP : acc.used ≤ c.limit ∧ used0 + acc.next.length ≤ acc.used)
    (h : ev st (layer.foldlM (shortestExpand c all best k) acc) = .ok (.ok acc')) :
    acc'.used ≤ c.limit ∧ used0 + acc'.next.length ≤ acc'.used := by
  refine ev_foldlM_inv (fun acc : SAcc => acc.used ≤ c.limit ∧ used0 + acc.next.length ≤ acc.used)
    (shortestExpand c all best k) st (fun b i b' hb hs => ?_) layer acc acc' hP h
  unfold shortestExpand at hs
  simp only at hs
  obtain ⟨L, -, hs⟩ := ev_bind_ok hs
  exact ev_foldlM_inv (fun acc : SAcc => acc.used ≤ c.limit ∧ used0 + acc.next.length ≤ acc.used)
    _ st (fun b a b' hb hs => shortestStep_used hb hs) L b b' hb hs

/-- path-evaluation "Termination and search bound" (shortest modes, time-respecting or not): every
new layer node is a charged search state and a layer is non-empty only after one, so the loop with
fuel `f` (`f + depth ≥ pathMaxStates + 1`, as for the initial call) has the same outcome as with any
larger fuel. -/
theorem shortestLoop_fuel {st : ModelState} {c : Ctx} {x : Int64} {all : Bool} :
    ∀ (f k : Nat) (A : Array SNode) (I : Std.HashMap SState Nat) (best : Std.HashMap SState (Option Int))
      (E : Std.HashSet Int64) (layer : List Nat) (d used : Nat) (rows : List PathRow),
      used ≤ c.limit → (layer ≠ [] → d + 1 ≤ used) → c.limit + 1 ≤ f + d →
      ev st (shortestLoop c x all f A I best E layer d used rows) =
        ev st (shortestLoop c x all (f + k) A I best E layer d used rows)
  | 0, k, A, I, best, E, layer, d, used, rows, hle, hfu, hf => by
    have hl : layer = [] := by
      by_contra hne; have := hfu hne; omega
    subst hl
    cases k with
    | zero => rfl
    | succ k => rw [show 0 + (k + 1) = k + 1 by omega, shortestLoop.eq_1, shortestLoop.eq_2]; simp
  | f + 1, k, A, I, best, E, layer, d, used, rows, hle, hfu, hf => by
    rw [show f + 1 + k = (f + k) + 1 by omega, shortestLoop.eq_2, shortestLoop.eq_2]
    split
    · rfl
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      apply ev_bind_congr
      intro acc hacc
      have hP0 : ({ arena := A, index := I, used := used, next := [], tindex := ∅ } : SAcc).used ≤ c.limit ∧
          used + ({ arena := A, index := I, used := used, next := [], tindex := ∅ } : SAcc).next.length ≤
            ({ arena := A, index := I, used := used, next := [], tindex := ∅ } : SAcc).used := ⟨hle, by simp⟩
      have hP := shortestLayer_used layer hP0 hacc
      dsimp only
      cases all with
      | false =>
        rw [if_neg (by simp), if_neg (by simp), ev_bind, ev_bind]
        simp only [ev_pure]
        exact shortestLoop_fuel f k _ _ _ _ _ _ _ _ hP.1 (fun hne => by
          have := hfu hc.1; have : 0 < acc.next.length := List.length_pos_of_ne_nil hne; omega) (by omega)
      | true =>
        rw [if_pos rfl, if_pos rfl]
        apply ev_bind_congr
        rintro ⟨found, used'⟩ hcol
        obtain ⟨-, hu1, hu2⟩ := collectAll_spec hP.1 hcol
        exact shortestLoop_fuel f k _ _ _ _ _ _ _ _ hu1 (fun hne => by
          have := hfu hc.1; have : 0 < acc.next.length := List.length_pos_of_ne_nil hne; omega) (by omega)

/-! ## Evaluation from the end -/

theorem shortest_inv {R : HopRel} (hS : R.Symm) (e : PathExpr) (x y : Int64) (w : List Step)
    (h : Shortest R e x y w) : Shortest R (.inv e) y x (revWalk x w) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isWalk_rev hS x y w h1, ?_, fun w' hw' hl' => ?_⟩
  · rw [mem_lang_inv, word_rev, flipRev_flipRev]; exact h2
  · rw [length_rev]
    have := h3 (revWalk y w') (isWalk_rev hS y x w' hw') (by rw [word_rev]; exact (mem_lang_inv e _).1 hl')
    rwa [length_rev] at this

theorem shortest_inv' {R : HopRel} (hS : R.Symm) (e : PathExpr) (x y : Int64) (w : List Step)
    (h : Shortest R (.inv e) y x w) : Shortest R e x y (revWalk y w) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isWalk_rev hS y x w h1, ?_, fun w' hw' hl' => ?_⟩
  · rw [word_rev]; exact (mem_lang_inv e _).1 h2
  · rw [length_rev]
    have := h3 (revWalk x w') (isWalk_rev hS x y w' hw') (by rw [mem_lang_inv, word_rev, flipRev_flipRev]; exact hl')
    rwa [length_rev] at this

/-- path-evaluation "Endpoint binding" (ALL_SHORTEST): with a reversible hop relation, the rows into
`y` of the ALL_SHORTEST search from `x` for `e` are exactly the reversed rows from `x` of the
ALL_SHORTEST search from `y` for `^e` (same hop bound). -/
theorem allShortest_fromEnd {st : ModelState} {c c' : Ctx} {R : HopRel} {x y : Int64} {e : PathExpr}
    (hS : R.Symm) (hx : HopsExact st c R) (hn : HopsNodup st c) (hx' : HopsExact st c' R)
    (hn' : HopsNodup st c') (hF : HopFun R) (hT : c.timed = none) (hT' : c'.timed = none)
    (hd : buildDfa (toRE false e) = .ok c.dfa) (hd' : buildDfa (toRE false (.inv e)) = .ok c'.dfa)
    (hb : c'.maxHops = c.maxHops) {rowsS rowsE : List PathRow}
    (hs : ev st (shortest c x true) = .ok (.ok rowsS)) (he : ev st (shortest c' y true) = .ok (.ok rowsE))
    (r : PathRow) :
    (r ∈ rowsS ∧ r.end = y) ↔ (r ∈ rowsE.map PathRow.flip ∧ r.start = x) := by
  have hS1 := (allShortest_spec hx hn hF hT hd hs).1
  have hE1 := (allShortest_spec hx' hn' hF hT' hd' he).1
  constructor
  · rintro ⟨hr, hend⟩
    obtain ⟨y0, w, hw, hwb, rfl⟩ := (hS1 r).1 hr
    have hy : y0 = y := by rw [← hend, walkRow_eq hw.1]
    subst hy
    refine ⟨List.mem_map.2 ⟨walkRow c' y0 (revWalk x w) none, (hE1 _).2 ⟨x, revWalk x w,
      shortest_inv hS e x y0 w hw, by rw [length_rev, hb]; exact hwb, rfl⟩, flip_walkRow hT hT' hw.1⟩,
      by rw [walkRow_eq hw.1]⟩
  · rintro ⟨hr, hstart⟩
    obtain ⟨r2, hr2m, rfl⟩ := List.mem_map.1 hr
    obtain ⟨x0, w, hw, hwb, rfl⟩ := (hE1 r2).1 hr2m
    have hx0 : x0 = x := by
      rw [← hstart, flip_walkRow' hT hT' hw.1, walkRow_eq (isWalk_rev hS y x0 w hw.1)]
    subst hx0
    rw [flip_walkRow' hT hT' hw.1]
    exact ⟨(hS1 _).2 ⟨y, revWalk y w, shortest_inv' hS e x0 y w hw, by rw [length_rev, ← hb]; exact hwb, rfl⟩,
      by rw [walkRow_eq (isWalk_rev hS y x0 w hw.1)]⟩

end Tiramemsu.Path
