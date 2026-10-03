/-
path-evaluation "Trail mode" (and time-respecting TRAIL): on a model state, whenever the hop layer
lists exactly the hops of `R`, each hop once (`HopsExact`, `HopsNodup`), and the automaton is
compiled from `e`, a successful TRAIL search from `x` returns exactly one row per trail of `R`
from `x` (no repeated hop identity) whose word is in `lang e`, whose length is within the hop
bound and which is allowed by the hop rule (time-respecting searches), with that trail's path
value and arrival. The fuel bound is sufficient.

The arena holds one node per partial trail: its parent chain spells the trail's steps, and the
nodes of each layer are exactly the partial trails of that length.
-/
import TiramemsuProofs.Path.Reach

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Arena chains -/

/-- The steps spelled by the parent chain of arena node `i`. -/
def steps (A : Array TNode) (i : Nat) : List (Hop × Int64) := stepsOf A (i + 1) (some i) []

/-- Arena node 0 is the root (no parent, no hop); every other node has an earlier parent and a hop. -/
structure Chain (A : Array TNode) : Prop where
  pos : 0 < A.size
  root : (A.getD 0 default).parent = none ∧ (A.getD 0 default).hop = none
  link : ∀ i, 0 < i → i < A.size →
    ∃ p h, (A.getD i default).parent = some p ∧ p < i ∧ (A.getD i default).hop = some h

theorem stepsOf_none (A : Array TNode) : ∀ (f : Nat) (acc : List (Hop × Int64)), stepsOf A f none acc = acc
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem stepsOf_eq {A : Array TNode} (hC : Chain A) :
    ∀ i, i < A.size → ∀ f, i + 1 ≤ f → ∀ acc, stepsOf A f (some i) acc = steps A i ++ acc := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf acc
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    unfold steps
    simp only [stepsOf]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hC.root.1, hC.root.2]; simp [stepsOf_none]
    · obtain ⟨p, h, hp, hpi, hh⟩ := hC.link i hpos hi
      rw [hp, hh]
      simp only
      rw [ih p hpi (by omega) f (by omega), ih p hpi (by omega) i (by omega)]
      simp

theorem steps_zero {A : Array TNode} (hC : Chain A) : steps A 0 = [] := by
  unfold steps; simp only [stepsOf]; rw [hC.root.2]

theorem steps_link {A : Array TNode} (hC : Chain A) {i p : Nat} {h : Hop} (hi : i < A.size)
    (hp : (A.getD i default).parent = some p) (hpi : p < i) (hh : (A.getD i default).hop = some h) :
    steps A i = steps A p ++ [(h, (A.getD i default).node)] := by
  conv_lhs => unfold steps
  simp only [stepsOf]
  rw [hp, hh]; simp only
  rw [stepsOf_eq hC p (by omega) i (by omega)]

theorem onChain_iff {A : Array TNode} (hC : Chain A) (ident : Int64 × Nat) :
    ∀ i, i < A.size → ∀ f, i + 1 ≤ f →
      (onChain A ident f (some i) = true ↔ ident ∈ (steps A i).map (·.1.identity)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [onChain]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hC.root.1, hC.root.2, steps_zero hC]
      cases f <;> simp [onChain]
    · obtain ⟨p, h, hp, hpi, hh⟩ := hC.link i hpos hi
      rw [hp, hh, steps_link hC hi hp hpi hh]
      simp only [Option.any_some, Bool.or_eq_true]
      rw [ih p hpi (by omega) f (by omega)]
      simp only [beq_iff_eq, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
      tauto

theorem getD_push_lt {α : Type} (A : Array α) (n d : α) {i : Nat} (hi : i < A.size) :
    (A.push n).getD i d = A.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  rw [if_neg (by omega)]

theorem getD_push_eq {α : Type} (A : Array α) (n d : α) : (A.push n).getD A.size d = n := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push]

theorem Chain.push {A : Array TNode} (hC : Chain A) {n : TNode} {p : Nat} {h : Hop}
    (hp : n.parent = some p) (hpA : p < A.size) (hh : n.hop = some h) : Chain (A.push n) := by
  refine ⟨by simp, ?_, fun i hi hiA => ?_⟩
  · rw [getD_push_lt _ _ _ hC.pos]; exact hC.root
  · simp only [Array.size_push] at hiA
    by_cases hlt : i < A.size
    · rw [getD_push_lt _ _ _ hlt]; exact hC.link i hi hlt
    · have : i = A.size := by omega
      subst this
      rw [getD_push_eq]
      exact ⟨p, h, hp, hpA, hh⟩

theorem steps_push {A : Array TNode} (hC : Chain A) {n : TNode} {p : Nat} {h : Hop}
    (hp : n.parent = some p) (hpA : p < A.size) (hh : n.hop = some h) :
    ∀ i, i < A.size → steps (A.push n) i = steps A i := by
  have hC' := hC.push hp hpA hh
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [steps_zero hC, steps_zero hC']
    · obtain ⟨q, h', hq, hqi, hh'⟩ := hC.link i hpos hi
      have hq' : ((A.push n).getD i default).parent = some q := by rw [getD_push_lt _ _ _ hi]; exact hq
      have hh'' : ((A.push n).getD i default).hop = some h' := by rw [getD_push_lt _ _ _ hi]; exact hh'
      rw [steps_link hC' (by simp; omega) hq' hqi hh'', steps_link hC hi hq hqi hh', ih q hqi (by omega),
        getD_push_lt _ _ _ hi]

theorem steps_push_new {A : Array TNode} (hC : Chain A) {n : TNode} {p : Nat} {h : Hop}
    (hp : n.parent = some p) (hpA : p < A.size) (hh : n.hop = some h) :
    steps (A.push n) A.size = steps A p ++ [(h, n.node)] := by
  have hC' := hC.push hp hpA hh
  have hp' : ((A.push n).getD A.size default).parent = some p := by rw [getD_push_eq]; exact hp
  have hh' : ((A.push n).getD A.size default).hop = some h := by rw [getD_push_eq]; exact hh
  rw [steps_link hC' (by simp) hp' hpA hh', steps_push hC hp hpA hh p hpA, getD_push_eq]

/-- `A'` extends `A`: its first nodes and their chains are `A`'s. -/
def AExt (A A' : Array TNode) : Prop :=
  A.size ≤ A'.size ∧ ∀ i < A.size, A'.getD i default = A.getD i default ∧ steps A' i = steps A i

theorem AExt.refl (A : Array TNode) : AExt A A := ⟨le_refl _, fun _ _ => ⟨rfl, rfl⟩⟩

theorem AExt.trans {A B C : Array TNode} (h1 : AExt A B) (h2 : AExt B C) : AExt A C :=
  ⟨le_trans h1.1 h2.1, fun i hi => by
    obtain ⟨a, b⟩ := h1.2 i hi
    obtain ⟨a', b'⟩ := h2.2 i (by have := h1.1; omega)
    exact ⟨a'.trans a, b'.trans b⟩⟩

theorem AExt.push {A : Array TNode} (hC : Chain A) {n : TNode} {p : Nat} {h : Hop}
    (hp : n.parent = some p) (hpA : p < A.size) (hh : n.hop = some h) : AExt A (A.push n) :=
  ⟨by simp, fun i hi => ⟨getD_push_lt _ _ _ hi, steps_push hC hp hpA hh i hi⟩⟩

/-! ## Trails of a walk relation -/

/-- The (hop, node reached) steps of a walk. -/
def stepPairs (w : List Step) : List (Hop × Int64) := w.map fun s => (s.2.hop, s.2.to)

/-- The time after the hops of a walk (`none`: some hop is not allowed); untimed searches keep it. -/
def walkTau (c : Ctx) : List Step → Option Int → Option (Option Int)
  | [], τ => some τ
  | s :: w, τ => (c.tstep s.2 τ).bind (walkTau c w)

theorem walkTau_append (c : Ctx) : ∀ (u v : List Step) (τ : Option Int),
    walkTau c (u ++ v) τ = (walkTau c u τ).bind (walkTau c v)
  | [], v, τ => rfl
  | s :: u, v, τ => by
    simp only [List.cons_append, walkTau]
    cases c.tstep s.2 τ with
    | none => rfl
    | some τ' => exact walkTau_append c u v τ'

/-- The end of a walk is the last node its steps reach (the start when it has none). -/
theorem isWalk_end {R : HopRel} : ∀ {x y : Int64} {w : List Step}, IsWalk R x w y →
    ((stepPairs w).getLast?.map (·.2)).getD x = y
  | _, _, [], h => h
  | _, _, [s], h => by simp [stepPairs] at h ⊢; exact h.2
  | _, _, s :: s' :: w, h => by
    have := isWalk_end h.2
    rw [← this]
    simp only [stepPairs, List.map_cons, List.getLast?_cons_cons]
    rw [List.getLast?_eq_getLast (by simp)]
    rfl

/-- The row of a walk from `x` with its time. -/
def walkRow (c : Ctx) (x : Int64) (w : List Step) (τ : Option Int) : PathRow := rowOf c x (stepPairs w) τ

theorem walkRow_eq {R : HopRel} {c : Ctx} {x y : Int64} {w : List Step} (h : IsWalk R x w y) (τ : Option Int) :
    walkRow c x w τ = { start := x, «end» := y, hops := w.length, path := some (pathOf x w),
                        arrival := arrivalOf c τ } := by
  simp only [walkRow, rowOf]
  rw [isWalk_end h]
  simp [pathOf, stepPairs, Function.comp_def]

/-! ## One TRAIL layer -/

/-- The arena node a transition from arena node `i` adds: none when the hop rule refuses it at
`i`'s time or its identity is already on `i`'s trail. -/
def trailNew (c : Ctx) (A : Array TNode) (i : Nat) (a : Nb × Nat) : Option TNode :=
  match c.tstep a.1 (A.getD i default).tau with
  | none => none
  | some tau =>
    if a.1.hop.identity ∈ (steps A i).map (·.1.identity) then none
    else some { node := a.1.to, state := a.2, parent := some i, hop := some a.1.hop, tau }

theorem trailStep_fold {st : ModelState} {c : Ctx} {A : Array TNode} (hC : Chain A) {i : Nat} (hi : i < A.size) :
    ∀ (L : List (Nb × Nat)) (B : Array TNode) (u : Nat) (res : Array TNode × Nat),
      Chain B → AExt A B → u = B.size → u ≤ c.limit →
      ev st (L.foldlM (trailStep c i (A.getD i default)) (B, u)) = .ok (.ok res) →
      Chain res.1 ∧ AExt A res.1 ∧ res.2 = res.1.size ∧ res.2 ≤ c.limit ∧
        res.1.toList = B.toList ++ L.filterMap (trailNew c A i)
  | [], B, u, res, hB, hE, hu, hl, h => by
    simp only [List.foldlM_nil] at h
    cases ev_pure_inj h
    exact ⟨hB, hE, hu, hl, by simp⟩
  | a :: L, B, u, res, hB, hE, hu, hl, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', h1, h2⟩ := ev_bind_ok h
    have hiB : i < B.size := lt_of_lt_of_le hi hE.1
    have hchain : onChain B a.1.hop.identity (B.size + 1) (some i) = true ↔
        a.1.hop.identity ∈ (steps A i).map (·.1.identity) := by
      rw [onChain_iff hB _ i hiB _ (by omega), (hE.2 i hi).2]
    obtain ⟨nb, t⟩ := a
    unfold trailStep at h1
    simp only at h1
    rw [List.filterMap_cons]
    cases hn : c.tstep nb (A.getD i default).tau with
    | none =>
      rw [hn] at h1; simp only at h1
      cases ev_pure_inj h1
      have htn : trailNew c A i (nb, t) = none := by simp only [trailNew, hn]
      rw [htn]
      exact trailStep_fold hC hi L B u res hB hE hu hl h2
    | some tau =>
      rw [hn] at h1; simp only at h1
      split at h1
      · rename_i hon
        cases ev_pure_inj h1
        have htn : trailNew c A i (nb, t) = none := by simp only [trailNew, hn]; rw [if_pos (hchain.1 hon)]
        rw [htn]
        exact trailStep_fold hC hi L B u res hB hE hu hl h2
      · rename_i hon
        obtain ⟨u', hu', h1⟩ := ev_bind_ok h1
        obtain ⟨rfl, hul⟩ := charge_ok hu'
        cases ev_pure_inj h1
        have hnot : ¬ nb.hop.identity ∈ (steps A i).map (·.1.identity) := fun h' => hon (hchain.2 h')
        have htn : trailNew c A i (nb, t) =
            some { node := nb.to, state := t, parent := some i, hop := some nb.hop, tau } := by
          simp only [trailNew, hn]; rw [if_neg hnot]
        rw [htn]
        have hB' := hB.push (n := { node := nb.to, state := t, parent := some i, hop := some nb.hop, tau })
          rfl hiB rfl
        have hE' := hE.trans (AExt.push hB (n := { node := nb.to, state := t, parent := some i, hop := some nb.hop, tau })
          rfl hiB rfl)
        obtain ⟨r1, r2, r3, r4, r5⟩ := trailStep_fold hC hi L _ _ res hB' hE' (by simp; omega) hul h2
        exact ⟨r1, r2, r3, r4, by rw [r5]; simp⟩

/-- The new arena nodes of a layer: per layer node, in order, the nodes its transitions add. -/
def layerNew (c : Ctx) (A : Array TNode) (idxs : List Nat) (Ls : List (List (Nb × Nat))) : List TNode :=
  (List.zipWith (fun i L => L.filterMap (trailNew c A i)) idxs Ls).flatten

theorem trailExtend_fold {st : ModelState} {c : Ctx} {A : Array TNode} (hC : Chain A) :
    ∀ (idxs : List Nat) (B : Array TNode) (u : Nat) (res : Array TNode × Nat),
      (∀ i ∈ idxs, i < A.size) → Chain B → AExt A B → u = B.size → u ≤ c.limit →
      ev st (idxs.foldlM (trailExtend c) (B, u)) = .ok (.ok res) →
      ∃ Ls : List (List (Nb × Nat)),
        List.Forall₂ (fun i L => ev st (expandOne c (A.getD i default).node (A.getD i default).state) = .ok (.ok L))
          idxs Ls ∧
        Chain res.1 ∧ AExt A res.1 ∧ res.2 = res.1.size ∧ res.2 ≤ c.limit ∧
        res.1.toList = B.toList ++ layerNew c A idxs Ls
  | [], B, u, res, _, hB, hE, hu, hl, h => by
    simp only [List.foldlM_nil] at h
    cases ev_pure_inj h
    exact ⟨[], .nil, hB, hE, hu, hl, by simp [layerNew]⟩
  | i :: idxs, B, u, res, hidx, hB, hE, hu, hl, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨⟨B', u'⟩, h1, h2⟩ := ev_bind_ok h
    have hi : i < A.size := hidx i (List.mem_cons_self ..)
    unfold trailExtend at h1
    simp only at h1
    rw [(hE.2 i hi).1] at h1
    obtain ⟨L, hL, h1⟩ := ev_bind_ok h1
    obtain ⟨r1, r2, r3, r4, r5⟩ := trailStep_fold hC hi L B u (B', u') hB hE hu hl h1
    obtain ⟨Ls, hLs, s1, s2, s3, s4, s5⟩ :=
      trailExtend_fold hC idxs B' u' res (fun j hj => hidx j (List.mem_cons_of_mem _ hj)) r1 r2 r3 r4 h2
    refine ⟨L :: Ls, .cons hL hLs, s1, s2, s3, s4, ?_⟩
    rw [s5, r5]
    simp [layerNew]

theorem mem_layerNew {c : Ctx} {A : Array TNode} {P : Nat → List (Nb × Nat) → Prop} :
    ∀ {idxs : List Nat} {Ls : List (List (Nb × Nat))}, List.Forall₂ P idxs Ls → ∀ {e : TNode},
      e ∈ layerNew c A idxs Ls → ∃ i ∈ idxs, ∃ L, P i L ∧ ∃ a ∈ L, trailNew c A i a = some e
  | _, _, .nil, _, h => by simp [layerNew] at h
  | i :: idxs, L :: Ls, .cons hp hr, e, h => by
    simp only [layerNew, List.zipWith_cons_cons, List.flatten_cons, List.mem_append, List.mem_filterMap] at h
    rcases h with ⟨a, ha, he⟩ | h
    · exact ⟨i, List.mem_cons_self .., L, hp, a, ha, he⟩
    · obtain ⟨j, hj, L', hL', a, ha, he⟩ := mem_layerNew hr h
      exact ⟨j, List.mem_cons_of_mem _ hj, L', hL', a, ha, he⟩

theorem mem_layerNew_of {c : Ctx} {A : Array TNode} :
    ∀ {idxs : List Nat} {Ls : List (List (Nb × Nat))} {P : Nat → List (Nb × Nat) → Prop},
      List.Forall₂ P idxs Ls → (∀ i L L', P i L → P i L' → L = L') →
      ∀ {i : Nat} {L : List (Nb × Nat)} {a : Nb × Nat} {e : TNode}, i ∈ idxs → P i L → a ∈ L →
        trailNew c A i a = some e → e ∈ layerNew c A idxs Ls
  | _, _, _, .nil, _, _, _, _, _, hi, _, _, _ => by cases hi
  | j :: idxs, L' :: Ls, P, .cons hp hr, hfun, i, L, a, e, hi, hPi, ha, he => by
    simp only [layerNew, List.zipWith_cons_cons, List.flatten_cons, List.mem_append, List.mem_filterMap]
    rcases List.mem_cons.1 hi with rfl | hi
    · exact .inl ⟨a, hfun _ _ _ hPi hp ▸ ha, he⟩
    · exact .inr (mem_layerNew_of hr hfun hi hPi ha he)

theorem trailNew_spec {c : Ctx} {A : Array TNode} {i : Nat} {a : Nb × Nat} {e : TNode}
    (h : trailNew c A i a = some e) :
    ∃ tau, c.tstep a.1 (A.getD i default).tau = some tau ∧
      a.1.hop.identity ∉ (steps A i).map (·.1.identity) ∧
      e = { node := a.1.to, state := a.2, parent := some i, hop := some a.1.hop, tau } := by
  unfold trailNew at h
  split at h
  · cases h
  · rename_i tau htau
    split at h
    · cases h
    · rename_i hn
      cases h
      exact ⟨tau, htau, hn, rfl⟩

theorem getD_of_toList {A A' : Array TNode} {N : List TNode} (h : A'.toList = A.toList ++ N) :
    A'.size = A.size + N.length ∧ ∀ k (hk : k < N.length), A'.getD (A.size + k) default = N[k] := by
  have hs : A'.size = A.size + N.length := by
    rw [← Array.length_toList, h, List.length_append, Array.length_toList]
  refine ⟨hs, fun k hk => ?_⟩
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, List.getElem?_append_right (by simp)]
  simp [hk]

/-- A filter-map that keeps some elements, each as its image under `g`, is a sublist of the map. -/
theorem filterMap_sublist_map {α β : Type} (f : α → Option β) (g : α → β)
    (h : ∀ a b, f a = some b → b = g a) : ∀ l : List α, (l.filterMap f).Sublist (l.map g)
  | [] => by simp
  | a :: l => by
    rw [List.filterMap_cons, List.map_cons]
    cases hf : f a with
    | none => exact (filterMap_sublist_map f g h l).cons _
    | some b => rw [h a b hf]; exact (filterMap_sublist_map f g h l).cons₂ _

/-- The new nodes of a layer have distinct (parent, hop) pairs. -/
theorem layerNew_keys_nodup {c : Ctx} {A : Array TNode} {P : Nat → List (Nb × Nat) → Prop} :
    ∀ {idxs : List Nat} {Ls : List (List (Nb × Nat))}, List.Forall₂ P idxs Ls → idxs.Nodup →
      (∀ i L, P i L → (L.map (·.1.hop)).Nodup) →
      ((layerNew c A idxs Ls).map fun e => (e.parent, e.hop)).Nodup
  | _, _, .nil, _, _ => by simp [layerNew]
  | i :: idxs, L :: Ls, .cons hp hr, hnd, hL => by
    simp only [layerNew, List.zipWith_cons_cons, List.flatten_cons, List.map_append]
    have hkey : ∀ a e, trailNew c A i a = some e → (e.parent, e.hop) = (some i, some a.1.hop) := by
      intro a e he; obtain ⟨_, _, _, rfl⟩ := trailNew_spec he; rfl
    refine List.nodup_append.2 ⟨?_, layerNew_keys_nodup hr (List.nodup_cons.1 hnd).2 hL, ?_⟩
    · rw [List.map_filterMap]
      refine List.Sublist.nodup (filterMap_sublist_map _ (fun a => (some i, some a.1.hop)) ?_ L) ?_
      · intro a b hb
        cases he : trailNew c A i a with
        | none => rw [he] at hb; cases hb
        | some e => rw [he] at hb; cases hb; exact hkey a e he
      · have := List.Nodup.map (f := fun h : Hop => (some i, some h)) (fun h h' hh => by simpa using hh) (hL i L hp)
        simpa [List.map_map, Function.comp_def] using this
    · intro k1 hk1 k2 hk2 heq
      subst heq
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.1 hk1
      obtain ⟨e2, he2, hk⟩ := List.mem_map.1 hk2
      obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 he1
      obtain ⟨j, hj, -, -, b, -, hb⟩ := mem_layerNew hr he2
      rw [hkey a e1 ha] at hk
      obtain ⟨_, _, _, rfl⟩ := trailNew_spec hb
      simp only [Prod.mk.injEq, Option.some.injEq] at hk
      exact (List.nodup_cons.1 hnd).1 (hk.1 ▸ hj)

/-! ## The TRAIL loop invariant -/

/-- The hop layer lists each hop once. -/
def HopsNodup (st : ModelState) (c : Ctx) : Prop :=
  ∀ x q L, ev st (expandOne c x q) = .ok (.ok L) → (L.map (·.1.hop)).Nodup

/-- A partial trail from `x`: a trail of `R` on which the automaton runs (to `q`) and the hop
rule allows every hop (reaching time `τ`). -/
def Partial (R : HopRel) (c : Ctx) (x : Int64) (w : List Step) (y : Int64) (q : Nat) (τ : Option Int) : Prop :=
  IsWalk R x w y ∧ c.dfa.runL 0 (word w) = some q ∧ IsTrail w ∧ walkTau c w (c.timed.getD none) = some τ

/-- Arena node `i` spells the partial trail `w`. -/
def Rep (R : HopRel) (c : Ctx) (x : Int64) (A : Array TNode) (i : Nat) (w : List Step) : Prop :=
  Partial R c x w (A.getD i default).node (A.getD i default).state (A.getD i default).tau ∧ steps A i = stepPairs w

/-- The row of arena node `i`, when its state accepts. -/
def trailRowAt (c : Ctx) (x : Int64) (A : Array TNode) (i : Nat) : Option PathRow :=
  if c.dfa.accepts (A.getD i default).state then some (rowOf c x (steps A i) (A.getD i default).tau) else none

/-- The state of the TRAIL search after `depth` layers: the arena holds each partial trail of at
most `depth` hops exactly once, the layer `[lo, hi)` those of exactly `depth` hops. -/
structure TrailInv (R : HopRel) (c : Ctx) (x : Int64) (A : Array TNode) (lo hi depth used : Nat)
    (rows : List PathRow) : Prop where
  chain : Chain A
  size : hi = A.size
  lohi : lo ≤ hi
  rep : ∀ i < A.size, ∃ w, Rep R c x A i w ∧ w.length ≤ depth ∧ (lo ≤ i ↔ w.length = depth)
  complete : ∀ w y q τ, Partial R c x w y q τ → w.length ≤ depth →
    ∃ i < A.size, steps A i = stepPairs w ∧ (A.getD i default).state = q ∧ (A.getD i default).tau = τ
  uniq : ∀ i j, i < A.size → j < A.size → steps A i = steps A j → i = j
  rowsEq : rows = (List.range A.size).filterMap (trailRowAt c x A)
  bound : Within c.maxHops depth
  usedEq : used = A.size
  usedLe : used ≤ c.limit
  fuel : lo < hi → depth + 1 ≤ used

theorem stepPairs_append (u v : List Step) : stepPairs (u ++ v) = stepPairs u ++ stepPairs v := by
  simp [stepPairs]

theorem length_stepPairs (w : List Step) : (stepPairs w).length = w.length := by simp [stepPairs]

theorem stepPairs_ids (w : List Step) : (stepPairs w).map (·.1.identity) = w.map (·.2.hop.identity) := by
  simp [stepPairs]

/-- Two walks from `x` spelling the same steps end at the same node. -/
theorem end_of_stepPairs {R R' : HopRel} {x y y' : Int64} {w w' : List Step} (h : IsWalk R x w y)
    (h' : IsWalk R' x w' y') (he : stepPairs w = stepPairs w') : y = y' := by
  rw [← isWalk_end h, ← isWalk_end h', he]

/-- A new arena node of a layer extends a node of the layer by one transition of its expansion. -/
theorem trail_new_origin {st : ModelState} {c : Ctx} {A A' : Array TNode} {lo hi : Nat} {Ls : List (List (Nb × Nat))}
    (hsz : hi = A.size)
    (hLs : List.Forall₂ (fun i L => ev st (expandOne c (A.getD i default).node (A.getD i default).state) = .ok (.ok L))
      (List.range' lo (hi - lo)) Ls)
    (hlist : A'.toList = A.toList ++ layerNew c A (List.range' lo (hi - lo)) Ls) {j : Nat}
    (hj1 : A.size ≤ j) (hj2 : j < A'.size) :
    ∃ i, lo ≤ i ∧ i < hi ∧ ∃ L, ev st (expandOne c (A.getD i default).node (A.getD i default).state) = .ok (.ok L) ∧
      ∃ a ∈ L, trailNew c A i a = some (A'.getD j default) := by
  obtain ⟨hs, hget⟩ := getD_of_toList hlist
  obtain ⟨k, rfl⟩ : ∃ k, j = A.size + k := ⟨j - A.size, by omega⟩
  have hk : k < (layerNew c A (List.range' lo (hi - lo)) Ls).length := by omega
  rw [hget k hk]
  obtain ⟨i, hi, L, hL, a, ha, he⟩ := mem_layerNew hLs (List.getElem_mem hk)
  simp only [List.mem_range'] at hi
  exact ⟨i, by omega, by omega, L, hL, a, ha, he⟩

/-- The partial trail spelled by a new arena node. -/
theorem trail_new_rep {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} (hx : HopsExact st c R)
    {A A' : Array TNode} {i : Nat} {w : List Step} {L : List (Nb × Nat)} {a : Nb × Nat} {e : TNode} {j : Nat}
    (hC' : Chain A') (hE : AExt A A') (hi : i < A.size) (hj : A.size ≤ j) (hjA : j < A'.size)
    (hrep : Rep R c x A i w) (hL : ev st (expandOne c (A.getD i default).node (A.getD i default).state) = .ok (.ok L))
    (ha : a ∈ L) (he : trailNew c A i a = some e) (hej : A'.getD j default = e) :
    ∃ l, Rep R c x A' j (w ++ [(l, a.1)]) := by
  obtain ⟨tau, htau, hnot, rfl⟩ := trailNew_spec he
  obtain ⟨nb, t⟩ := a
  obtain ⟨l, hR, hstep⟩ := (hx _ _ L hL nb t).1 ha
  obtain ⟨⟨hw1, hw2, hw3, hw4⟩, hw5⟩ := hrep
  refine ⟨l, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hej]; exact (isWalk_append ..).2 ⟨_, hw1, hR, rfl⟩
  · rw [hej, word_append, runL_append, hw2]
    simp only [Option.bind_some, word_cons, word_nil, Dfa.runL, hstep]
  · unfold IsTrail
    rw [List.map_append, List.nodup_append]
    refine ⟨hw3, List.nodup_singleton _, fun u hu v hv huv => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv
    subst hv; subst huv
    rw [hw5, stepPairs_ids] at hnot
    exact hnot hu
  · rw [hej, walkTau_append, hw4]
    simp only [Option.bind_some, walkTau, htau]
  · have hp : (A'.getD j default).parent = some i := by rw [hej]
    have hh : (A'.getD j default).hop = some nb.hop := by rw [hej]
    rw [steps_link hC' hjA hp (by omega) hh, (hE.2 i hi).2, hw5, stepPairs_append, hej]
    rfl

theorem Rep.ext {R : HopRel} {c : Ctx} {x : Int64} {A A' : Array TNode} {j : Nat} {w : List Step}
    (h : Rep R c x A j w) (hE : AExt A A') (hj : j < A.size) : Rep R c x A' j w := by
  obtain ⟨hg, hs⟩ := hE.2 j hj
  unfold Rep; rw [hg, hs]; exact h

theorem Rep.length_eq {R : HopRel} {c : Ctx} {x : Int64} {A : Array TNode} {i j : Nat} {w w' : List Step}
    (h : Rep R c x A i w) (h' : Rep R c x A j w') (hs : steps A i = steps A j) : w.length = w'.length := by
  rw [← length_stepPairs, ← length_stepPairs w', ← h.2, ← h'.2, hs]

/-- A partial trail of one more hop: a partial trail and one step. -/
theorem partial_snoc {R : HopRel} {c : Ctx} {x y : Int64} {w : List Step} {s : Step} {q : Nat} {τ : Option Int}
    (h : Partial R c x (w ++ [s]) y q τ) :
    ∃ y0 q0 τ0, Partial R c x w y0 q0 τ0 ∧ R y0 s.1 s.2 ∧ s.2.to = y ∧ c.dfa.stepL q0 s.1 = some q ∧
      c.tstep s.2 τ0 = some τ ∧ s.2.hop.identity ∉ w.map (·.2.hop.identity) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨y0, hw, hR, hto⟩ := (isWalk_snoc ..).1 h1
  rw [word_append, runL_append] at h2
  rw [walkTau_append] at h4
  cases hq : c.dfa.runL 0 (word w) with
  | none => rw [hq] at h2; cases h2
  | some q0 =>
    cases ht : walkTau c w (c.timed.getD none) with
    | none => rw [ht] at h4; cases h4
    | some τ0 =>
      rw [hq] at h2; rw [ht] at h4
      simp only [Option.bind_some, word_cons, word_nil, Dfa.runL] at h2
      simp only [Option.bind_some, walkTau] at h4
      unfold IsTrail at h3
      rw [List.map_append, List.nodup_append] at h3
      refine ⟨y0, q0, τ0, ⟨hw, hq, h3.1, ht⟩, hR, hto, ?_, ?_, fun hm => h3.2.2 _ hm _ (by simp) rfl⟩
      · cases hs : c.dfa.stepL q0 s.1 with
        | none => rw [hs] at h2; cases h2
        | some q' => rw [hs] at h2; simpa using h2
      · cases hs : c.tstep s.2 τ0 with
        | none => rw [hs] at h4; cases h4
        | some τ' => rw [hs] at h4; simpa using h4

/-- One TRAIL layer preserves the invariant, one hop deeper. -/
theorem trailInv_step {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} (hx : HopsExact st c R)
    (hnd : HopsNodup st c) {A A' : Array TNode} {lo hi depth used used' : Nat} {rows : List PathRow}
    (hI : TrailInv R c x A lo hi depth used rows) (hlt : lo < hi) (hok : c.depthOk depth = true)
    (hf : ev st ((List.range' lo (hi - lo)).foldlM (trailExtend c) (A, used)) = .ok (.ok (A', used'))) :
    TrailInv R c x A' hi A'.size (depth + 1) used'
      (rows ++ (List.range (A'.size - hi)).filterMap fun k =>
        let n := A'.getD (hi + k) default
        if c.dfa.accepts n.state then some (rowOf c x (stepsOf A' (A'.size + 1) (some (hi + k)) []) n.tau)
        else none) := by
  obtain ⟨Ls, hLs, hC', hE, hus, hle, hlist⟩ := trailExtend_fold hI.chain (List.range' lo (hi - lo)) A used
    (A', used') (fun i hi' => by simp only [List.mem_range'] at hi'; have := hI.size; omega)
    hI.chain (AExt.refl A) hI.usedEq hI.usedLe hf
  simp only at hus hle hlist hC' hE
  have hsize := hI.size
  obtain ⟨hs, hget⟩ := getD_of_toList hlist
  -- every node of the new arena spells a partial trail of its layer's length
  have hrep : ∀ j < A'.size, ∃ w, Rep R c x A' j w ∧ w.length ≤ depth + 1 ∧ (hi ≤ j ↔ w.length = depth + 1) := by
    intro j hj
    by_cases hjA : j < A.size
    · obtain ⟨w, hw, hwl, -⟩ := hI.rep j hjA
      exact ⟨w, hw.ext hE hjA, by omega, by omega⟩
    · obtain ⟨i, hi1, hi2, L, hL, a, ha, he⟩ := trail_new_origin hsize hLs hlist (by omega) hj
      obtain ⟨w, hw, hwl, hwd⟩ := hI.rep i (by omega)
      obtain ⟨l, hr⟩ := trail_new_rep hx hC' hE (by omega) (by omega) hj hw hL ha he rfl
      have : w.length = depth := hwd.1 hi1
      exact ⟨_, hr, by simp; omega, by simp; omega⟩
  have hPfun : ∀ i L L', ev st (expandOne c (A.getD i default).node (A.getD i default).state) = .ok (.ok L) →
      ev st (expandOne c (A.getD i default).node (A.getD i default).state) = .ok (.ok L') → L = L' := by
    intro i L L' h1 h2; rw [h1] at h2; cases h2; rfl
  -- every partial trail of at most `depth + 1` hops has a node
  have hcomplete : ∀ w y q τ, Partial R c x w y q τ → w.length ≤ depth + 1 →
      ∃ i < A'.size, steps A' i = stepPairs w ∧ (A'.getD i default).state = q ∧ (A'.getD i default).tau = τ := by
    intro w y q τ hw hwl
    by_cases hwd : w.length ≤ depth
    · obtain ⟨i, hi, h1, h2, h3⟩ := hI.complete w y q τ hw hwd
      obtain ⟨hg, hst⟩ := hE.2 i hi
      exact ⟨i, by omega, by rw [hst]; exact h1, by rw [hg]; exact h2, by rw [hg]; exact h3⟩
    · have hne : w ≠ [] := by rintro rfl; simp at hwd
      obtain ⟨w0, s, rfl⟩ : ∃ w0 s, w = w0 ++ [s] :=
        ⟨w.dropLast, w.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      · simp only [List.length_append, List.length_singleton] at hwl hwd
        obtain ⟨y0, q0, τ0, hp0, hR, hto, hstep, htau, hid⟩ := partial_snoc hw
        obtain ⟨i, hiA, h1, h2, h3⟩ := hI.complete w0 y0 q0 τ0 hp0 (by omega)
        obtain ⟨wi, hwi, -, hwid⟩ := hI.rep i hiA
        have hlen : wi.length = w0.length := by rw [← length_stepPairs, ← length_stepPairs w0, ← hwi.2, h1]
        have hlo : lo ≤ i := hwid.2 (by omega)
        have hnode : (A.getD i default).node = y0 := end_of_stepPairs hwi.1.1 hp0.1 (by rw [← hwi.2, h1])
        have hmem : i ∈ List.range' lo (hi - lo) := by rw [List.mem_range'_1]; omega
        obtain ⟨L, -, hL⟩ := forall₂_mem_left hLs i hmem
        have hin : (s.2, q) ∈ L := (hx _ _ L hL s.2 q).2 ⟨s.1, hnode ▸ hR, h2 ▸ hstep⟩
        have htn : trailNew c A i (s.2, q) =
            some { node := s.2.to, state := q, parent := some i, hop := some s.2.hop, tau := τ } := by
          unfold trailNew
          simp only
          rw [h3, htau]
          simp only
          rw [if_neg (by rw [h1, stepPairs_ids]; exact hid)]
        have hnew := mem_layerNew_of hLs hPfun hmem hL hin htn
        obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 hnew
        have hgk := hget k hk
        rw [hke] at hgk
        refine ⟨A.size + k, by show A.size + k < A'.size; omega, ?_, by rw [hgk], by rw [hgk]⟩
        have hp : (A'.getD (A.size + k) default).parent = some i := by rw [hgk]
        have hh : (A'.getD (A.size + k) default).hop = some s.2.hop := by rw [hgk]
        rw [steps_link hC' (by omega) hp (by omega) hh, (hE.2 i hiA).2, h1, stepPairs_append, hgk]
        simp [stepPairs, hto]
  have hkeys := layerNew_keys_nodup (c := c) (A := A) hLs List.nodup_range' (fun i L hL => hnd _ _ L hL)
  -- each partial trail has one node
  have huniq : ∀ i j, i < A'.size → j < A'.size → steps A' i = steps A' j → i = j := by
    intro i j hi' hj' hij
    obtain ⟨wi, hwi, hwil, hwi'⟩ := hrep i hi'
    obtain ⟨wj, hwj, hwjl, hwj'⟩ := hrep j hj'
    have hl := hwi.length_eq hwj hij
    by_cases hiA : i < A.size
    · by_cases hjA : j < A.size
      · exact hI.uniq i j hiA hjA (by rw [← (hE.2 i hiA).2, ← (hE.2 j hjA).2, hij])
      · exfalso; have := hwj'.1 (by omega); have := hwi'.2 (by omega); omega
    · by_cases hjA : j < A.size
      · exfalso; have := hwi'.1 (by omega); have := hwj'.2 (by omega); omega
      · obtain ⟨k1, rfl⟩ : ∃ k, i = A.size + k := ⟨i - A.size, by omega⟩
        obtain ⟨k2, rfl⟩ : ∃ k, j = A.size + k := ⟨j - A.size, by omega⟩
        have hk1 : k1 < (layerNew c A (List.range' lo (hi - lo)) Ls).length := by omega
        have hk2 : k2 < (layerNew c A (List.range' lo (hi - lo)) Ls).length := by omega
        have hg1 := hget k1 hk1
        have hg2 := hget k2 hk2
        obtain ⟨p1, hp1, hp1', -, -, a1, -, he1⟩ := trail_new_origin hsize hLs hlist (by omega) hi'
        obtain ⟨p2, hp2, hp2', -, -, a2, -, he2⟩ := trail_new_origin hsize hLs hlist (by omega) hj'
        obtain ⟨_, _, _, he1'⟩ := trailNew_spec he1
        obtain ⟨_, _, _, he2'⟩ := trailNew_spec he2
        have hs1 : steps A' (A.size + k1) = steps A p1 ++ [(a1.1.hop, a1.1.to)] := by
          rw [steps_link hC' hi' (by rw [he1']) (by omega) (by rw [he1']), (hE.2 p1 (by omega)).2, he1']
        have hs2 : steps A' (A.size + k2) = steps A p2 ++ [(a2.1.hop, a2.1.to)] := by
          rw [steps_link hC' hj' (by rw [he2']) (by omega) (by rw [he2']), (hE.2 p2 (by omega)).2, he2']
        rw [hs1, hs2] at hij
        obtain ⟨hpp, hlast⟩ := List.append_inj' hij rfl
        have hp12 : p1 = p2 := hI.uniq p1 p2 (by omega) (by omega) hpp
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hlast
        have hk : ((layerNew c A (List.range' lo (hi - lo)) Ls).map fun e => (e.parent, e.hop))[k1]'(by simpa using hk1) =
            ((layerNew c A (List.range' lo (hi - lo)) Ls).map fun e => (e.parent, e.hop))[k2]'(by simpa using hk2) := by
          simp only [List.getElem_map, ← hg1, ← hg2, he1', he2', hp12, hlast.1]
        have := (List.Nodup.getElem_inj_iff hkeys).1 hk
        omega
  refine ⟨hC', rfl, by omega, hrep, hcomplete, huniq, ?_, within_succ hok, hus, hle, fun hlt' => ?_⟩
  · rw [hI.rowsEq]
    have hsz' : A'.size = A.size + (A'.size - hi) := by omega
    conv_rhs => rw [hsz']
    rw [List.range_add, List.filterMap_append, List.filterMap_map]
    congr 1
    · apply List.filterMap_congr
      intro i hi'
      rw [List.mem_range] at hi'
      unfold trailRowAt
      rw [(hE.2 i hi').1, (hE.2 i hi').2]
    · apply List.filterMap_congr
      intro k hk
      rw [List.mem_range] at hk
      simp only [Function.comp_apply, trailRowAt]
      rw [stepsOf_eq hC' (hi + k) (by omega) _ (by omega) [], List.append_nil, hsize]
  · have := hI.fuel hlt; have := hI.usedEq; omega

/-- The TRAIL loop ends in a state satisfying the invariant whose layer is empty or whose depth is
the hop bound; the fuel never runs out first. -/
theorem trailLoop_inv {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} (hx : HopsExact st c R)
    (hnd : HopsNodup st c) :
    ∀ (fuel : Nat) (A : Array TNode) (lo hi depth used : Nat) (rows res : List PathRow),
      TrailInv R c x A lo hi depth used rows → c.limit + 1 ≤ fuel + depth →
      ev st (trailLoop c x fuel A lo hi depth used rows) = .ok (.ok res) →
      ∃ (A' : Array TNode) (lo' hi' depth' used' : Nat),
        TrailInv R c x A' lo' hi' depth' used' res ∧ (hi' ≤ lo' ∨ c.depthOk depth' = false)
  | 0, A, lo, hi, depth, used, rows, res, hI, hf, h => by
    simp only [trailLoop] at h
    cases ev_pure_inj h
    refine ⟨A, lo, hi, depth, used, hI, .inl ?_⟩
    by_contra hlt
    have := hI.fuel (by omega); have := hI.usedLe; omega
  | fuel + 1, A, lo, hi, depth, used, rows, res, hI, hf, h => by
    simp only [trailLoop] at h
    split at h
    · rename_i hc
      cases ev_pure_inj h
      refine ⟨A, lo, hi, depth, used, hI, ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      exact hc
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Bool.not_eq_false,
        Nat.not_le] at hc
      obtain ⟨⟨A', used'⟩, hl, h⟩ := ev_bind_ok h
      exact trailLoop_inv hx hnd fuel _ _ _ _ _ _ res (trailInv_step hx hnd hI hc.1 hc.2 hl) (by omega) h

/-- A prefix of a partial trail is a partial trail. -/
theorem partial_prefix {R : HopRel} {c : Ctx} {x y : Int64} {u v : List Step} {q : Nat} {τ : Option Int}
    (h : Partial R c x (u ++ v) y q τ) : ∃ y' q' τ', Partial R c x u y' q' τ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨y', hu, -⟩ := (isWalk_append ..).1 h1
  rw [word_append, runL_append] at h2
  rw [walkTau_append] at h4
  cases hq : c.dfa.runL 0 (word u) with
  | none => rw [hq] at h2; cases h2
  | some q' =>
    cases ht : walkTau c u (c.timed.getD none) with
    | none => rw [ht] at h4; cases h4
    | some τ' =>
      unfold IsTrail at h3; rw [List.map_append, List.nodup_append] at h3
      exact ⟨y', q', τ', hu, hq, h3.1, ht⟩

/-- A path value determines the steps of its row. -/
theorem rowOf_path_inj {c c' : Ctx} {x x' : Int64} {s s' : List (Hop × Int64)} {τ τ' : Option Int}
    (h : (rowOf c x s τ).path = (rowOf c' x' s' τ').path) : s = s' := by
  simp only [rowOf, Option.some.injEq, PathValue.mk.injEq, List.cons.injEq] at h
  rw [← List.zip_unzip s, ← List.zip_unzip s']
  simp only [List.unzip_fst, List.unzip_snd]
  rw [h.1.2, h.2]

theorem nodup_filterMap_of_injOn {α β : Type} (f : α → Option β) :
    ∀ (l : List α), l.Nodup → (∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') →
      (l.filterMap f).Nodup
  | [], _, _ => by simp
  | a :: l, hl, h => by
    have ih := nodup_filterMap_of_injOn f l (List.nodup_cons.1 hl).2
      (fun a1 h1 a2 h2 b => h a1 (List.mem_cons_of_mem _ h1) a2 (List.mem_cons_of_mem _ h2) b)
    rw [List.filterMap_cons]
    cases hf : f a with
    | none => exact ih
    | some b =>
      refine List.nodup_cons.2 ⟨fun hb => ?_, ih⟩
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.1 hb
      have := h a (List.mem_cons_self ..) a' (List.mem_cons_of_mem _ ha') b hf hfa'
      subst this
      exact (List.nodup_cons.1 hl).1 ha'

/-- path-evaluation "Trail mode" (and the time-respecting TRAIL of "Time-respecting evaluation"):
when the hop layer lists exactly the hops of `R`, each once, and the automaton is compiled from
`e`, a successful TRAIL search from `x` returns exactly the rows of the trails `w` of `R` from `x`
(no repeated hop identity) whose word is in `lang e`, whose length is within the hop bound and
whose hops the hop rule allows from the start instant (always, when not time-respecting), each
with its path value and arrival; no path value repeats. -/
theorem trail_spec {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hx : HopsExact st c R) (hnd : HopsNodup st c) (hd : buildDfa (toRE false e) = .ok c.dfa)
    {rows : List PathRow} (h : ev st (trail c x) = .ok (.ok rows)) :
    (∀ r, r ∈ rows ↔ ∃ y w τ, IsWalk R x w y ∧ IsTrail w ∧ word w ∈ lang e ∧ Within c.maxHops w.length ∧
      walkTau c w (c.timed.getD none) = some τ ∧ r = walkRow c x w τ) ∧
    (rows.map PathRow.path).Nodup := by
  unfold trail at h
  obtain ⟨u, hu, h⟩ := ev_bind_ok h
  obtain ⟨rfl, hul⟩ := charge_ok hu
  let A0 : Array TNode := #[{ node := x, state := 0, parent := none, hop := none, tau := c.timed.getD none }]
  have hC0 : Chain A0 := ⟨by simp [A0], ⟨rfl, rfl⟩, fun i h1 h2 => by simp [A0] at h2; omega⟩
  have hI : TrailInv R c x A0 0 1 0 (0 + 1)
      (if c.dfa.accepts 0 then [rowOf c x [] (c.timed.getD none)] else []) := by
    refine ⟨hC0, rfl, by omega, fun i hi => ?_, fun w y q τ hw hwl => ?_, fun i j hi hj _ => ?_, ?_,
      fun m _ => Nat.zero_le m, by simp [A0], hul, fun _ => le_refl _⟩
    · have : i = 0 := by simp [A0] at hi; omega
      subst this
      exact ⟨[], ⟨⟨rfl, rfl, List.nodup_nil, rfl⟩, steps_zero hC0⟩, le_refl _, by simp⟩
    · have : w = [] := List.length_eq_zero_iff.1 (by omega)
      subst this
      obtain ⟨h1, h2, -, h4⟩ := hw
      simp only [isWalk_nil, word_nil, Dfa.runL, walkTau, Option.some.injEq] at h1 h2 h4
      subst h1; subst h2; subst h4
      exact ⟨0, by simp [A0], by rw [steps_zero hC0]; rfl, rfl, rfl⟩
    · simp [A0] at hi hj; omega
    · show _ = (List.range 1).filterMap (trailRowAt c x A0)
      simp only [List.range_one, List.filterMap_cons, List.filterMap_nil, trailRowAt, steps_zero hC0]
      rw [show A0.getD 0 default = { node := x, state := 0, parent := none, hop := none, tau := c.timed.getD none }
        from rfl]
      by_cases ha : c.dfa.accepts 0 = true <;> simp [ha]
  obtain ⟨A, lo, hi, dep, used, hF, hend⟩ := trailLoop_inv hx hnd _ _ _ _ _ _ _ rows hI (by omega) h
  -- every partial trail within the bound is at most `dep` hops long
  have hlen : ∀ w y q τ, Partial R c x w y q τ → Within c.maxHops w.length → w.length ≤ dep := by
    intro w y q τ hw hb
    rcases hend with hlo | hdep
    · by_contra hlt
      push Not at hlt
      obtain ⟨y', q', τ', hp⟩ := partial_prefix (u := w.take dep) (v := w.drop dep) (by rw [List.take_append_drop]; exact hw)
      obtain ⟨i, hi', hs, -, -⟩ := hF.complete _ y' q' τ' hp (by simp)
      obtain ⟨wi, hwi, -, hwid⟩ := hF.rep i hi'
      have : wi.length = dep := by
        rw [← length_stepPairs, ← hwi.2, hs, length_stepPairs, List.length_take]; omega
      have := hwid.2 this
      have := hF.size; omega
    · cases hm : c.maxHops with
      | none => simp [Ctx.depthOk, hm] at hdep
      | some m =>
        simp only [Ctx.depthOk, hm, Option.all_some, decide_eq_false_iff_not, Nat.not_lt] at hdep
        have := hF.bound m hm; have := hb m hm; omega
  refine ⟨fun r => ?_, ?_⟩
  · rw [hF.rowsEq, List.mem_filterMap]
    constructor
    · rintro ⟨i, hi', hr⟩
      rw [List.mem_range] at hi'
      by_cases hacc : c.dfa.accepts (A.getD i default).state = true
      · rw [trailRowAt, if_pos hacc, Option.some.injEq] at hr
        subst hr
        obtain ⟨w, ⟨⟨h1, h2, h3, h4⟩, h5⟩, hwl, -⟩ := hF.rep i hi'
        refine ⟨_, w, _, h1, h3, (match_iff_run hd w).2 ⟨_, h2, hacc⟩,
          fun m hm => by have := hF.bound m hm; omega, h4, ?_⟩
        unfold walkRow; rw [h5]
      · rw [trailRowAt, if_neg hacc] at hr; cases hr
    · rintro ⟨y, w, τ, h1, h3, hl, hb, h4, rfl⟩
      obtain ⟨q, hq, hacc⟩ := (match_iff_run hd w).1 hl
      have hp : Partial R c x w y q τ := ⟨h1, hq, h3, h4⟩
      obtain ⟨i, hi', hs, hst, hta⟩ := hF.complete w y q τ hp (hlen w y q τ hp hb)
      refine ⟨i, List.mem_range.2 hi', ?_⟩
      unfold trailRowAt walkRow
      rw [hst, if_pos hacc, hs, hta]
  · rw [hF.rowsEq, List.map_filterMap]
    refine nodup_filterMap_of_injOn _ _ List.nodup_range fun i hi j hj p h1 h2 => ?_
    rw [List.mem_range] at hi hj
    by_cases ha : c.dfa.accepts (A.getD i default).state = true
    · by_cases hb : c.dfa.accepts (A.getD j default).state = true
      · rw [trailRowAt, if_pos ha, Option.map_some, Option.some.injEq] at h1
        rw [trailRowAt, if_pos hb, Option.map_some, Option.some.injEq] at h2
        exact hF.uniq i j hi hj (rowOf_path_inj (h1.trans h2.symm))
      · rw [trailRowAt, if_neg hb, Option.map_none] at h2; cases h2
    · rw [trailRowAt, if_neg ha, Option.map_none] at h1; cases h1

/-! ## Fuel -/

/-- path-evaluation "Termination and search bound" (TRAIL): every arena node is a charged search
state and a layer is non-empty only after a charged one, so the TRAIL loop with fuel `f`
(`f + depth ≥ pathMaxStates + 1`, as for the initial call) has the same outcome as with any larger
fuel. -/
theorem trailLoop_fuel {st : ModelState} {c : Ctx} {x : Int64} :
    ∀ (f k : Nat) (A : Array TNode) (lo hi depth used : Nat) (rows : List PathRow),
      Chain A → hi = A.size → lo ≤ hi → used = A.size → used ≤ c.limit → (lo < hi → depth + 1 ≤ used) →
      c.limit + 1 ≤ f + depth →
      ev st (trailLoop c x f A lo hi depth used rows) = ev st (trailLoop c x (f + k) A lo hi depth used rows)
  | 0, k, A, lo, hi, depth, used, rows, hC, hs, hlh, hu, hle, hfu, hf => by
    have hlo : hi ≤ lo := by
      by_contra hlt; have := hfu (by omega); omega
    cases k with
    | zero => rfl
    | succ k => simp [trailLoop, hlo]
  | f + 1, k, A, lo, hi, depth, used, rows, hC, hs, hlh, hu, hle, hfu, hf => by
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [trailLoop]
    split
    · rfl
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Bool.not_eq_false,
        Nat.not_le] at hc
      apply ev_bind_congr
      rintro ⟨A', used'⟩ hl
      obtain ⟨-, -, hC', hE, hus, hle', -⟩ := trailExtend_fold hC (List.range' lo (hi - lo)) A used (A', used')
        (fun i hi' => by rw [List.mem_range'_1] at hi'; omega) hC (AExt.refl A) hu hle hl
      simp only at hC' hE hus hle'
      exact trailLoop_fuel f k A' hi A'.size (depth + 1) used' _ hC' rfl (by have := hE.1; omega) hus hle'
        (fun hlt => by have := hfu hc.1; omega) (by omega)

end Tiramemsu.Path
