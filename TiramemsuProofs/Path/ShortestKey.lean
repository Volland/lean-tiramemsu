/-
path-evaluation "Shortest modes", ANY_SHORTEST's choice: among the matching walks of minimal length
to an end, the returned one has the least hop-key sequence (hop keys ordered by eid, then stored
before virtual, then forward before inverse; sequences compared lexicographically).

The proof orders the arena: a node's first path (through its one predecessor) is the least
shortest path to its search state, and the nodes of a layer come in increasing order of their
first paths, because a layer is expanded parent by parent, each parent's transitions sorted by hop
key, and a node is created by the first transition reaching it.
-/
import TiramemsuProofs.Path.Shortest

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## The order of hop keys -/

abbrev HKey := Int × Nat × Nat

theorem keyLt_iff (a b : HKey) : keyLt a b = true ↔
    a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2))) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp [keyLt]

theorem keyLt_irrefl (a : HKey) : keyLt a a = false := by
  cases h : keyLt a a
  · rfl
  · rw [keyLt_iff] at h; omega

theorem keyLt_trans {a b c : HKey} (h1 : keyLt a b = true) (h2 : keyLt b c = true) : keyLt a c = true := by
  rw [keyLt_iff] at *; omega

theorem keyLt_asymm {a b : HKey} (h : keyLt a b = true) : keyLt b a = false := by
  cases h' : keyLt b a
  · rfl
  · rw [keyLt_iff] at h h'; omega

theorem keyLt_total {a b : HKey} (h : a ≠ b) : keyLt a b = true ∨ keyLt b a = true := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  rw [keyLt_iff, keyLt_iff]
  simp only [ne_eq, Prod.mk.injEq] at h ⊢
  omega

theorem keyLe_iff (a b : HKey) : keyLe a b = true ↔ keyLt b a = false := by
  simp [keyLe]

theorem keyLe_refl (a : HKey) : keyLe a a = true := by rw [keyLe_iff, keyLt_irrefl]

theorem keyLe_trans {a b c : HKey} (h1 : keyLe a b = true) (h2 : keyLe b c = true) : keyLe a c = true := by
  rw [keyLe_iff] at *
  cases h : keyLt c a
  · rfl
  · by_cases hab : a = b
    · subst hab; rw [h] at h2; cases h2
    · rcases keyLt_total hab with h' | h'
      · exact absurd (keyLt_trans h h') (by rw [h2]; simp)
      · rw [h'] at h1; cases h1

theorem keyLe_total (a b : HKey) : keyLe a b = true ∨ keyLe b a = true := by
  rw [keyLe_iff, keyLe_iff]
  cases h : keyLt b a
  · exact .inl rfl
  · exact .inr (keyLt_asymm h)

theorem keyLe_antisymm {a b : HKey} (h1 : keyLe a b = true) (h2 : keyLe b a = true) : a = b := by
  by_contra hne
  rw [keyLe_iff] at h1 h2
  rcases keyLt_total hne with h | h
  · rw [h] at h2; cases h2
  · rw [h] at h1; cases h1

/-! ## The lexicographic order of hop-key sequences -/

theorem keysLe_refl : ∀ a : List HKey, keysLe a a = true
  | [] => rfl
  | x :: a => by simp [keysLe, keyLt_irrefl, keysLe_refl a]

theorem keysLe_cons (x y : HKey) (a b : List HKey) :
    keysLe (x :: a) (y :: b) = true ↔ keyLt x y = true ∨ (x = y ∧ keysLe a b = true) := by
  simp only [keysLe]
  by_cases h1 : keyLt x y = true
  · simp [h1]
  · by_cases h2 : keyLt y x = true
    · have hxy : x ≠ y := by rintro rfl; rw [keyLt_irrefl] at h2; exact absurd h2 (by simp)
      simp [h1, h2, hxy]
    · have hxy : x = y := by
        by_contra hne; rcases keyLt_total hne with h | h; exact h1 h; exact h2 h
      subst hxy
      simp [keyLt_irrefl]

theorem keysLe_antisymm : ∀ {a b : List HKey}, keysLe a b = true → keysLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [keysLe] at h
  | _ :: _, [], h, _ => by simp [keysLe] at h
  | x :: a, y :: b, h1, h2 => by
    rw [keysLe_cons] at h1 h2
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, -⟩
      · rw [keyLt_asymm h1] at h2; cases h2
      · rw [keyLt_irrefl] at h1; cases h1
    · rcases h2 with h2 | ⟨-, h2⟩
      · rw [keyLt_irrefl] at h2; cases h2
      · rw [keysLe_antisymm h1 h2]

theorem keysLe_trans : ∀ {a b c : List HKey}, keysLe a b = true → keysLe b c = true → keysLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [keysLe] at h
  | _ :: _, _ :: _, [], _, h => by simp [keysLe] at h
  | x :: a, y :: b, z :: c, h1, h2 => by
    rw [keysLe_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact .inl (keyLt_trans h1 h2)
      · exact .inl h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact .inl h2
      · exact .inr ⟨rfl, keysLe_trans h1 h2⟩

theorem keysLe_total : ∀ a b : List HKey, keysLe a b = true ∨ keysLe b a = true
  | [], _ => .inl rfl
  | _ :: _, [] => .inr rfl
  | x :: a, y :: b => by
    rw [keysLe_cons, keysLe_cons]
    by_cases hxy : x = y
    · subst hxy
      rcases keysLe_total a b with h | h
      · exact .inl (.inr ⟨rfl, h⟩)
      · exact .inr (.inr ⟨rfl, h⟩)
    · rcases keyLt_total hxy with h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)

/-- A strictly smaller sequence stays smaller whatever follows (equal lengths). -/
theorem keysLe_append_of_ne : ∀ {a b : List HKey} (u v : List HKey), a.length = b.length →
    keysLe a b = true → a ≠ b → keysLe (a ++ u) (b ++ v) = true
  | [], [], _, _, _, _, hne => absurd rfl hne
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | x :: a, y :: b, u, v, hl, h, hne => by
    simp only [List.cons_append]
    rw [keysLe_cons] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact .inl h
    · exact .inr ⟨rfl, keysLe_append_of_ne u v (by simpa using hl) h (fun h' => hne (by rw [h']))⟩

theorem keysLe_append_same : ∀ (a u v : List HKey), keysLe (a ++ u) (a ++ v) = keysLe u v
  | [], u, v => rfl
  | x :: a, u, v => by
    simp only [List.cons_append, keysLe, keyLt_irrefl]
    exact keysLe_append_same a u v

theorem keysLe_singleton (x y : HKey) : keysLe [x] [y] = keyLe x y := by
  simp only [keysLe, keyLe]
  cases h1 : keyLt x y <;> cases h2 : keyLt y x
  · rfl
  · rfl
  · rfl
  · rw [keyLt_asymm h1] at h2; cases h2

/-! ## Sorted expansions and the order of a layer's transitions -/

/-- The transitions of a search state come sorted by hop key. -/
theorem expandOne_sorted {st : ModelState} {c : Ctx} {x : Int64} {q : Nat} {L : List (Nb × Nat)}
    (h : ev st (expandOne c x q) = .ok (.ok L)) :
    L.Pairwise (fun a b => keyLe a.1.hop.key b.1.hop.key = true) := by
  unfold expandOne at h
  obtain ⟨parts, -, h⟩ := ev_bind_ok h
  cases ev_pure_inj h
  exact List.pairwise_mergeSort (le := fun a b : Nb × Nat => keyLe a.1.hop.key b.1.hop.key)
    (fun a b c h1 h2 => keyLe_trans h1 h2)
    (fun a b => by rcases keyLe_total a.1.hop.key b.1.hop.key with h | h <;> simp [h]) _

/-- The order in which a layer's transitions are processed: by parent, then by hop key. -/
def TransLe (a b : Nat × (Nb × Nat)) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ keyLe a.2.1.hop.key b.2.1.hop.key = true)

theorem layerTrans_sorted {P : Nat → List (Nb × Nat) → Prop}
    (hP : ∀ j L, P j L → L.Pairwise (fun a b => keyLe a.1.hop.key b.1.hop.key = true)) :
    ∀ {layer : List Nat} {Ls : List (List (Nb × Nat))}, List.Forall₂ P layer Ls → layer.Pairwise (· < ·) →
      (layerTrans layer Ls).Pairwise TransLe
  | _, _, .nil, _ => by simp [layerTrans]
  | j :: layer, L :: Ls, .cons hp hr, hs => by
    simp only [layerTrans, List.zipWith_cons_cons, List.flatten_cons]
    rw [List.pairwise_append]
    refine ⟨?_, layerTrans_sorted hP hr (List.pairwise_cons.1 hs).2, fun a ha b hb => ?_⟩
    · rw [List.pairwise_map]
      exact (hP j L hp).imp fun h => .inr ⟨rfl, h⟩
    · obtain ⟨a', -, rfl⟩ := List.mem_map.1 ha
      have hb' := layerTrans_parent layer Ls b hb
      exact .inl ((List.pairwise_cons.1 hs).1 _ hb')

/-! ## Creation order of a layer's nodes -/

/-- The position of the first processed transition reaching search state `p`. -/
def firstIdx (P : List (Nat × (Nb × Nat))) (p : SState) : Nat := P.findIdx fun a => tgt a == p

theorem firstIdx_lt {P : List (Nat × (Nb × Nat))} {p : SState} (h : ∃ a ∈ P, tgt a = p) : firstIdx P p < P.length :=
  List.findIdx_lt_length_of_exists (by obtain ⟨a, ha, h⟩ := h; exact ⟨a, ha, by simp [h]⟩)

theorem firstIdx_append {P : List (Nat × (Nb × Nat))} {p : SState} (h : ∃ a ∈ P, tgt a = p)
    (Q : List (Nat × (Nb × Nat))) : firstIdx (P ++ Q) p = firstIdx P p := by
  have hl := firstIdx_lt h
  unfold firstIdx at hl ⊢; rw [List.findIdx_append, if_pos hl]

theorem firstIdx_new {P : List (Nat × (Nb × Nat))} {a : Nat × (Nb × Nat)} (h : ∀ b ∈ P, tgt b ≠ tgt a) :
    firstIdx (P ++ [a]) (tgt a) = P.length := by
  unfold firstIdx
  rw [List.findIdx_append]
  have : P.findIdx (fun b => tgt b == tgt a) = P.length :=
    List.findIdx_eq_length.2 (fun b hb => by simpa using h b hb)
  rw [this, if_neg (lt_irrefl _)]
  simp

/-- The nodes of a layer are created in the order of their first transitions. -/
def SOrder (A0 : Array SNode) (P : List (Nat × (Nb × Nat))) (acc : SAcc) : Prop :=
  ∀ i j, A0.size ≤ i → i < j → j < acc.arena.size →
    firstIdx P (skey (acc.arena.getD i default)) < firstIdx P (skey (acc.arena.getD j default))

theorem shortestStep_order {st : ModelState} {c : Ctx} (hT : c.timed = none) {all : Bool}
    {best : Std.HashMap SState (Option Int)} {k parent : Nat} {pn : SNode}
    {A0 : Array SNode} {I0 : Std.HashMap SState Nat} {used0 : Nat}
    {P : List (Nat × (Nb × Nat))} {acc acc' : SAcc} {a : Nb × Nat}
    (hS : SLayer c all k A0 I0 used0 P acc) (hO : SOrder A0 P acc)
    (h : ev st (shortestStep c all best k parent pn acc a) = .ok (.ok acc')) :
    SOrder A0 (P ++ [(parent, a)]) acc' := by
  obtain ⟨nb, t⟩ := a
  have hocc : ∀ i, A0.size ≤ i → i < acc.arena.size → ∃ b ∈ P, tgt b = skey (acc.arena.getD i default) :=
    fun i h1 h2 => (hS.new i h1 h2).2.2.2.1
  have hkey_new : ∀ i, A0.size ≤ i → i < acc.arena.size → acc.index[skey (acc.arena.getD i default)]? = some i :=
    fun i h1 h2 => (hS.index _ i).2 (.inr ⟨h1, h2, rfl⟩)
  have hsame : ∀ i j, A0.size ≤ i → i < j → j < acc.arena.size →
      firstIdx (P ++ [(parent, (nb, t))]) (skey (acc.arena.getD i default)) <
        firstIdx (P ++ [(parent, (nb, t))]) (skey (acc.arena.getD j default)) := by
    intro i j h1 h2 h3
    rw [firstIdx_append (hocc i h1 (by omega)), firstIdx_append (hocc j (by omega) h3)]
    exact hO i j h1 h2 h3
  unfold shortestStep at h
  simp only [hT] at h
  cases hj : acc.index.get? (nb.to, t) with
  | none =>
    rw [hj] at h; simp only at h
    rw [Std.HashMap.get?_eq_getElem?] at hj
    obtain ⟨u, hu, h⟩ := ev_bind_ok h
    obtain ⟨rfl, -⟩ := charge_ok hu
    cases ev_pure_inj h
    have hnotP : ∀ b ∈ P, tgt b ≠ tgt (parent, (nb, t)) := by
      intro b hb heq; obtain ⟨i, hi⟩ := hS.done b hb; rw [heq] at hi
      simp only [tgt] at hi; rw [hj] at hi; cases hi
    intro i j h1 h2 h3
    simp only [Array.size_push] at h3
    rw [getD_push_lt _ _ _ (by omega)]
    by_cases hj' : j < acc.arena.size
    · rw [getD_push_lt _ _ _ hj']; exact hsame i j h1 h2 hj'
    · have : j = acc.arena.size := by omega
      subst this
      rw [getD_push_eq]
      have hn := firstIdx_new hnotP
      have hi := firstIdx_append (hocc i h1 (by omega)) [(parent, (nb, t))]
      have hlt := firstIdx_lt (hocc i h1 (by omega))
      have hn' : firstIdx (P ++ [(parent, (nb, t))]) (nb.to, t) = P.length := hn
      show _ < firstIdx (P ++ [(parent, (nb, t))]) (nb.to, t)
      rw [hn', hi]; exact hlt
  | some j =>
    rw [hj] at h; simp only at h
    split at h
    · obtain ⟨u, hu, h⟩ := ev_bind_ok h
      obtain ⟨rfl, -⟩ := charge_ok hu
      cases ev_pure_inj h
      intro i j' h1 h2 h3
      simp only [Array.size_modify] at h3
      have hk : ∀ m, skey ((acc.arena.modify j fun n => { n with preds := n.preds ++ [(parent, nb.hop)] }).getD m default)
          = skey (acc.arena.getD m default) := by
        intro m; rw [getD_modify]; split <;> rfl
      simp only
      rw [hk, hk]
      exact hsame i j' h1 h2 h3
    · cases ev_pure_inj h
      exact hsame

theorem shortestExpand_order {st : ModelState} {c : Ctx} (hT : c.timed = none) {all : Bool}
    {best : Std.HashMap SState (Option Int)} {k : Nat} {A0 : Array SNode} {I0 : Std.HashMap SState Nat}
    {used0 : Nat} (hd0 : ∀ i < A0.size, (A0.getD i default).depth ≤ k)
    (hI0 : ∀ (p : SState) (i : Nat), I0[p]? = some i → i < A0.size) :
    ∀ (layer : List Nat) (P : List (Nat × (Nb × Nat))) (acc res : SAcc),
      (∀ i ∈ layer, i < A0.size) → SLayer c all k A0 I0 used0 P acc → SOrder A0 P acc →
      ev st (layer.foldlM (shortestExpand c all best k) acc) = .ok (.ok res) →
      ∃ Ls : List (List (Nb × Nat)),
        List.Forall₂ (fun i L => ev st (expandOne c (A0.getD i default).node (A0.getD i default).state) =
          .ok (.ok L)) layer Ls ∧
        SLayer c all k A0 I0 used0 (P ++ layerTrans layer Ls) res ∧ SOrder A0 (P ++ layerTrans layer Ls) res
  | [], P, acc, res, _, hS, hO, h => by
    simp only [List.foldlM_nil] at h
    cases ev_pure_inj h
    exact ⟨[], .nil, by simpa [layerTrans] using hS, by simpa [layerTrans] using hO⟩
  | i :: layer, P, acc, res, hl, hS, hO, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h2⟩ := ev_bind_ok h
    have hi : i < A0.size := hl i (List.mem_cons_self ..)
    unfold shortestExpand at h1
    simp only at h1
    rw [hS.old i hi] at h1
    obtain ⟨L, hL, h1⟩ := ev_bind_ok h1
    have hS1 := ev_foldlM_pre st (shortestStep c all best k i (A0.getD i default))
      (fun done acc => SLayer c all k A0 I0 used0 (P ++ done.map (i, ·)) acc ∧ SOrder A0 (P ++ done.map (i, ·)) acc)
      (fun done b a b' hb hs => by
        have h1 := shortestStep_layer hT hd0 hI0 hb.1 hs
        have h2 := shortestStep_order hT hb.1 hb.2 hs
        exact ⟨by simpa using h1, by simpa using h2⟩) L [] acc acc1 ⟨by simpa using hS, by simpa using hO⟩ h1
    simp only [List.nil_append] at hS1
    obtain ⟨Ls, hLs, hres, hord⟩ := shortestExpand_order hT hd0 hI0 layer _ acc1 res
      (fun j hj => hl j (List.mem_cons_of_mem _ hj)) hS1.1 hS1.2 h2
    refine ⟨L :: Ls, .cons hL hLs, ?_, ?_⟩
    · simpa [layerTrans] using hres
    · simpa [layerTrans] using hord

/-! ## Paths of an extended arena -/

theorem pathsTo_congr {A A' : Array SNode} {j : Nat}
    (hag : ∀ m ≤ j, A'.getD m default = A.getD m default)
    (hpred : ∀ m ≤ j, ∀ jh ∈ (A.getD m default).preds, jh.1 < m) :
    ∀ f, pathsTo A' f j = pathsTo A f j := by
  intro f
  induction f generalizing j with
  | zero => rfl
  | succ f ih =>
    simp only [pathsTo]
    rw [hag j (le_refl _)]
    split
    · rfl
    · apply List.flatMap_congr
      rintro ⟨p, h⟩ hph
      have hp := hpred j (le_refl _) _ hph
      rw [ih (j := p) (fun m hm => hag m (by simp at hp; omega)) (fun m hm => hpred m (by simp at hp; omega))]

theorem pathsTo_single {A : Array SNode} {i j : Nat} {h : Hop} (hp : (A.getD i default).preds = [(j, h)]) (f : Nat) :
    pathsTo A (f + 1) i = (pathsTo A f j).map (· ++ [(h, (A.getD i default).node)]) := by
  simp only [pathsTo, hp, List.isEmpty_cons, Bool.false_eq_true, if_false, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem firstIdx_tgt {P : List (Nat × (Nb × Nat))} {p : SState} (h : ∃ a ∈ P, tgt a = p) :
    tgt (P[firstIdx P p]'(firstIdx_lt h)) = p := by
  have := List.findIdx_getElem (p := fun a => tgt a == p) (xs := P) (w := firstIdx_lt h)
  exact beq_iff_eq.1 this

theorem firstIdx_le {P : List (Nat × (Nb × Nat))} {p : SState} {m : Nat} (hm : m < P.length)
    (h : tgt P[m] = p) : firstIdx P p ≤ m := by
  by_contra hlt
  push Not at hlt
  have := List.not_of_lt_findIdx (p := fun a => tgt a == p) (xs := P) hlt
  simp [h] at this

theorem predsOf_any {P : List (Nat × (Nb × Nat))} {p : SState} (h : ∃ a ∈ P, tgt a = p) :
    predsOf false P p = [recPred (P[firstIdx P p]'(firstIdx_lt h))] := by
  unfold predsOf
  simp only [Bool.false_eq_true, if_false]
  have hl := firstIdx_lt h
  unfold firstIdx at hl ⊢
  rw [List.find?_eq_getElem?_findIdx, List.getElem?_eq_getElem hl]
  rfl

/-- A hop key determines the hop from a node (true of a store view: a statement id, kind and
direction determine the hop). -/
def KeyFun (R : HopRel) : Prop :=
  ∀ x l l' nb nb', R x l nb → R x l' nb' → nb.hop.key = nb'.hop.key → nb.hop = nb'.hop

/-- ANY_SHORTEST's order invariant: one predecessor per node; a node's path is the hop-key-least
shortest walk to its search state; the current layer's nodes come in increasing path order. -/
structure AnyKey (R : HopRel) (d : Dfa) (x : Int64) (A : Array SNode) (lo : Nat) : Prop where
  single : ∀ i < A.size, 0 < i → ∃ j h, (A.getD i default).preds = [(j, h)]
  least : ∀ i < A.size, ∀ s ∈ pathsTo A ((A.getD i default).depth + 1) i, ∀ w : List Step,
    w.length = (A.getD i default).depth → IsWalk R x w (A.getD i default).node →
    d.runL 0 (word w) = some (A.getD i default).state → keysLe (hopKeys s) (hopKeys (stepPairs w)) = true
  order : ∀ i j, lo ≤ i → i < j → j < A.size → ∀ s ∈ pathsTo A ((A.getD i default).depth + 1) i,
    ∀ s' ∈ pathsTo A ((A.getD j default).depth + 1) j, keysLe (hopKeys s) (hopKeys s') = true ∧ hopKeys s ≠ hopKeys s'

theorem hopKeys_append (a b : List (Hop × Int64)) : hopKeys (a ++ b) = hopKeys a ++ hopKeys b := by
  simp [hopKeys]

theorem hopKeys_length (a : List (Hop × Int64)) : (hopKeys a).length = a.length := by simp [hopKeys]

theorem pathsTo_eq_of_single {A : Array SNode} (hsingle : ∀ i < A.size, 0 < i → ∃ j h, (A.getD i default).preds = [(j, h)])
    (hroot : (A.getD 0 default).preds = []) (hlt : ∀ i < A.size, ∀ jh ∈ (A.getD i default).preds, jh.1 < i) :
    ∀ f i, i < A.size → ∀ s ∈ pathsTo A f i, ∀ s' ∈ pathsTo A f i, s = s' := by
  intro f
  induction f with
  | zero => intro i _ s hs; simp [pathsTo] at hs
  | succ f ih =>
    intro i hi s hs s' hs'
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [pathsTo, hroot, List.isEmpty_nil, if_true, List.mem_singleton] at hs hs'
      rw [hs, hs']
    · obtain ⟨j, h, hp⟩ := hsingle i hi hpos
      have hj : j < i := hlt i hi (j, h) (by rw [hp]; exact List.mem_singleton_self _)
      rw [pathsTo_single hp] at hs hs'
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hs'
      rw [ih j (by omega) t ht t' ht']

theorem keysLe_snoc {u v : List HKey} {x y : HKey} (hl : u.length = v.length) (h : keysLe u v = true)
    (hxy : keyLe x y = true) : keysLe (u ++ [x]) (v ++ [y]) = true := by
  by_cases huv : u = v
  · subst huv; rw [keysLe_append_same, keysLe_singleton]; exact hxy
  · exact keysLe_append_of_ne _ _ hl h huv

/-- One ANY_SHORTEST layer preserves the order invariant. -/
theorem anyKey_step {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hF : HopFun R)
    (hK : KeyFun R) {x : Int64} {A : Array SNode} {I : Std.HashMap SState Nat} {k lo : Nat}
    (hA : ArenaOK R c.dfa false x A I k) (hlo : ∀ i < A.size, (lo ≤ i ↔ (A.getD i default).depth = k))
    (hAK : AnyKey R c.dfa x A lo) {Ls : List (List (Nb × Nat))}
    (hLs : List.Forall₂ (fun i L => ev st (expandOne c (A.getD i default).node (A.getD i default).state) =
      .ok (.ok L)) (List.range' lo (A.size - lo)) Ls)
    {used0 : Nat} {acc : SAcc}
    (hS : SLayer c false k A I used0 (layerTrans (List.range' lo (A.size - lo)) Ls) acc)
    (hO : SOrder A (layerTrans (List.range' lo (A.size - lo)) Ls) acc)
    (hA' : ArenaOK R c.dfa false x acc.arena acc.index (k + 1))
    (hlo' : ∀ i < acc.arena.size, (A.size ≤ i ↔ (acc.arena.getD i default).depth = k + 1)) :
    AnyKey R c.dfa x acc.arena A.size := by
  set layer := List.range' lo (A.size - lo)
  set P := layerTrans layer Ls
  set A' := acc.arena
  have hfun : ∀ j L L', ev st (expandOne c (A.getD j default).node (A.getD j default).state) = .ok (.ok L) →
      ev st (expandOne c (A.getD j default).node (A.getD j default).state) = .ok (.ok L') → L = L' := by
    intro j L L' h1 h2; rw [h1] at h2; cases h2; rfl
  have hmemP := mem_layerTrans hfun hLs
  have hlay : ∀ j, j ∈ layer ↔ j < A.size ∧ (A.getD j default).depth = k := by
    intro j; rw [List.mem_range'_1]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, (hlo j (by omega)).1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hlo j h1).2 h2, by omega⟩
  have hPstep : ∀ a ∈ P, a.1 ∈ layer ∧ PStep R c.dfa (skey (A.getD a.1 default)) a.2.1 a.2.2 := by
    intro a ha
    obtain ⟨j, hj, L, hL, h1, h2⟩ := (hmemP a).1 ha
    subst h1
    exact ⟨hj, (hx _ _ L hL a.2.1 a.2.2).1 h2⟩
  have hPall : ∀ j ∈ layer, ∀ nb t, PStep R c.dfa (skey (A.getD j default)) nb t → (j, (nb, t)) ∈ P := by
    intro j hj nb t hs
    obtain ⟨L, -, hL⟩ := forall₂_mem_left hLs j hj
    exact (hmemP _).2 ⟨j, hj, L, hL, rfl, (hx _ _ L hL nb t).2 hs⟩
  have hsorted : P.Pairwise TransLe :=
    layerTrans_sorted (fun j L hL => expandOne_sorted hL) hLs (List.pairwise_lt_range' 1 (by omega))
  have hpredlt : ∀ m < A.size, ∀ jh ∈ (A.getD m default).preds, jh.1 < m := by
    intro m hm jh hjh
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [hA.root.2.2] at hjh; cases hjh
    · exact ((hA.preds m hm hpos).sound jh.1 jh.2 hjh).1
  have hold : ∀ j < A.size, ∀ f, pathsTo A' f j = pathsTo A f j := fun j hj =>
    pathsTo_congr (fun m hm => hS.old m (by omega)) (fun m hm => hpredlt m (by omega))
  -- a new node extends the first transition reaching it
  have hnew : ∀ i, A.size ≤ i → i < A'.size → ∃ (hm : firstIdx P (skey (A'.getD i default)) < P.length),
      tgt (P[firstIdx P (skey (A'.getD i default))]'hm) = skey (A'.getD i default) ∧
      (A'.getD i default).preds = [recPred (P[firstIdx P (skey (A'.getD i default))]'hm)] := by
    intro i h1 h2
    obtain ⟨-, -, -, hocc, hpr⟩ := hS.new i h1 h2
    exact ⟨firstIdx_lt hocc, firstIdx_tgt hocc, by rw [hpr]; exact predsOf_any hocc⟩
  -- the path of a new node: its first transition's parent path, extended
  have hnewpath : ∀ i, A.size ≤ i → i < A'.size → ∀ s ∈ pathsTo A' ((A'.getD i default).depth + 1) i,
      ∃ (hm : firstIdx P (skey (A'.getD i default)) < P.length),
        (P[firstIdx P (skey (A'.getD i default))]'hm).1 ∈ layer ∧
        ∃ s0 ∈ pathsTo A (k + 1) (P[firstIdx P (skey (A'.getD i default))]'hm).1,
          s = s0 ++ [((P[firstIdx P (skey (A'.getD i default))]'hm).2.1.hop, (A'.getD i default).node)] := by
    intro i h1 h2 s hs
    obtain ⟨hm, -, hp⟩ := hnew i h1 h2
    have hd : (A'.getD i default).depth = k + 1 := (hlo' i h2).1 h1
    rw [hd, pathsTo_single hp] at hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
    have hl := (hPstep _ (List.getElem_mem hm)).1
    refine ⟨hm, hl, s0, ?_, rfl⟩
    rw [← hold _ ((hlay _).1 hl).1]; exact hs0
  have hsingle : ∀ i < A'.size, 0 < i → ∃ j h, (A'.getD i default).preds = [(j, h)] := by
    intro i hi hpos
    by_cases hlt : i < A.size
    · rw [hS.old i hlt]; exact hAK.single i hlt hpos
    · obtain ⟨hm, -, hp⟩ := hnew i (by omega) hi
      exact ⟨_, _, hp⟩
  have hlen0 : ∀ j, j ∈ layer → ∀ s0 ∈ pathsTo A (k + 1) j, (hopKeys s0).length = k := by
    intro j hj s0 hs0
    obtain ⟨hjA, hjk⟩ := (hlay j).1 hj
    obtain ⟨w, hw1, -, -, rfl⟩ := paths_sound hA j hjA (k + 1) (by omega) s0 hs0
    rw [hopKeys_length, length_stepPairs, hw1, hjk]
  refine ⟨hsingle, fun i hi s hs w hwl hww hwr => ?_, fun i j h1 h2 h3 s hs s' hs' => ?_⟩
  · by_cases hlt : i < A.size
    · rw [hS.old i hlt] at hs hwl hww hwr
      rw [hold i hlt] at hs
      exact hAK.least i hlt s hs w hwl hww hwr
    · obtain ⟨hm, hl, s0, hs0, rfl⟩ := hnewpath i (by omega) hi s hs
      obtain ⟨-, htgt, -⟩ := hnew i (by omega) hi
      have hd : (A'.getD i default).depth = k + 1 := (hlo' i hi).1 (by omega)
      rw [hd] at hwl
      have hne : w ≠ [] := by rintro rfl; simp at hwl
      obtain ⟨w', stp, rfl⟩ : ∃ w' stp, w = w' ++ [stp] :=
        ⟨w.dropLast, w.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      simp only [List.length_append, List.length_singleton] at hwl
      replace hwl : w'.length = k := by omega
      obtain ⟨y', hw', hR, hto⟩ := (isWalk_snoc ..).1 hww
      rw [word_append, runL_append] at hwr
      cases hq : c.dfa.runL 0 (word w') with
      | none => rw [hq] at hwr; cases hwr
      | some q' =>
        rw [hq] at hwr
        simp only [Option.bind_some, word_cons, word_nil, Dfa.runL] at hwr
        have hst : c.dfa.stepL q' stp.1 = some (A'.getD i default).state := by
          cases hs : c.dfa.stepL q' stp.1 with
          | none => rw [hs] at hwr; cases hwr
          | some q'' => rw [hs] at hwr; simpa using hwr
        have hdist := hA'.dist i hi
        rw [hd] at hdist
        have hat : AtDist R c.dfa x k (y', q') := by
          refine ⟨⟨w', hwl, hw', hq⟩, fun m hm hr => hdist.2 (m + 1) (by omega) ?_⟩
          exact (rch_succ R c.dfa x m _).2 ⟨_, hr, stp.2, ⟨stp.1, hR, hst⟩, hto⟩
        obtain ⟨j', hj'⟩ := hA.complete k (le_refl _) _ hat.1
        obtain ⟨hj'A, hj'k⟩ := (hA.index _ j').1 hj'
        have hdj' : (A.getD j' default).depth = k := atDist_unique (hj'k ▸ hA.dist j' hj'A) hat
        have hj'l : j' ∈ layer := (hlay j').2 ⟨hj'A, hdj'⟩
        have hkk : skey (A.getD j' default) = (y', q') := hj'k
        simp only [skey, Prod.mk.injEq] at hkk
        have ha' := hPall j' hj'l stp.2 _ (by simp only [skey, hkk.1, hkk.2]; exact ⟨stp.1, hR, hst⟩)
        obtain ⟨m', hm', hPm'⟩ := List.mem_iff_getElem.1 ha'
        have htgt' : tgt P[m'] = skey (A'.getD i default) := by rw [hPm']; simp [tgt, skey, hto]
        have hmm := firstIdx_le hm' htgt'
        have hleast' : ∀ s1 ∈ pathsTo A (k + 1) j', keysLe (hopKeys s1) (hopKeys (stepPairs w')) = true := by
          intro s1 hs1
          have := hAK.least j' hj'A s1 (by rw [hdj']; exact hs1) w' (by rw [hdj']; exact hwl)
            (by rw [hkk.1]; exact hw') (by rw [hkk.2]; exact hq)
          exact this
        have hw'len : (hopKeys (stepPairs w')).length = k := by rw [hopKeys_length, length_stepPairs, hwl]
        rw [hopKeys_append, stepPairs_append, hopKeys_append]
        have hs0len := hlen0 _ hl s0 hs0
        rcases Nat.lt_or_eq_of_le hmm with hlt' | heq
        · have htr := List.pairwise_iff_getElem.1 hsorted _ _ hm hm' hlt'
          rw [hPm'] at htr
          rcases htr with hpar | ⟨hpar, hkey⟩
          · obtain ⟨s1, hs1⟩ := List.exists_mem_of_ne_nil _ (paths_ne hA j' hj'A (k + 1) (by omega))
            obtain ⟨o1, o2⟩ := hAK.order _ j' (List.mem_range'_1.1 hl).1 hpar hj'A s0
              (by rw [((hlay _).1 hl).2]; exact hs0) s1 (by rw [hdj']; exact hs1)
            have h01 := keysLe_trans o1 (hleast' s1 hs1)
            refine keysLe_append_of_ne _ _ (by rw [hs0len, hw'len]) h01 fun he => o2 ?_
            rw [he] at o1 ⊢
            exact keysLe_antisymm o1 (hleast' s1 hs1)
          · simp only at hpar
            rw [hpar] at hs0
            exact keysLe_snoc (by rw [hs0len, hw'len]) (hleast' s0 hs0) (by simpa [hopKeys] using hkey)
        · have hPeq : P[firstIdx P (skey (A'.getD i default))]'hm = (j', (stp.2, (A'.getD i default).state)) := by
            rw [← hPm']; congr 1
          rw [hPeq] at hs0 ⊢
          exact keysLe_snoc (by rw [hs0len, hw'len]) (hleast' s0 hs0) (keyLe_refl _)
  · obtain ⟨hm1, hl1, s1, hs1, rfl⟩ := hnewpath i h1 (by omega) s hs
    obtain ⟨hm2, hl2, s2, hs2, rfl⟩ := hnewpath j (by omega) h3 s' hs'
    obtain ⟨hm1', htg1, -⟩ := hnew i h1 (by omega)
    obtain ⟨hm2', htg2, -⟩ := hnew j (by omega) h3
    have hord := hO i j h1 h2 h3
    have htr := List.pairwise_iff_getElem.1 hsorted _ _ hm1 hm2 hord
    have hl1len := hlen0 _ hl1 s1 hs1
    have hl2len := hlen0 _ hl2 s2 hs2
    rw [hopKeys_append, hopKeys_append]
    rcases htr with hpar | ⟨hpar, hkey⟩
    · obtain ⟨o1, o2⟩ := hAK.order _ _ (List.mem_range'_1.1 hl1).1 hpar ((hlay _).1 hl2).1 s1
        (by rw [((hlay _).1 hl1).2]; exact hs1) s2 (by rw [((hlay _).1 hl2).2]; exact hs2)
      refine ⟨keysLe_append_of_ne _ _ (by rw [hl1len, hl2len]) o1 o2, fun he => o2 ?_⟩
      exact (List.append_inj' he (by simp [hopKeys])).1
    · rw [hpar] at hs1
      have hs12 : s1 = s2 := pathsTo_eq_of_single hAK.single hA.root.2.2 hpredlt _ _ ((hlay _).1 hl2).1 s1 hs1 s2 hs2
      subst hs12
      refine ⟨by rw [keysLe_append_same]; simp only [hopKeys, List.map_cons, List.map_nil]
                 rw [keysLe_singleton]; exact hkey, fun he => ?_⟩
      have hk := (List.append_inj' he (by simp [hopKeys])).2
      simp only [hopKeys, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hk
      have hp1 := (hPstep _ (List.getElem_mem hm1)).2
      have hp2 := (hPstep _ (List.getElem_mem hm2)).2
      rw [hpar] at hp1
      obtain ⟨l1, hR1, -⟩ := hp1
      obtain ⟨l2, hR2, -⟩ := hp2
      have hh := hK _ _ _ _ _ hR1 hR2 hk
      obtain ⟨hto, ht⟩ := pstep_det hF ((hPstep _ (List.getElem_mem hm1)).2 |> fun h => by rw [hpar] at h; exact h)
        (hPstep _ (List.getElem_mem hm2)).2 hh
      have htt : tgt (P[firstIdx P (skey (A'.getD i default))]'hm1) =
          tgt (P[firstIdx P (skey (A'.getD j default))]'hm2) := Prod.ext hto ht
      have hkeq : skey (A'.getD i default) = skey (A'.getD j default) :=
        htg1.symm.trans (htt.trans htg2)
      have := hA'.key_inj (by omega) h3 hkeq
      omega

/-! ## ANY_SHORTEST rows -/

/-- ANY_SHORTEST collects, for each end, a path of the first target of that end. -/
theorem collectAny_first (arena : Array SNode) (depth : Nat) :
    ∀ (l D : List Nat) (acc : List (List (Hop × Int64) × Option Int) × Std.HashSet Int64),
      (D ++ l).Pairwise (· < ·) →
      (∀ y, acc.2.contains y = true ↔ ∃ i ∈ D, (arena.getD i default).node = y) →
      (∀ z ∈ acc.1, ∃ i ∈ D, z.1 ∈ pathsTo arena (depth + 2) i ∧ z.2 = (arena.getD i default).tau ∧
        ∀ i' ∈ D, (arena.getD i' default).node = (arena.getD i default).node → i ≤ i') →
      ∀ z ∈ (l.foldl (anyStep arena depth) acc).1, ∃ i ∈ D ++ l, z.1 ∈ pathsTo arena (depth + 2) i ∧
        z.2 = (arena.getD i default).tau ∧
        ∀ i' ∈ D ++ l, (arena.getD i' default).node = (arena.getD i default).node → i ≤ i'
  | [], D, acc, _, _, h2 => by simpa using h2
  | i :: l, D, acc, hs, h1, h2 => by
    rw [List.foldl_cons]
    have hlt : ∀ i0 ∈ D, i0 < i := fun i0 hi0 =>
      (List.pairwise_append.1 hs).2.2 i0 hi0 i (List.mem_cons_self ..)
    have := collectAny_first arena depth l (D ++ [i]) (anyStep arena depth acc i) (by simpa using hs) ?_ ?_
    · simpa using this
    · intro y
      unfold anyStep
      simp only
      split
      · rename_i hc
        rw [h1]
        constructor
        · rintro ⟨i0, hi0, h⟩; exact ⟨i0, List.mem_append_left _ hi0, h⟩
        · rintro ⟨i0, hi0, h⟩
          rcases List.mem_append.1 hi0 with hi0 | hi0
          · exact ⟨i0, hi0, h⟩
          · simp only [List.mem_singleton] at hi0; subst hi0; rw [← h]; exact (h1 _).1 hc
      · split <;>
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, h1, List.mem_append,
            List.mem_singleton]
          constructor
          · rintro (h | ⟨i0, hi0, h⟩); exact ⟨i, .inr rfl, h⟩; exact ⟨i0, .inl hi0, h⟩
          · rintro ⟨i0, hi0 | rfl, h⟩; exact .inr ⟨i0, hi0, h⟩; exact .inl h
    · intro z hz
      unfold anyStep at hz
      simp only at hz
      split at hz
      · obtain ⟨i0, hi0, hp, hτ, hmin⟩ := h2 z hz
        refine ⟨i0, List.mem_append_left _ hi0, hp, hτ, fun i' hi' hn => ?_⟩
        rcases List.mem_append.1 hi' with hi' | hi'
        · exact hmin i' hi' hn
        · simp only [List.mem_singleton] at hi'; subst hi'; exact le_of_lt (hlt i0 hi0)
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        have hfresh : ∀ i0 ∈ D, (arena.getD i0 default).node ≠ (arena.getD i default).node := by
          intro i0 hi0 he; have := (h1 _).2 ⟨i0, hi0, he⟩; rw [hc] at this; cases this
        split at hz
        · rename_i p ps hps
          rcases List.mem_append.1 hz with hz | hz
          · obtain ⟨i0, hi0, hp, hτ, hmin⟩ := h2 z hz
            refine ⟨i0, List.mem_append_left _ hi0, hp, hτ, fun i' hi' hn => ?_⟩
            rcases List.mem_append.1 hi' with hi' | hi'
            · exact hmin i' hi' hn
            · simp only [List.mem_singleton] at hi'; subst hi'; exact le_of_lt (hlt i0 hi0)
          · simp only [List.mem_singleton] at hz; subst hz
            refine ⟨i, List.mem_append_right _ (List.mem_singleton_self _), by rw [hps]; exact List.mem_cons_self ..,
              rfl, ?_⟩
            intro i' hi' hn
            rcases List.mem_append.1 hi' with hi' | hi'
            · exact absurd hn (hfresh i' hi')
            · simp only [List.mem_singleton] at hi'; omega
        · obtain ⟨i0, hi0, hp, hτ, hmin⟩ := h2 z hz
          refine ⟨i0, List.mem_append_left _ hi0, hp, hτ, fun i' hi' hn => ?_⟩
          rcases List.mem_append.1 hi' with hi' | hi'
          · exact hmin i' hi' hn
          · simp only [List.mem_singleton] at hi'; subst hi'; exact le_of_lt (hlt i0 hi0)

/-- ANY_SHORTEST rows carry hop-key-least minimal paths. -/
def RowsLeast (R : HopRel) (c : Ctx) (x : Int64) (rows : List PathRow) : Prop :=
  ∀ r ∈ rows, ∃ s, r = rowOf c x s none ∧ ∀ w, MinW R c.dfa x r.end w →
    keysLe (hopKeys s) (hopKeys (stepPairs w)) = true

/-- The state of the ANY_SHORTEST search (not time-respecting), with its order invariant. -/
structure AnyInv (R : HopRel) (c : Ctx) (x : Int64) (A : Array SNode) (I : Std.HashMap SState Nat)
    (E : Std.HashSet Int64) (layer : List Nat) (k used : Nat) (rows : List PathRow) : Prop where
  sh : ShInv R c false x A I E layer k used rows
  key : ∃ lo, layer = List.range' lo (A.size - lo) ∧ AnyKey R c.dfa x A lo
  least : RowsLeast R c x rows

theorem anyInv_step {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hn : HopsNodup st c)
    (hF : HopFun R) (hK : KeyFun R) (hT : c.timed = none) {x : Int64} {A : Array SNode}
    {I : Std.HashMap SState Nat} {best : Std.HashMap SState (Option Int)} {E : Std.HashSet Int64}
    {layer : List Nat} {k used : Nat} {rows : List PathRow} (hI : AnyInv R c x A I E layer k used rows)
    (hne : layer ≠ []) (hok : c.depthOk k = true) {acc : SAcc}
    (hacc : ev st (layer.foldlM (shortestExpand c false best k)
      { arena := A, index := I, used, next := [], tindex := ∅ }) = .ok (.ok acc))
    {found : List (List (Hop × Int64) × Option Int)} {used' : Nat}
    (hcol : ev st (if false = true then collectAll c acc.arena k (acc.next.filter fun i =>
        c.dfa.accepts (acc.arena.getD i default).state && !E.contains (acc.arena.getD i default).node) acc.used
      else pure (collectAny acc.arena k (acc.next.filter fun i =>
        c.dfa.accepts (acc.arena.getD i default).state && !E.contains (acc.arena.getD i default).node), acc.used)) =
      .ok (.ok (found, used'))) :
    AnyInv R c x acc.arena acc.index
      ((acc.next.filter fun i => c.dfa.accepts (acc.arena.getD i default).state &&
        !E.contains (acc.arena.getD i default).node).foldl (fun e i => e.insert (acc.arena.getD i default).node) E)
      acc.next (k + 1) used' (rows ++ found.map fun (p, tau) => rowOf c x p tau) := by
  have hsh' := shInv_step hx hn hF hT hI.sh hne hok hacc hcol
  obtain ⟨lo, hlay, hAK⟩ := hI.key
  obtain ⟨lo0, hlay0, hlo⟩ := hI.sh.layerEq
  have hlo0 : lo0 = lo := by
    rw [hlay] at hlay0
    obtain ⟨n, hn⟩ : ∃ n, A.size - lo = n + 1 := ⟨A.size - lo - 1, by
      have : A.size - lo ≠ 0 := fun h0 => hne (by rw [hlay, h0]; rfl)
      omega⟩
    obtain ⟨n0, hn0⟩ : ∃ n0, A.size - lo0 = n0 + 1 := ⟨A.size - lo0 - 1, by
      have : A.size - lo0 ≠ 0 := fun h0 => by rw [hn, h0] at hlay0; simp at hlay0
      omega⟩
    rw [hn, hn0, List.range'_succ, List.range'_succ] at hlay0
    exact (List.cons.inj hlay0).1.symm
  subst hlo0
  -- the layer fold again, with the creation order
  have hS0 : SLayer c false k A I used [] { arena := A, index := I, used, next := [], tindex := ∅ } := by
    refine ⟨fun _ _ => rfl, le_refl _, fun i h1 h2 => ?_, fun p i => ?_, fun a ha => (by cases ha), ?_, ?_⟩
    · exact absurd h2 (by simp only; omega)
    · simp only
      constructor
      · intro h; exact .inl h
      · rintro (h | ⟨h1, h2, -⟩); exact h; omega
    · simp
    · simp only [Nat.sub_self, Nat.add_zero]; exact ⟨hI.sh.usedLe, le_refl _⟩
  have hO0 : SOrder A [] { arena := A, index := I, used, next := [], tindex := ∅ } :=
    fun i j h1 h2 h3 => absurd h3 (by simp only; omega)
  rw [hlay] at hacc
  obtain ⟨Ls, hLs, hS, hO⟩ := shortestExpand_order (all := false) (best := best) hT hI.sh.arena.depthLe
    (fun p i h => ((hI.sh.arena.index p i).1 h).1) _ [] _ acc
    (fun i hi => by rw [List.mem_range'_1] at hi; omega) hS0 hO0 hacc
  simp only [List.nil_append] at hS hO
  obtain ⟨hA', hlo', -⟩ := layer_arena hx hn hI.sh.arena hlo hI.sh.tau hLs hS
  have hAK' := anyKey_step hx hF hK hI.sh.arena hlo hAK hLs hS hO hA' hlo'
  refine ⟨hsh', ⟨A.size, hS.next, hAK'⟩, ?_⟩
  rw [if_neg (by simp)] at hcol
  cases ev_pure_inj hcol
  have hnext := hS.next
  have hgrow := hS.grow
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
  have hts : targets.Pairwise (· < ·) :=
    (show acc.next.Pairwise (· < ·) by rw [hnext]; exact List.pairwise_lt_range' 1 (by omega)).sublist
      List.filter_sublist
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hI.least r hr
  obtain ⟨⟨p0, t0⟩, hz, rfl⟩ := List.mem_map.1 hr
  obtain ⟨i, hi, hzp, hτ, hfirst⟩ := collectAny_first A' k targets [] ([], ∅) (by simpa using hts) (by simp)
    (by simp) _ hz
  simp only [List.nil_append] at hi hfirst hzp hτ
  obtain ⟨h1, h2, h3, h4⟩ := (htarg i).1 hi
  have hd : (A'.getD i default).depth = k + 1 := (hlo' i h2).1 h1
  have hτ0 : t0 = none := by rw [hτ]; exact hsh'.tau i h2
  subst hτ0
  obtain ⟨w0, hw0l, hw0, -, hw0s⟩ := paths_sound hA' i h2 (k + 2) (by omega) p0 hzp
  have hend : (rowOf c x p0 none).end = (A'.getD i default).node := by
    show ((p0.getLast?.map (·.2)).getD x) = _
    rw [← hw0s]; exact isWalk_end hw0
  refine ⟨p0, rfl, fun w hw => ?_⟩
  simp only at hw
  rw [hend] at hw
  obtain ⟨hww, ⟨q, hq, hacc⟩, hmin⟩ := hw
  -- the minimal matching walks to this end have `k + 1` hops
  have hAcc : AccR R c.dfa x (k + 1) (A'.getD i default).node :=
    ⟨_, h3, hd ▸ (hA'.dist i h2).1⟩
  have hle : w.length ≤ k + 1 := by
    by_contra hlt; push Not at hlt; exact hmin (k + 1) hlt hAcc
  have hge : k + 1 ≤ w.length := by
    by_contra hlt; push Not at hlt
    have := (hI.sh.emitted _).2 ⟨w.length, by omega, q, hacc, w, rfl, hww, hq⟩
    rw [h4] at this; cases this
  have hwl : w.length = k + 1 := by omega
  -- it ends at a target of the same end, after the first one
  have hr : Rch R c.dfa x (k + 1) ((A'.getD i default).node, q) := ⟨w, hwl, hww, hq⟩
  have hat : AtDist R c.dfa x (k + 1) ((A'.getD i default).node, q) :=
    ⟨hr, fun m hm hr' => hmin m (by omega) ⟨q, hacc, hr'⟩⟩
  obtain ⟨i', hi'⟩ := hA'.complete (k + 1) (le_refl _) _ hr
  obtain ⟨hi'A, hi'k⟩ := (hA'.index _ i').1 hi'
  have hdi' : (A'.getD i' default).depth = k + 1 := atDist_unique (hi'k ▸ hA'.dist i' hi'A) hat
  have hkk : skey (A'.getD i' default) = ((A'.getD i default).node, q) := hi'k
  simp only [skey, Prod.mk.injEq] at hkk
  have hi't : i' ∈ targets := (htarg i').2 ⟨(hlo' i' hi'A).2 hdi', hi'A, by rw [hkk.2]; exact hacc,
    by rw [hkk.1]; exact h4⟩
  have hii' : i ≤ i' := hfirst i' hi't hkk.1
  have hleast' : ∀ s' ∈ pathsTo A' (k + 2) i', keysLe (hopKeys s') (hopKeys (stepPairs w)) = true := by
    intro s' hs'
    exact hAK'.least i' hi'A s' (by rw [hdi']; exact hs') w (by rw [hdi']; exact hwl)
      (by rw [hkk.1]; exact hww) (by rw [hkk.2]; exact hq)
  rcases Nat.lt_or_eq_of_le hii' with hlt | heq
  · obtain ⟨s', hs'⟩ := List.exists_mem_of_ne_nil _ (paths_ne hA' i' hi'A (k + 2) (by omega))
    have := hAK'.order i i' h1 hlt hi'A p0 (by rw [hd]; exact hzp) s' (by rw [hdi']; exact hs')
    exact keysLe_trans this.1 (hleast' s' hs')
  · subst heq; exact hleast' p0 hzp

theorem anyLoop_inv {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R) (hn : HopsNodup st c)
    (hF : HopFun R) (hK : KeyFun R) (hT : c.timed = none) {x : Int64} :
    ∀ (fuel : Nat) (A : Array SNode) (I : Std.HashMap SState Nat) (best : Std.HashMap SState (Option Int))
      (E : Std.HashSet Int64) (layer : List Nat) (k used : Nat) (rows res : List PathRow),
      AnyInv R c x A I E layer k used rows → c.limit + 1 ≤ fuel + k →
      ev st (shortestLoop c x false fuel A I best E layer k used rows) = .ok (.ok res) →
      ∃ A' I' E' layer' k' used', AnyInv R c x A' I' E' layer' k' used' res
  | 0, A, I, best, E, layer, k, used, rows, res, hI, hf, h => by
    simp only [shortestLoop] at h
    cases ev_pure_inj h
    exact ⟨A, I, E, layer, k, used, hI⟩
  | fuel + 1, A, I, best, E, layer, k, used, rows, res, hI, hf, h => by
    rw [shortestLoop.eq_2] at h
    split at h
    · cases ev_pure_inj h
      exact ⟨A, I, E, layer, k, used, hI⟩
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      obtain ⟨acc, hacc, h⟩ := ev_bind_ok h
      dsimp only at h
      rw [if_neg (by simp)] at h
      obtain ⟨⟨found, used'⟩, hcol, h⟩ := ev_bind_ok h
      exact anyLoop_inv hx hn hF hK hT fuel _ _ _ _ _ _ _ _ res
        (anyInv_step hx hn hF hK hT hI hc.1 hc.2 hacc (by rw [if_neg (by simp)]; exact hcol)) (by omega) h

/-- path-evaluation "Shortest modes" (ANY_SHORTEST's choice, not time-respecting): when the hop
layer lists exactly the hops of `R`, each once, and a hop is determined by its key (and so are its
letter and target), each row of a successful ANY_SHORTEST search spells a path whose hop-key
sequence is lexicographically least among the matching walks of minimal length to its end. -/
theorem anyShortest_least {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hx : HopsExact st c R) (hn : HopsNodup st c) (hF : HopFun R) (hK : KeyFun R) (hT : c.timed = none)
    (hd : buildDfa (toRE false e) = .ok c.dfa) {rows : List PathRow}
    (h : ev st (shortest c x false) = .ok (.ok rows)) :
    ∀ r ∈ rows, ∃ s, r = rowOf c x s none ∧
      ∀ w, Shortest R e x r.end w → keysLe (hopKeys s) (hopKeys (stepPairs w)) = true := by
  unfold shortest at h
  rw [hT] at h
  obtain ⟨u, hu, h⟩ := ev_bind_ok h
  obtain ⟨rfl, hul⟩ := charge_ok hu
  simp only [Option.getD_none] at h
  have hI := shInv_init R c false x hul
  have hroot : ∀ i < 1, i = 0 := fun i hi => by omega
  have hAK : AnyKey R c.dfa x #[{ node := x, state := 0, depth := 0, tau := none, preds := [] }] 0 := by
    refine ⟨fun i hi hpos => absurd hi (by simp; omega), fun i hi s hs w hwl hww hwr => ?_,
      fun i j h1 h2 h3 => absurd h3 (by simp; omega)⟩
    have : i = 0 := by simp at hi; omega
    subst this
    simp only [pathsTo, Array.getD_eq_getD_getElem?] at hs
    simp at hs
    subst hs
    rfl
  have hRL : RowsLeast R c x (if c.dfa.accepts 0 then [rowOf c x [] none] else []) := by
    intro r hr
    split at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨[], rfl, fun _ _ => rfl⟩
    · cases hr
  obtain ⟨A, I, E, layer, k, used, hF'⟩ := anyLoop_inv hx hn hF hK hT _ _ _ _ _ _ _ _ _ rows
    ⟨hI, ⟨0, rfl, hAK⟩, hRL⟩ (by omega) h
  intro r hr
  obtain ⟨s, hs, hmin⟩ := hF'.least r hr
  exact ⟨s, hs, fun w hw => hmin w ((minW_iff hd x r.end w).2 hw)⟩

/-! ## The hops of a store view are determined by their keys -/

theorem eid_unique {st : ModelState} (hwf : st.WF) {r r' : TripleRow} (hr : r ∈ st.triples)
    (hr' : r' ∈ st.triples) (h : r.eid = r'.eid) : r = r' := by
  by_contra hne
  haveI : Std.Symm (fun a b : TripleRow => a.eid ≠ b.eid) := ⟨fun _ _ h => Ne.symm h⟩
  exact List.Pairwise.forall (R := fun a b : TripleRow => a.eid ≠ b.eid) hwf hr hr' hne h

theorem VKind.code_inj {k k' : VKind} (h : k.code = k'.code) : k = k' := by
  cases k <;> cases k' <;> simp_all [VKind.code]

theorem Dir.code_inj {d d' : Dir} (h : d.code = d'.code) : d = d' := by
  cases d <;> cases d' <;> simp_all [Dir.code]

theorem VKind.code_pos (k : VKind) : k.code ≠ 0 := by cases k <;> simp [VKind.code]

/-- The hops of a store view, by the statement they step over. -/
theorem viewHop_inv {st : ModelState} {V : Store.View} {rel : Int64 → Int64 → Bool} {x : Int64} {l : Letter}
    {nb : Nb} (h : ViewHop st V rel x l nb) : ∃ r ∈ st.triples,
      ((∃ iri, Sem.decodeId st r.p = .ok (.iri iri) ∧
        ((l = .stored iri (rel r.p r.o) .out ∧ nb = storedNb .out r.s r) ∨
         (l = .stored iri (rel r.p r.o) .inn ∧ nb = storedNb .inn r.o r))) ∨
      (∃ k, (l = .virt k .out ∧ nb = virtNb k .out r) ∨ (l = .virt k .inn ∧ nb = virtNb k .inn r))) := by
  cases h with
  | out hr _ hd => exact ⟨_, hr, .inl ⟨_, hd, .inl ⟨rfl, rfl⟩⟩⟩
  | inn hr _ hd => exact ⟨_, hr, .inl ⟨_, hd, .inr ⟨rfl, rfl⟩⟩⟩
  | virtOut k hr _ => exact ⟨_, hr, .inr ⟨k, .inl ⟨rfl, rfl⟩⟩⟩
  | virtIn k hr _ => exact ⟨_, hr, .inr ⟨k, .inr ⟨rfl, rfl⟩⟩⟩

/-- On a well-formed state, a hop of a store view determines its letter and target. -/
theorem viewHop_fun {st : ModelState} (hwf : st.WF) (V : Store.View) (rel : Int64 → Int64 → Bool) :
    HopFun (ViewHop st V rel) := by
  intro x l l' nb nb' h1 h2 hh
  obtain ⟨r, hr, h1⟩ := viewHop_inv h1
  obtain ⟨r', hr', h2⟩ := viewHop_inv h2
  rcases h1 with ⟨iri, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
  rcases h2 with ⟨iri', hd', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
  simp only [storedNb, virtNb, Hop.mk.injEq, reduceCtorEq, beq_self_eq_true, if_true, false_and, and_false,
    Bool.false_eq_true] at hh <;>
  first
    | (obtain rfl := eid_unique hwf hr hr' hh.1
       rw [hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩)
    | (obtain rfl := eid_unique hwf hr hr' hh.1
       obtain rfl := VKind.code_inj hh.2.2.2
       exact ⟨rfl, rfl⟩)
    | exact absurd hh.2.2.2.symm (VKind.code_pos _)
    | exact absurd hh.2.2.2 (VKind.code_pos _)
    | (simp [Dir] at hh)

/-- On a well-formed state, a hop key of a store view determines the hop. -/
theorem viewHop_keyFun {st : ModelState} (hwf : st.WF) (V : Store.View) (rel : Int64 → Int64 → Bool) :
    KeyFun (ViewHop st V rel) := by
  intro x l l' nb nb' h1 h2 hk
  obtain ⟨r, hr, h1⟩ := viewHop_inv h1
  obtain ⟨r', hr', h2⟩ := viewHop_inv h2
  rcases h1 with ⟨iri, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
  rcases h2 with ⟨iri', hd', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨k', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
  simp only [storedNb, virtNb, Hop.key, Prod.mk.injEq, Int64.toInt_inj, Dir.code, beq_self_eq_true, if_true,
    reduceCtorEq] at hk <;>
  first
    | (obtain rfl := eid_unique hwf hr hr' hk.1; rfl)
    | (obtain rfl := eid_unique hwf hr hr' hk.1
       obtain rfl := VKind.code_inj hk.2.1
       rfl)
    | exact absurd hk.2.1.symm (VKind.code_pos _)
    | exact absurd hk.2.1 (VKind.code_pos _)
    | (simp at hk)
    | omega

/-- path-evaluation "Endpoint binding" (ANY_SHORTEST, up to the tie-break): with a reversible hop
relation, every reversed row of the ANY_SHORTEST search from `y` for `^e` is the row of a matching
walk of minimal length from its start into `y`, and every start of a matching walk into `y` within
the bound has exactly one. (Which minimal path is chosen can differ from the search from the start:
each search breaks ties by the hop keys read from its own start.) -/
theorem anyShortest_fromEnd {st : ModelState} {c' : Ctx} {R : HopRel} {y : Int64} {e : PathExpr}
    (hS : R.Symm) (hx' : HopsExact st c' R) (hn' : HopsNodup st c') (hF : HopFun R) (hT' : c'.timed = none)
    (hd' : buildDfa (toRE false (.inv e)) = .ok c'.dfa) {rowsE : List PathRow}
    (he : ev st (shortest c' y false) = .ok (.ok rowsE)) :
    (∀ r ∈ rowsE.map PathRow.flip, ∃ x w, Shortest R e x y w ∧ Within c'.maxHops w.length ∧
      r = walkRow c' x w none) ∧
    (∀ x w, IsWalk R x w y → word w ∈ lang e → Within c'.maxHops w.length →
      ∃ r ∈ rowsE.map PathRow.flip, r.start = x) ∧
    ((rowsE.map PathRow.flip).map PathRow.start).Nodup := by
  obtain ⟨h1, h2, h3⟩ := anyShortest_spec hx' hn' hF hT' hd' he
  refine ⟨fun r hr => ?_, fun x w hw hl hb => ?_, ?_⟩
  · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
    obtain ⟨x, w, hw, hb, rfl⟩ := h1 r2 hr2
    exact ⟨x, revWalk y w, shortest_inv' hS e x y w hw, by rw [length_rev]; exact hb,
      flip_walkRow' hT' hT' hw.1⟩
  · obtain ⟨r2, hr2, hr2e⟩ := h2 x (revWalk x w) (isWalk_rev hS x y w hw)
      (by rw [mem_lang_inv, word_rev, flipRev_flipRev]; exact hl) (by rw [length_rev]; exact hb)
    exact ⟨r2.flip, List.mem_map.2 ⟨r2, hr2, rfl⟩, hr2e⟩
  · rw [List.map_map]
    have : (PathRow.start ∘ PathRow.flip) = PathRow.end := rfl
    rw [this]; exact h3

/-- path-evaluation "Endpoint binding" (ANY_SHORTEST): with a reversible hop relation, the
search from `x` for `e` has a row into `y` exactly when the search from `y` for `^e` (same hop
bound) has one from `x` after reversal, and any two such rows join the same endpoints with the
same number of hops — each a shortest matching walk. The chosen paths may differ (ties broken by
each search's own hop keys). -/
theorem anyShortest_fromEnd_len {st : ModelState} {c c' : Ctx} {R : HopRel} {x y : Int64} {e : PathExpr}
    (hS : R.Symm) (hx : HopsExact st c R) (hn : HopsNodup st c) (hx' : HopsExact st c' R)
    (hn' : HopsNodup st c') (hF : HopFun R) (hT : c.timed = none) (hT' : c'.timed = none)
    (hd : buildDfa (toRE false e) = .ok c.dfa) (hd' : buildDfa (toRE false (.inv e)) = .ok c'.dfa)
    (hb : c'.maxHops = c.maxHops) {rowsS rowsE : List PathRow}
    (hs : ev st (shortest c x false) = .ok (.ok rowsS)) (he : ev st (shortest c' y false) = .ok (.ok rowsE)) :
    ((∃ r ∈ rowsS, r.end = y) ↔ (∃ r ∈ rowsE.map PathRow.flip, r.start = x)) ∧
    (∀ r ∈ rowsS, r.end = y → ∀ r' ∈ rowsE.map PathRow.flip, r'.start = x →
      r.start = r'.start ∧ r.end = r'.end ∧ r.hops = r'.hops) := by
  obtain ⟨h1, h2, -⟩ := anyShortest_spec hx hn hF hT hd hs
  obtain ⟨g1, g2, -⟩ := anyShortest_fromEnd hS hx' hn' hF hT' hd' he
  have side : ∀ r ∈ rowsS, r.end = y → ∃ w, Shortest R e x y w ∧ Within c.maxHops w.length ∧
      r = walkRow c x w none := by
    intro r hr hend
    obtain ⟨y0, w, hw, hwb, rfl⟩ := h1 r hr
    have hy : y0 = y := by rw [← hend, walkRow_eq hw.1]
    subst hy; exact ⟨w, hw, hwb, rfl⟩
  have side' : ∀ r ∈ rowsE.map PathRow.flip, r.start = x → ∃ w, Shortest R e x y w ∧
      Within c'.maxHops w.length ∧ r = walkRow c' x w none := by
    intro r hr hst
    obtain ⟨x0, w, hw, hwb, rfl⟩ := g1 r hr
    have hx0 : x0 = x := by rw [← hst, walkRow_eq hw.1]
    subst hx0; exact ⟨w, hw, hwb, rfl⟩
  refine ⟨⟨fun ⟨r, hr, hend⟩ => ?_, fun ⟨r, hr, hst⟩ => ?_⟩, fun r hr hend r' hr' hst => ?_⟩
  · obtain ⟨w, hw, hwb, -⟩ := side r hr hend
    exact g2 x w hw.1 hw.2.1 (by rw [hb]; exact hwb)
  · obtain ⟨w, hw, hwb, -⟩ := side' r hr hst
    exact h2 y w hw.1 hw.2.1 (by rw [← hb]; exact hwb)
  · obtain ⟨w, hw, -, rfl⟩ := side r hr hend
    obtain ⟨w', hw', -, rfl⟩ := side' r' hr' hst
    rw [walkRow_eq hw.1, walkRow_eq hw'.1]
    have := hw.2.2 w' hw'.1 hw'.2.1
    have := hw'.2.2 w hw.1 hw.2.1
    simp only [true_and]
    omega

end Tiramemsu.Path
