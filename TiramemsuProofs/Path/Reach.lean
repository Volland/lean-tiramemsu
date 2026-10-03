/-
path-evaluation "Reachability mode" and "Termination and search bound" for REACH: on a model
state, whenever the hop layer lists exactly the hops of a relation `R` (`HopsExact`) and the
automaton is compiled from `e`, a successful REACH search from `x` returns each end of a walk of
`R` from `x` whose word is in `lang e` and whose length is within the hop bound exactly once,
with the length of a shortest such walk; and searching with the stated fuel returns the same
outcome as with any larger fuel.

The proof is the breadth-first invariant over `(node, state)` layers: after `depth` layers the
visited set is the states reachable within `depth` hops, the frontier the states at distance
exactly `depth`, and the emitted ends those with an accepting state within `depth` hops.
-/
import TiramemsuProofs.Path.Spec
import TiramemsuProofs.Store.Temporal

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Evaluator programs: lists and folds -/

theorem ev_mapM_forall₂ {α β : Type} (st : ModelState) (f : α → EvM β) :
    ∀ (xs : List α) (ys : List β), ev st (xs.mapM f) = .ok (.ok ys) →
      List.Forall₂ (fun x y => ev st (f x) = .ok (.ok y)) xs ys
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    rw [ev_pure] at h
    cases h; exact .nil
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := ev_bind_ok h
    obtain ⟨ys', hys, h⟩ := ev_bind_ok h
    rw [ev_pure] at h
    cases h
    exact .cons hy (ev_mapM_forall₂ st f xs ys' hys)

/-- A fold invariant indexed by the processed prefix. -/
theorem ev_foldlM_pre {α β : Type} (st : ModelState) (f : β → α → EvM β) (P : List α → β → Prop)
    (hf : ∀ done b a b', P done b → ev st (f b a) = .ok (.ok b') → P (done ++ [a]) b') :
    ∀ (l done : List α) (init b : β), P done init → ev st (l.foldlM f init) = .ok (.ok b) → P (done ++ l) b
  | [], done, init, b, hi, h => by
    simp only [List.foldlM_nil] at h
    rw [ev_pure] at h
    cases h; simpa using hi
  | a :: l, done, init, b, hi, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', h1, h2⟩ := ev_bind_ok h
    have := ev_foldlM_pre st f P hf l (done ++ [a]) b' b (hf done init a b' hi h1) h2
    simpa using this

theorem ev_pure_inj {α : Type} {st : ModelState} {a b : α} (h : ev st (pure a : EvM α) = .ok (.ok b)) : a = b := by
  rw [ev_pure] at h; cases h; rfl

/-! ## Distances in the search graph -/

section Dist

variable (R : HopRel) (d : Dfa) (x : Int64)

/-- A search state reachable from `(x, start)` in exactly `n` hops. -/
def Rch (n : Nat) (p : SState) : Prop := PRf R d (x, 0) n p

/-- A search state at distance exactly `n`. -/
def AtDist (n : Nat) (p : SState) : Prop := Rch R d x n p ∧ ∀ k < n, ¬ Rch R d x k p

/-- An end reached by a matching walk of exactly `n` hops (an accepting state). -/
def AccR (n : Nat) (y : Int64) : Prop := ∃ t, d.accepts t = true ∧ Rch R d x n (y, t)

/-- The successors of a list of search states. -/
def Succ (frontier : List SState) (p : SState) : Prop :=
  ∃ a ∈ frontier, ∃ nb, PStep R d a nb p.2 ∧ nb.to = p.1

theorem rch_zero (p : SState) : Rch R d x 0 p ↔ p = (x, 0) := prf_zero R d _ p

theorem rch_succ (n : Nat) (p : SState) :
    Rch R d x (n + 1) p ↔ ∃ a, Rch R d x n a ∧ ∃ nb, PStep R d a nb p.2 ∧ nb.to = p.1 := by
  unfold Rch; rw [prf_succ]
  constructor
  · rintro ⟨b, nb, h1, h2, h3⟩; exact ⟨b, h1, nb, h2, h3⟩
  · rintro ⟨b, h1, nb, h2, h3⟩; exact ⟨b, nb, h1, h2, h3⟩

/-- The next layer: the successors of the states at distance `n` not reachable within `n` hops
are exactly the states at distance `n + 1`. -/
theorem atDist_succ (n : Nat) (frontier : List SState)
    (hf : ∀ p, p ∈ frontier ↔ AtDist R d x n p) (p : SState) :
    AtDist R d x (n + 1) p ↔ Succ R d frontier p ∧ ∀ k ≤ n, ¬ Rch R d x k p := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun k hk => h2 k (by omega)⟩
    obtain ⟨a, ha, nb, hs, ht⟩ := (rch_succ R d x n p).1 h1
    refine ⟨a, (hf a).2 ⟨ha, fun k hk hka => h2 (k + 1) (by omega) ?_⟩, nb, hs, ht⟩
    exact (rch_succ R d x k p).2 ⟨a, hka, nb, hs, ht⟩
  · rintro ⟨⟨a, ha, nb, hs, ht⟩, h2⟩
    exact ⟨(rch_succ R d x n p).2 ⟨a, ((hf a).1 ha).1, nb, hs, ht⟩, fun k hk => h2 k (by omega)⟩

/-- Breadth-first completeness: when no state is at distance `n`, every reachable state is
reachable within fewer than `n` hops. -/
theorem rch_lt_of_empty (n : Nat) (hn : ∀ p, ¬ AtDist R d x n p) :
    ∀ m p, Rch R d x m p → ∃ k < n, Rch R d x k p := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hp
    by_cases hm : m < n
    · exact ⟨m, hm, hp⟩
    · obtain ⟨b, hb1, hb2⟩ := (prf_add R d (x, 0) p n (m - n)).1 (by rw [Nat.add_sub_cancel' (by omega)]; exact hp)
      have : ∃ k < n, Rch R d x k b := by
        by_contra hk
        push Not at hk
        exact hn b ⟨hb1, fun k hk' h => hk k hk' h⟩
      obtain ⟨k, hk, hkb⟩ := this
      obtain ⟨k', hk', hp'⟩ := ih (k + (m - n)) (by omega) p ((prf_add R d (x, 0) p k (m - n)).2 ⟨b, hkb, hb2⟩)
      exact ⟨k', hk', hp'⟩

end Dist

/-! ## One REACH layer -/

/-- The fold state of one REACH layer after processing the transitions `done`. -/
structure LayerOK (c : Ctx) (V0 : Std.HashSet SState) (E0 : Std.HashSet Int64) (u0 : Nat)
    (done : List (Nb × Nat))
    (acc : List SState × Std.HashSet SState × Std.HashSet Int64 × List Int64 × Nat) : Prop where
  vis : ∀ p, acc.2.1.contains p = true ↔ V0.contains p = true ∨ ∃ a ∈ done, (a.1.to, a.2) = p
  next : ∀ p, p ∈ acc.1 ↔ (∃ a ∈ done, (a.1.to, a.2) = p) ∧ V0.contains p = false
  nodup : acc.1.Nodup
  em : ∀ y, acc.2.2.1.contains y = true ↔ E0.contains y = true ∨ ∃ t, c.dfa.accepts t = true ∧ (y, t) ∈ acc.1
  ends : ∀ y, y ∈ acc.2.2.2.1 ↔ E0.contains y = false ∧ ∃ t, c.dfa.accepts t = true ∧ (y, t) ∈ acc.1
  endsNodup : acc.2.2.2.1.Nodup
  used : acc.2.2.2.2 = u0 + acc.1.length
  le : acc.2.2.2.2 ≤ c.limit

theorem reachLayer_fold {st : ModelState} {c : Ctx} {frontier : List SState} {V0 : Std.HashSet SState}
    {E0 : Std.HashSet Int64} {u0 : Nat} {res : List SState × Std.HashSet SState × Std.HashSet Int64 × List Int64 × Nat}
    (hu : u0 ≤ c.limit) (h : ev st (reachLayer c frontier V0 E0 u0) = .ok (.ok res)) :
    ∃ exps : List (List (Nb × Nat)),
      List.Forall₂ (fun p L => ev st (expandOne c p.1 p.2) = .ok (.ok L)) frontier exps ∧
      LayerOK c V0 E0 u0 exps.flatten res := by
  unfold reachLayer at h
  obtain ⟨exps, hexps, h⟩ := ev_bind_ok h
  refine ⟨exps, (ev_mapM_forall₂ st _ frontier exps hexps).imp (fun {p L} hp => by
    obtain ⟨n, q⟩ := p; exact hp), ?_⟩
  have := ev_foldlM_pre st _ (fun done acc => LayerOK c V0 E0 u0 done acc) ?_ exps.flatten [] _ res ?_ h
  · simpa using this
  · intro done b a b' hb hs
    obtain ⟨next, vis, em, ends, used⟩ := b
    obtain ⟨nb, t⟩ := a
    simp only at hs
    obtain ⟨hv, hn, hnd, he, hen, hend, hus, hle⟩ := hb
    simp only at hv hn hnd he hen hend hus hle
    have hmem : ∀ p, (∃ a ∈ done ++ [(nb, t)], (a.1.to, a.2) = p) ↔
        (∃ a ∈ done, (a.1.to, a.2) = p) ∨ (nb.to, t) = p := by
      intro p; simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨a, ha | rfl, h⟩; exact .inl ⟨a, ha, h⟩; exact .inr h
      · rintro (⟨a, ha, h⟩ | h); exact ⟨a, .inl ha, h⟩; exact ⟨_, .inr rfl, h⟩
    split at hs
    · rename_i hc
      cases ev_pure_inj hs
      refine ⟨fun p => ?_, fun p => ?_, hnd, he, hen, hend, hus, hle⟩
      · rw [hv, hmem]
        constructor
        · rintro (h | h); exact .inl h; exact .inr (.inl h)
        · rintro (h | h | rfl); exact .inl h; exact .inr h; exact (hv _).1 hc
      · rw [hn, hmem]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨.inl h1, h2⟩
        · rintro ⟨h1 | rfl, h2⟩
          · exact ⟨h1, h2⟩
          · rcases (hv _).1 hc with h | h
            · rw [h] at h2; cases h2
            · exact ⟨h, h2⟩
    · rename_i hc
      simp only [Bool.not_eq_true] at hc
      obtain ⟨u, hu', hs⟩ := ev_bind_ok hs
      obtain ⟨rfl, hul⟩ := charge_ok hu'
      have hnotin : (nb.to, t) ∉ next := fun h => by
        have := (hv _).2 (.inr ((hn _).1 h).1); rw [hc] at this; cases this
      have hV0 : V0.contains (nb.to, t) = false := by
        cases h : V0.contains (nb.to, t)
        · rfl
        · have := (hv _).2 (.inl h); rw [hc] at this; cases this
      have hvis' : ∀ p, (vis.insert (nb.to, t)).contains p = true ↔ V0.contains p = true ∨
          ∃ a ∈ done ++ [(nb, t)], (a.1.to, a.2) = p := by
        intro p; rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hv, hmem]
        constructor
        · rintro (h | h | h); exacts [.inr (.inr h), .inl h, .inr (.inl h)]
        · rintro (h | h | h); exacts [.inr (.inl h), .inr (.inr h), .inl h]
      have hnext' : ∀ p, p ∈ next ++ [(nb.to, t)] ↔ (∃ a ∈ done ++ [(nb, t)], (a.1.to, a.2) = p) ∧
          V0.contains p = false := by
        intro p; rw [List.mem_append, List.mem_singleton, hn, hmem]
        constructor
        · rintro (⟨h1, h2⟩ | rfl); exact ⟨.inl h1, h2⟩; exact ⟨.inr rfl, hV0⟩
        · rintro ⟨h1 | rfl, h2⟩; exact .inl ⟨h1, h2⟩; exact .inr rfl
      have hnd' : (next ++ [(nb.to, t)]).Nodup := List.nodup_append.2 ⟨hnd, List.nodup_singleton _,
        fun a ha b hb => by simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hnotin ha⟩
      split at hs
      · rename_i ha
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
        cases ev_pure_inj hs
        refine ⟨hvis', hnext', hnd', fun y => ?_, fun y => ?_, ?_, by simp; omega, hul⟩
        · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, he]
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro (rfl | h | ⟨t', h1, h2⟩); exact .inr ⟨t, ha.1, .inr ⟨rfl, rfl⟩⟩; exact .inl h
            exact .inr ⟨t', h1, .inl h2⟩
          · rintro (h | ⟨t', h1, h2 | ⟨rfl, rfl⟩⟩); exact .inr (.inl h); exact .inr (.inr ⟨t', h1, h2⟩)
            exact .inl rfl
        · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
          rw [hen]
          constructor
          · rintro (⟨h1, t', h2, h3⟩ | rfl)
            · exact ⟨h1, t', h2, .inl h3⟩
            · refine ⟨?_, t, ha.1, .inr ⟨rfl, rfl⟩⟩
              cases h : E0.contains nb.to
              · rfl
              · have := (he _).2 (.inl h); rw [ha.2] at this; cases this
          · rintro ⟨h1, t', h2, h3 | ⟨rfl, rfl⟩⟩
            · exact .inl ⟨h1, t', h2, h3⟩
            · exact .inr rfl
        · refine List.nodup_append.2 ⟨hend, List.nodup_singleton _, fun a ha' b hb => ?_⟩
          simp only [List.mem_singleton] at hb; subst hb; rintro rfl
          obtain ⟨-, t', h2, h3⟩ := (hen _).1 ha'
          have := (he _).2 (.inr ⟨t', h2, h3⟩); rw [ha.2] at this; cases this
      · rename_i ha
        cases ev_pure_inj hs
        have hacc : c.dfa.accepts t = true → em.contains nb.to = true := by
          intro h1; cases h2 : em.contains nb.to
          · simp [h1, h2] at ha
          · rfl
        refine ⟨hvis', hnext', hnd', fun y => ?_, fun y => ?_, hend, by simp; omega, hul⟩
        · rw [he]
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro (h | ⟨t', h1, h2⟩); exact .inl h; exact .inr ⟨t', h1, .inl h2⟩
          · rintro (h | ⟨t', h1, h2 | ⟨rfl, rfl⟩⟩)
            · exact .inl h
            · exact .inr ⟨t', h1, h2⟩
            · exact (he _).1 (hacc h1)
        · rw [hen]
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨h1, t', h2, h3⟩; exact ⟨h1, t', h2, .inl h3⟩
          · rintro ⟨h1, t', h2, h3 | ⟨rfl, rfl⟩⟩
            · exact ⟨h1, t', h2, h3⟩
            · rcases (he _).1 (hacc h2) with h | h
              · rw [h] at h1; cases h1
              · exact ⟨h1, h⟩
  · refine ⟨fun p => ?_, fun p => ?_, List.nodup_nil, fun y => ?_, fun y => ?_, List.nodup_nil, rfl, hu⟩ <;> simp

theorem forall₂_mem_right {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ y ∈ ys, ∃ x ∈ xs, P x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hp hr, y, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hp⟩
    · obtain ⟨x, hx, h⟩ := forall₂_mem_right hr y h; exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem forall₂_mem_left {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ x ∈ xs, ∃ y ∈ ys, P x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hp hr, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hp⟩
    · obtain ⟨y, hy, h⟩ := forall₂_mem_left hr x h; exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

/-- The transitions expanded from a frontier are exactly its successors. -/
theorem expanded_iff {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R)
    {frontier : List SState} {exps : List (List (Nb × Nat))}
    (h : List.Forall₂ (fun p L => ev st (expandOne c p.1 p.2) = .ok (.ok L)) frontier exps) (p : SState) :
    (∃ a ∈ exps.flatten, (a.1.to, a.2) = p) ↔ Succ R c.dfa frontier p := by
  constructor
  · rintro ⟨⟨nb, t⟩, ha, rfl⟩
    obtain ⟨L, hL, ha⟩ := List.mem_flatten.1 ha
    obtain ⟨a, haf, hev⟩ := forall₂_mem_right h L hL
    exact ⟨a, haf, nb, (hx a.1 a.2 L hev nb t).1 ha, rfl⟩
  · rintro ⟨a, haf, nb, hs, hto⟩
    obtain ⟨L, hL, hev⟩ := forall₂_mem_left h a haf
    exact ⟨(nb, p.2), List.mem_flatten.2 ⟨L, hL, (hx a.1 a.2 L hev nb p.2).2 hs⟩, by rw [hto]⟩

/-! ## The REACH loop invariant -/

/-- The state of the REACH search after `depth` layers. -/
structure ReachInv (R : HopRel) (c : Ctx) (x : Int64) (frontier : List SState)
    (visited : Std.HashSet SState) (emitted : Std.HashSet Int64) (depth used : Nat) (rows : List PathRow) : Prop where
  front : ∀ p, p ∈ frontier ↔ AtDist R c.dfa x depth p
  frontNodup : frontier.Nodup
  vis : ∀ p, visited.contains p = true ↔ ∃ k ≤ depth, Rch R c.dfa x k p
  em : ∀ y, emitted.contains y = true ↔ ∃ k ≤ depth, AccR R c.dfa x k y
  rowsOk : ∀ r ∈ rows, r = { start := x, «end» := r.end, hops := r.hops } ∧ AccR R c.dfa x r.hops r.end ∧
    (∀ k < r.hops, ¬ AccR R c.dfa x k r.end) ∧ r.hops ≤ depth
  complete : ∀ y, emitted.contains y = true → ∃ r ∈ rows, r.end = y
  nodup : (rows.map PathRow.end).Nodup
  bound : Within c.maxHops depth
  le : used ≤ c.limit
  fuel : frontier ≠ [] → depth + 1 ≤ used

theorem within_succ {b : Option Nat} {n : Nat} (h : b.all (n < ·) = true) : Within b (n + 1) := by
  intro m hm; subst hm; simpa using h

/-- One REACH layer preserves the invariant, one hop deeper. -/
theorem reachInv_step {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} (hx : HopsExact st c R)
    {frontier next : List SState} {visited vis : Std.HashSet SState} {emitted em : Std.HashSet Int64}
    {depth used used' : Nat} {rows : List PathRow} {ends : List Int64}
    (hI : ReachInv R c x frontier visited emitted depth used rows) (hne : frontier ≠ [])
    (hok : c.depthOk depth = true)
    (hl : ev st (reachLayer c frontier visited emitted used) = .ok (.ok (next, vis, em, ends, used'))) :
    ReachInv R c x next vis em (depth + 1) used'
      (rows ++ (ends.mergeSort fun a b => decide (a.toInt ≤ b.toInt)).map
        fun e => { start := x, «end» := e, hops := depth + 1 }) := by
  obtain ⟨exps, hexps, hL⟩ := reachLayer_fold hI.le hl
  obtain ⟨hv, hn, hnd, he, hen, hend, hus, hle⟩ := hL
  simp only at hv hn hnd he hen hend hus hle
  have hT := expanded_iff hx hexps
  have hfront : ∀ p, p ∈ next ↔ AtDist R c.dfa x (depth + 1) p := by
    intro p
    rw [hn, hT, atDist_succ R c.dfa x depth frontier hI.front]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k hk hr => ?_⟩
      have := (hI.vis p).2 ⟨k, hk, hr⟩; rw [h2] at this; cases this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      cases h : visited.contains p
      · rfl
      · obtain ⟨k, hk, hr⟩ := (hI.vis p).1 h; exact absurd hr (h2 k hk)
  have hsucc_rch : ∀ p, Succ R c.dfa frontier p → Rch R c.dfa x (depth + 1) p := by
    rintro p ⟨a, ha, nb, hs, hto⟩
    exact (rch_succ R c.dfa x depth p).2 ⟨a, ((hI.front a).1 ha).1, nb, hs, hto⟩
  have hE0 : ∀ y, emitted.contains y = false ↔ ∀ k ≤ depth, ¬ AccR R c.dfa x k y := by
    intro y
    constructor
    · intro h k hk ha; have := (hI.em y).2 ⟨k, hk, ha⟩; rw [h] at this; cases this
    · intro h; cases h' : emitted.contains y
      · rfl
      · obtain ⟨k, hk, ha⟩ := (hI.em y).1 h'; exact absurd ha (h k hk)
  have hsort := List.mergeSort_perm ends (fun a b => decide (a.toInt ≤ b.toInt))
  refine ⟨hfront, hnd, fun p => ?_, fun y => ?_, ?_, fun y hy => ?_, ?_, within_succ hok, hle, fun hne' => ?_⟩
  · rw [hv, hI.vis, hT]
    constructor
    · rintro (⟨k, hk, hr⟩ | h)
      · exact ⟨k, by omega, hr⟩
      · exact ⟨depth + 1, le_refl _, hsucc_rch p h⟩
    · rintro ⟨k, hk, hr⟩
      by_cases hk' : k ≤ depth
      · exact .inl ⟨k, hk', hr⟩
      · have hk1 : k = depth + 1 := by omega
        subst hk1
        by_cases hlo : ∃ k ≤ depth, Rch R c.dfa x k p
        · exact .inl hlo
        · push Not at hlo
          exact .inr ((atDist_succ R c.dfa x depth frontier hI.front p).1 ⟨hr, fun k hk => hlo k (by omega)⟩).1
  · rw [he, hI.em]
    constructor
    · rintro (⟨k, hk, ha⟩ | ⟨t, ht, hm⟩)
      · exact ⟨k, by omega, ha⟩
      · exact ⟨depth + 1, le_refl _, t, ht, ((hfront _).1 hm).1⟩
    · rintro ⟨k, hk, t, ht, hr⟩
      by_cases hk' : k ≤ depth
      · exact .inl ⟨k, hk', t, ht, hr⟩
      · have hk1 : k = depth + 1 := by omega
        subst hk1
        by_cases hlo : ∃ k ≤ depth, Rch R c.dfa x k (y, t)
        · obtain ⟨k, hk, hr'⟩ := hlo; exact .inl ⟨k, hk, t, ht, hr'⟩
        · push Not at hlo
          exact .inr ⟨t, ht, (hfront _).2 ⟨hr, fun k hk => hlo k (by omega)⟩⟩
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨h1, h2, h3, h4⟩ := hI.rowsOk r hr; exact ⟨h1, h2, h3, by omega⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr
      obtain ⟨h1, t, ht, hm⟩ := (hen y).1 (hsort.mem_iff.1 hy)
      exact ⟨rfl, ⟨t, ht, ((hfront _).1 hm).1⟩, fun k hk ha => (hE0 y).1 h1 k (by simp only at hk; omega) ha, le_refl _⟩
  · rcases (he y).1 hy with h | h
    · obtain ⟨r, hr, hre⟩ := hI.complete y h; exact ⟨r, List.mem_append_left _ hr, hre⟩
    · cases h0 : emitted.contains y
      · have hy' : y ∈ ends := (hen y).2 ⟨h0, h⟩
        exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨y, hsort.mem_iff.2 hy', rfl⟩), rfl⟩
      · obtain ⟨r, hr, hre⟩ := hI.complete y h0; exact ⟨r, List.mem_append_left _ hr, hre⟩
  · rw [List.map_append, List.map_map]
    have hid : (PathRow.end ∘ fun e => ({ start := x, «end» := e, hops := depth + 1 } : PathRow)) = id := rfl
    rw [hid, List.map_id]
    refine List.nodup_append.2 ⟨hI.nodup, hsort.nodup_iff.2 hend, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    obtain ⟨-, hacc, -, hle'⟩ := hI.rowsOk r hr
    have := (hI.em r.end).2 ⟨r.hops, hle', hacc⟩
    rw [((hen _).1 (hsort.mem_iff.1 hb)).1] at this; cases this
  · have := hI.fuel hne
    have : 0 < next.length := List.length_pos_of_ne_nil hne'
    omega

/-- The REACH loop ends in a state satisfying the invariant whose frontier is empty or whose
depth is the hop bound; the fuel never runs out first. -/
theorem reachLoop_inv {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} (hx : HopsExact st c R) :
    ∀ (fuel : Nat) (frontier : List SState) (visited : Std.HashSet SState) (emitted : Std.HashSet Int64)
      (depth used : Nat) (rows res : List PathRow),
    ReachInv R c x frontier visited emitted depth used rows → c.limit + 1 ≤ fuel + depth →
    ev st (reachLoop c x fuel frontier visited emitted depth used rows) = .ok (.ok res) →
    ∃ (fr : List SState) (vis : Std.HashSet SState) (em : Std.HashSet Int64) (dep u : Nat),
      ReachInv R c x fr vis em dep u res ∧ (fr = [] ∨ c.depthOk dep = false)
  | 0, frontier, visited, emitted, depth, used, rows, res, hI, hf, h => by
    simp only [reachLoop] at h
    cases ev_pure_inj h
    refine ⟨frontier, visited, emitted, depth, used, hI, .inl ?_⟩
    by_contra hne
    have := hI.fuel hne; have := hI.le; omega
  | fuel + 1, frontier, visited, emitted, depth, used, rows, res, hI, hf, h => by
    simp only [reachLoop] at h
    split at h
    · rename_i hc
      cases ev_pure_inj h
      refine ⟨frontier, visited, emitted, depth, used, hI, ?_⟩
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hc
      exact hc
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      obtain ⟨⟨next, vis, em, ends, used'⟩, hl, h⟩ := ev_bind_ok h
      exact reachLoop_inv hx fuel next vis em (depth + 1) used' _ res
        (reachInv_step hx hI hc.1 hc.2 hl) (by omega) h

theorem accR_zero (R : HopRel) (d : Dfa) (x y : Int64) : AccR R d x 0 y ↔ d.accepts 0 = true ∧ y = x := by
  unfold AccR; simp only [rch_zero, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩; exact ⟨ht, rfl⟩
  · rintro ⟨ht, rfl⟩; exact ⟨0, ht, rfl, rfl⟩

/-- REACH in terms of search distances: on success, every row is an end with an accepting state
at its (minimal) hop count, within the bound; every such end within the bound has a row; no end
repeats. -/
theorem reach_acc {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} (hx : HopsExact st c R)
    {rows : List PathRow} (h : ev st (reach c x) = .ok (.ok rows)) :
    (∀ r ∈ rows, r = { start := x, «end» := r.end, hops := r.hops } ∧ AccR R c.dfa x r.hops r.end ∧
      (∀ k < r.hops, ¬ AccR R c.dfa x k r.end) ∧ Within c.maxHops r.hops) ∧
    (∀ y n, AccR R c.dfa x n y → Within c.maxHops n → ∃ r ∈ rows, r.end = y) ∧
    (rows.map PathRow.end).Nodup := by
  unfold reach at h
  obtain ⟨u, hu, h⟩ := ev_bind_ok h
  obtain ⟨rfl, hul⟩ := charge_ok hu
  have hI : ReachInv R c x [(x, 0)] ((∅ : Std.HashSet SState).insert (x, 0))
      (if c.dfa.accepts 0 then (∅ : Std.HashSet Int64).insert x else ∅) 0 (0 + 1)
      (if c.dfa.accepts 0 then [{ start := x, «end» := x, hops := 0 }] else []) := by
    refine ⟨fun p => ?_, List.nodup_singleton _, fun p => ?_, fun y => ?_, fun r hr => ?_, fun y hy => ?_, ?_,
      fun m _ => Nat.zero_le m, hul, fun _ => le_refl _⟩
    · simp only [List.mem_singleton, AtDist, rch_zero, Nat.not_lt_zero, false_imp_iff, imp_true_iff, and_true]
    · simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq,
        Nat.le_zero, exists_eq_left, rch_zero]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    · simp only [Nat.le_zero, exists_eq_left, accR_zero]
      split
      · rename_i ha
        simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq, ha, true_and]
        exact eq_comm
      · rename_i ha; simp [ha]
    · split at hr
      · rename_i ha
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨rfl, (accR_zero R c.dfa x x).2 ⟨ha, rfl⟩, fun k hk => absurd hk (Nat.not_lt_zero _), le_refl _⟩
      · cases hr
    · split at hy
      · simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false, beq_iff_eq] at hy
        subst hy; simp_all
      · simp at hy
    · split <;> simp
  obtain ⟨fr, vis, em, dep, u, hF, hend⟩ := reachLoop_inv hx _ _ _ _ _ _ _ rows hI (by omega) h
  refine ⟨fun r hr => ?_, fun y n ha hn => ?_, hF.nodup⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hF.rowsOk r hr
    refine ⟨h1, h2, h3, fun m hm => ?_⟩
    have := hF.bound m hm; omega
  · obtain ⟨t, ht, hr⟩ := ha
    have : ∃ k ≤ dep, Rch R c.dfa x k (y, t) := by
      rcases hend with hfr | hd
      · obtain ⟨k, hk, hk'⟩ := rch_lt_of_empty R c.dfa x dep
          (fun p hp => by rw [← hF.front, hfr] at hp; cases hp) n (y, t) hr
        exact ⟨k, by omega, hk'⟩
      · cases hm : c.maxHops with
        | none => simp [Ctx.depthOk, hm] at hd
        | some m =>
          simp only [Ctx.depthOk, hm, Option.all_some, decide_eq_false_iff_not, Nat.not_lt] at hd
          exact ⟨n, by have := hn m hm; omega, hr⟩
    obtain ⟨k, hk, hr'⟩ := this
    exact hF.complete y ((hF.em y).2 ⟨k, hk, t, ht, hr'⟩)

theorem accR_iff {R : HopRel} {e : PathExpr} {d : Dfa} (hd : buildDfa (toRE false e) = .ok d) (x y : Int64) (n : Nat) :
    AccR R d x n y ↔ ∃ w, IsWalk R x w y ∧ word w ∈ lang e ∧ w.length = n :=
  (matchWalk_iff hd x y n).symm

/-- path-evaluation "Reachability mode": when the hop layer lists exactly the hops of `R` and the
automaton is compiled from `e`, a successful REACH search from `x` returns, exactly once each, the
ends `y` of the walks of `R` from `x` whose word is in `lang e` and whose length is within the hop
bound, each with the length of a shortest such walk (and no path value or arrival). -/
theorem reach_spec {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hx : HopsExact st c R) (hd : buildDfa (toRE false e) = .ok c.dfa)
    {rows : List PathRow} (h : ev st (reach c x) = .ok (.ok rows)) :
    (∀ r ∈ rows, r = { start := x, «end» := r.end, hops := r.hops } ∧ Within c.maxHops r.hops ∧
      (∃ w, IsWalk R x w r.end ∧ word w ∈ lang e ∧ w.length = r.hops) ∧
      ∀ w, IsWalk R x w r.end → word w ∈ lang e → r.hops ≤ w.length) ∧
    (∀ y w, IsWalk R x w y → word w ∈ lang e → Within c.maxHops w.length → ∃ r ∈ rows, r.end = y) ∧
    (rows.map PathRow.end).Nodup := by
  obtain ⟨h1, h2, h3⟩ := reach_acc hx h
  refine ⟨fun r hr => ?_, fun y w hw hl hb => h2 y w.length ((accR_iff hd x y _).2 ⟨w, hw, hl, rfl⟩) hb, h3⟩
  obtain ⟨hr1, hr2, hr3, hr4⟩ := h1 r hr
  refine ⟨hr1, hr4, (accR_iff hd x r.end _).1 hr2, fun w hw hl => ?_⟩
  by_contra hlt
  exact hr3 w.length (by omega) ((accR_iff hd x r.end _).2 ⟨w, hw, hl, rfl⟩)

/-! ## Fuel -/

/-- path-evaluation "Termination and search bound" (REACH): with at most `pathMaxStates` charged
states and a non-empty layer only after a charged one, the REACH loop with fuel `f` (where
`f + depth ≥ pathMaxStates + 1`, as for the initial call) has the same outcome as with any larger
fuel — results, errors and limit failures alike. -/
theorem reachLoop_fuel {st : ModelState} {c : Ctx} {x : Int64} :
    ∀ (f k : Nat) (frontier : List SState) (visited : Std.HashSet SState) (emitted : Std.HashSet Int64)
      (depth used : Nat) (rows : List PathRow),
    used ≤ c.limit → (frontier ≠ [] → depth + 1 ≤ used) → c.limit + 1 ≤ f + depth →
    ev st (reachLoop c x f frontier visited emitted depth used rows) =
      ev st (reachLoop c x (f + k) frontier visited emitted depth used rows)
  | 0, k, frontier, visited, emitted, depth, used, rows, hle, hfu, hf => by
    have hfr : frontier = [] := by
      by_contra hne; have := hfu hne; omega
    subst hfr
    cases k with
    | zero => rfl
    | succ k => simp [reachLoop]
  | f + 1, k, frontier, visited, emitted, depth, used, rows, hle, hfu, hf => by
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [reachLoop]
    split
    · rfl
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      apply ev_bind_congr
      rintro ⟨next, vis, em, ends, used'⟩ hl
      obtain ⟨exps, -, hL⟩ := reachLayer_fold hle hl
      obtain ⟨-, -, -, -, -, -, hus, hle'⟩ := hL
      simp only at hus hle'
      refine reachLoop_fuel f k next vis em (depth + 1) used' _ hle' (fun hne => ?_) (by omega)
      have := hfu hc.1; have : 0 < next.length := List.length_pos_of_ne_nil hne; omega

end Tiramemsu.Path
