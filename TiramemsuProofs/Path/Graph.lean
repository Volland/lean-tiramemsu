/-
path-evaluation "Graph-scoped evaluation": a graph-scoped search is the unscoped search over the
hops whose statement has a visible membership in the graph set. On the engine: the scoped hop
layer lists exactly the unscoped hops whose statement passes the scope test, and on a model state
that test is a visible membership `(e sys:inGraph g)`, `g ∈ G`. So a graph-scoped REACH row is an
end of a matching walk every hop of which is in G, and a graph-scoped TRAIL row is exactly an
unscoped TRAIL row whose every hop statement has a visible membership in G; zero-hop rows do not
depend on G.
-/
import TiramemsuProofs.Path.Inverse
import TiramemsuProofs.Query.EvRun
import TiramemsuProofs.Query.Inlj

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Filters on the model -/

theorem ev_filterAuxM {α : Type} (st : ModelState) (p : α → EvM Bool) :
    ∀ (l acc res : List α), Path.ev st (List.filterAuxM p l acc) = .ok (.ok res) →
      ∀ a, a ∈ res ↔ a ∈ acc ∨ (a ∈ l ∧ Path.ev st (p a) = .ok (.ok true))
  | [], acc, res, h, a => by
    simp only [List.filterAuxM] at h
    rw [Path.ev_pure] at h; cases h; simp
  | x :: l, acc, res, h, a => by
    simp only [List.filterAuxM] at h
    obtain ⟨b, hb, h⟩ := Path.ev_bind_ok h
    rw [ev_filterAuxM st p l _ res h a]
    cases b with
    | false =>
      simp only [cond_false, List.mem_cons]
      constructor
      · rintro (h1 | ⟨h1, h2⟩); exact .inl h1; exact .inr ⟨.inr h1, h2⟩
      · rintro (h1 | ⟨rfl | h1, h2⟩)
        · exact .inl h1
        · rw [hb] at h2; cases h2
        · exact .inr ⟨h1, h2⟩
    | true =>
      simp only [cond_true, List.mem_cons]
      constructor
      · rintro ((rfl | h1) | ⟨h1, h2⟩)
        · exact .inr ⟨.inl rfl, hb⟩
        · exact .inl h1
        · exact .inr ⟨.inr h1, h2⟩
      · rintro (h1 | ⟨rfl | h1, h2⟩)
        · exact .inl (.inr h1)
        · exact .inl (.inl rfl)
        · exact .inr ⟨h1, h2⟩

theorem ev_filterM_mem {α : Type} (st : ModelState) (p : α → EvM Bool) (l res : List α)
    (h : Path.ev st (l.filterM p) = .ok (.ok res)) (a : α) :
    a ∈ res ↔ a ∈ l ∧ Path.ev st (p a) = .ok (.ok true) := by
  unfold List.filterM at h
  obtain ⟨r, hr, h⟩ := Path.ev_bind_ok h
  rw [Path.ev_pure] at h; cases h
  rw [List.mem_reverse, ev_filterAuxM st p l [] r hr a]
  simp

theorem ev_filterAuxM_true {α : Type} (st : ModelState) (p : α → EvM Bool) :
    ∀ (l acc : List α), (∀ a ∈ l, Path.ev st (p a) = .ok (.ok true)) →
      Path.ev st (List.filterAuxM p l acc) = .ok (.ok (l.reverse ++ acc))
  | [], acc, _ => by simp only [List.filterAuxM]; rfl
  | x :: l, acc, h => by
    simp only [List.filterAuxM]
    rw [Path.ev_bind, h x (List.mem_cons_self ..)]
    simp only [cond_true]
    rw [ev_filterAuxM_true st p l _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    simp

theorem ev_filterM_true {α : Type} (st : ModelState) (p : α → EvM Bool) (l : List α)
    (h : ∀ a ∈ l, Path.ev st (p a) = .ok (.ok true)) : Path.ev st (l.filterM p) = .ok (.ok l) := by
  unfold List.filterM
  rw [Path.ev_bind, ev_filterAuxM_true st p l [] h]
  simp

theorem ev_filterAuxM_sub {α : Type} (st : ModelState) (p : α → EvM Bool) :
    ∀ (l acc res : List α), Path.ev st (List.filterAuxM p l acc) = .ok (.ok res) →
      ∃ l' : List α, l'.Sublist l ∧ res = l'.reverse ++ acc
  | [], acc, res, h => by
    simp only [List.filterAuxM] at h
    rw [Path.ev_pure] at h; cases h; exact ⟨[], by simp, rfl⟩
  | x :: l, acc, res, h => by
    simp only [List.filterAuxM] at h
    obtain ⟨b, -, h⟩ := Path.ev_bind_ok h
    obtain ⟨l', hl', rfl⟩ := ev_filterAuxM_sub st p l _ res h
    cases b with
    | false => exact ⟨l', hl'.cons _, rfl⟩
    | true => exact ⟨x :: l', hl'.cons₂ _, by simp⟩

theorem ev_filterM_sub {α : Type} (st : ModelState) (p : α → EvM Bool) (l res : List α)
    (h : Path.ev st (l.filterM p) = .ok (.ok res)) : res.Sublist l := by
  unfold List.filterM at h
  obtain ⟨r, hr, h⟩ := Path.ev_bind_ok h
  rw [Path.ev_pure] at h; cases h
  obtain ⟨l', hl', rfl⟩ := ev_filterAuxM_sub st p l [] r hr
  simpa using hl'

/-! ## The scoped hop layer -/

theorem fetchRaw_graphs (c : Ctx) (g : Option (Option Int64 × List Int64)) (lc : LClass) (x : Int64) :
    fetchRaw { c with graphs := g } lc x = fetchRaw c lc x := by
  cases c; rfl

theorem ev_inScope_none {st : ModelState} {c : Ctx} (h : c.graphs = none) (eid : Int64) :
    Path.ev st (inScope c eid) = .ok (.ok true) := by
  unfold inScope; rw [h]; rfl

theorem ev_fetchClass_none {st : ModelState} {c : Ctx} (h : c.graphs = none) (lc : LClass) (x : Int64) :
    Path.ev st (fetchClass c lc x) = Path.ev st (fetchRaw c lc x) := by
  unfold fetchClass
  rw [Path.ev_bind]
  rcases hr : Path.ev st (fetchRaw c lc x) with e | (e | l)
  · rfl
  · rfl
  · exact ev_filterM_true st _ l (fun a _ => ev_inScope_none h _)

/-- The scoped class neighbours are the unscoped ones whose statement passes the scope test. -/
theorem ev_fetchClass_scoped {st : ModelState} {c : Ctx} (g : Option (Option Int64 × List Int64))
    (lc : LClass) (x : Int64) {L' : List Nb}
    (h : Path.ev st (fetchClass { c with graphs := g } lc x) = .ok (.ok L')) :
    ∃ L, Path.ev st (fetchRaw c lc x) = .ok (.ok L) ∧ L'.Sublist L ∧
      ∀ nb, nb ∈ L' ↔ nb ∈ L ∧ Path.ev st (inScope { c with graphs := g } nb.hop.eid) = .ok (.ok true) := by
  unfold fetchClass at h
  obtain ⟨L, hL, h⟩ := Path.ev_bind_ok h
  rw [fetchRaw_graphs] at hL
  exact ⟨L, hL, ev_filterM_sub st _ L L' h, ev_filterM_mem st _ L L' h⟩

theorem ev_mapM_of_forall₂ {α β : Type} (st : ModelState) (f : α → EvM β) :
    ∀ (xs : List α) (ys : List β), List.Forall₂ (fun x y => Path.ev st (f x) = .ok (.ok y)) xs ys →
      Path.ev st (xs.mapM f) = .ok (.ok ys)
  | [], [], .nil => rfl
  | x :: xs, y :: ys, .cons h hr => by
    rw [List.mapM_cons, Path.ev_bind, h]
    simp only
    rw [Path.ev_bind, ev_mapM_of_forall₂ st f xs ys hr]
    rfl

/-- The transitions of a search state through a class-neighbour function (`expandOne`). -/
def expandWith (F : LClass → EvM (List Nb)) (d : Dfa) (q : Nat) : EvM (List (Nb × Nat)) := do
  let parts ← (d.trans.getD q []).mapM fun (ci, t) => do
    let nbs ← F (d.alpha.getD ci (.other .out))
    return nbs.map (·, t)
  return parts.flatten.mergeSort fun a b => keyLe a.1.hop.key b.1.hop.key

theorem expandOne_eq (c : Ctx) (x : Int64) (q : Nat) :
    expandOne c x q = expandWith (fun lc => fetchClass c lc x) c.dfa q := rfl

theorem forall₂_flatten {α : Type} {P : α → Prop} :
    ∀ {ls' ls : List (List α)}, List.Forall₂ (fun l' l => l'.Sublist l ∧ ∀ a, a ∈ l' ↔ a ∈ l ∧ P a) ls' ls →
      ls'.flatten.Sublist ls.flatten ∧ ∀ a, a ∈ ls'.flatten ↔ a ∈ ls.flatten ∧ P a
  | _, _, .nil => by simp
  | l' :: ls', l :: ls, .cons ⟨h1, h2⟩ hr => by
    obtain ⟨r1, r2⟩ := forall₂_flatten hr
    refine ⟨h1.append r1, fun a => ?_⟩
    simp only [List.flatten_cons, List.mem_append, h2, r2]
    tauto

/-- Restricting every class-neighbour list to a predicate restricts the transitions to it. -/
theorem ev_expandWith_restrict {st : ModelState} {F F' : LClass → EvM (List Nb)} {P : Nb → Prop}
    (hF : ∀ lc L', Path.ev st (F' lc) = .ok (.ok L') →
      ∃ L, Path.ev st (F lc) = .ok (.ok L) ∧ L'.Sublist L ∧ ∀ nb, nb ∈ L' ↔ nb ∈ L ∧ P nb)
    (d : Dfa) (q : Nat) {L' : List (Nb × Nat)} (h : Path.ev st (expandWith F' d q) = .ok (.ok L')) :
    ∃ L, Path.ev st (expandWith F d q) = .ok (.ok L) ∧ (∀ a, a ∈ L' ↔ a ∈ L ∧ P a.1) ∧
      ((L.map (·.1.hop)).Nodup → (L'.map (·.1.hop)).Nodup) := by
  unfold expandWith at h
  obtain ⟨parts', hp', h⟩ := Path.ev_bind_ok h
  rw [Path.ev_pure] at h; cases h
  have h2 := ev_mapM_forall₂ st _ _ parts' hp'
  -- the unscoped parts, element by element
  have : ∀ (ts : List (Nat × Nat)) (ps' : List (List (Nb × Nat))),
      List.Forall₂ (fun (p : Nat × Nat) y => Path.ev st (F' (d.alpha.getD p.1 (.other .out)) >>= fun nbs =>
        pure (nbs.map (·, p.2))) = .ok (.ok y)) ts ps' →
      ∃ ps, List.Forall₂ (fun (p : Nat × Nat) y => Path.ev st (F (d.alpha.getD p.1 (.other .out)) >>= fun nbs =>
        pure (nbs.map (·, p.2))) = .ok (.ok y)) ts ps ∧
        List.Forall₂ (fun l' l => l'.Sublist l ∧ ∀ a, a ∈ l' ↔ a ∈ l ∧ P a.1) ps' ps := by
    intro ts ps' hts
    induction hts with
    | nil => exact ⟨[], .nil, .nil⟩
    | @cons p y ts ps' hy _ ih =>
      obtain ⟨ps, h1, h2⟩ := ih
      obtain ⟨nbs', hn', hy⟩ := Path.ev_bind_ok hy
      rw [Path.ev_pure] at hy; cases hy
      obtain ⟨nbs, hn, hsub, hmem⟩ := hF _ _ hn'
      refine ⟨nbs.map (·, p.2) :: ps, .cons (by rw [Path.ev_bind, hn]; rfl) h1, .cons ⟨hsub.map _, ?_⟩ h2⟩
      intro a
      simp only [List.mem_map]
      constructor
      · rintro ⟨nb, hnb, rfl⟩; exact ⟨⟨nb, ((hmem nb).1 hnb).1, rfl⟩, ((hmem nb).1 hnb).2⟩
      · rintro ⟨⟨nb, hnb, rfl⟩, hP⟩; exact ⟨nb, (hmem nb).2 ⟨hnb, hP⟩, rfl⟩
  obtain ⟨ps, hps, hrel⟩ := this _ parts' (h2.imp fun {p y} hy => by obtain ⟨ci, t⟩ := p; exact hy)
  obtain ⟨hsub, hm⟩ := forall₂_flatten hrel
  refine ⟨ps.flatten.mergeSort fun a b => keyLe a.1.hop.key b.1.hop.key, ?_, fun a => ?_, fun hnd => ?_⟩
  · unfold expandWith
    rw [Path.ev_bind, ev_mapM_of_forall₂ st _ _ ps (hps.imp fun {p y} hy => by obtain ⟨ci, t⟩ := p; exact hy)]
    rfl
  · rw [List.mem_mergeSort, List.mem_mergeSort, hm]
  · have p1 := (List.mergeSort_perm ps.flatten (fun a b => keyLe a.1.hop.key b.1.hop.key)).map (·.1.hop)
    have p2 := (List.mergeSort_perm parts'.flatten (fun a b => keyLe a.1.hop.key b.1.hop.key)).map (·.1.hop)
    exact p2.nodup_iff.2 ((hsub.map _).nodup (p1.nodup_iff.1 hnd))

/-- A statement passes the scope test of a search. -/
def ScopeOK (st : ModelState) (c : Ctx) (eid : Int64) : Prop := Path.ev st (inScope c eid) = .ok (.ok true)

/-- The hop layer of a graph-scoped search lists exactly the unscoped hops whose statement passes
the scope test. -/
theorem hopsExact_scoped {st : ModelState} {c : Ctx} {R : HopRel} (hc : c.graphs = none)
    (g : Option (Option Int64 × List Int64)) (hx : HopsExact st c R) :
    HopsExact st { c with graphs := g } (R.scoped (ScopeOK st { c with graphs := g })) := by
  intro x q L' h
  rw [expandOne_eq] at h
  obtain ⟨L, hL, hmem, -⟩ := ev_expandWith_restrict (F := fun lc => fetchClass c lc x)
    (P := fun nb => ScopeOK st { c with graphs := g } nb.hop.eid) (fun lc L' h' => by
      obtain ⟨L, hL, hs, hm⟩ := ev_fetchClass_scoped g lc x h'
      exact ⟨L, by rw [ev_fetchClass_none hc]; exact hL, hs, hm⟩) c.dfa q h
  rw [← expandOne_eq] at hL
  intro nb t
  rw [hmem, hx x q L hL nb t]
  simp only [PStep, HopRel.scoped]
  constructor
  · rintro ⟨⟨l, h1, h2⟩, h3⟩; exact ⟨l, ⟨h1, h3⟩, h2⟩
  · rintro ⟨l, ⟨h1, h3⟩, h2⟩; exact ⟨⟨l, h1, h2⟩, h3⟩

theorem hopsNodup_scoped {st : ModelState} {c : Ctx} (hc : c.graphs = none)
    (g : Option (Option Int64 × List Int64)) (hn : HopsNodup st c) : HopsNodup st { c with graphs := g } := by
  intro x q L' h
  rw [expandOne_eq] at h
  obtain ⟨L, hL, -, hnd⟩ := ev_expandWith_restrict (F := fun lc => fetchClass c lc x)
    (P := fun nb => ScopeOK st { c with graphs := g } nb.hop.eid) (fun lc L' h' => by
      obtain ⟨L, hL, hs, hm⟩ := ev_fetchClass_scoped g lc x h'
      exact ⟨L, by rw [ev_fetchClass_none hc]; exact hL, hs, hm⟩) c.dfa q h
  rw [← expandOne_eq] at hL
  exact hnd (hn x q L hL)

/-- On a model state the scope test is a visible membership `(e sys:inGraph g)`, `g ∈ G`; without
a `sys:inGraph` id no statement passes. -/
theorem scopeOK_iff {st : ModelState} {c : Ctx} {ig : Int64} {gs : List Int64}
    (h : c.graphs = some (some ig, gs)) (eid : Int64) :
    ScopeOK st c eid ↔ InGraphs st c.view ig gs eid := by
  unfold ScopeOK inScope
  rw [h]
  simp only
  have hs : Path.ev st (liftR (rangeScan .spo c.view [eid, ig])) =
      .ok (.ok (st.scanList (scanSpec .spo c.view [eid, ig]))) := Exec.ev_rangeScan st .spo c.view [eid, ig] (by simp)
  rw [Path.ev_bind, hs]
  simp only [Path.ev_pure, Except.ok.injEq, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨m, hm, hg⟩
    obtain ⟨hm1, hm2⟩ := Engine.mem_scanList_iff.1 hm
    rw [scan_matches_iff, Bool.and_eq_true] at hm2
    have hp := prefixOk_indexFor c.view (some eid) (some ig) none m
    simp only [indexFor] at hp
    rw [hp] at hm2
    simp only [optOk, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hm2
    exact ⟨m, hm1, hm2.1, hm2.2.1, hm2.2.2, hg⟩
  · rintro ⟨m, hm1, hm2, hm3, hm4, hg⟩
    refine ⟨m, Engine.mem_scanList_iff.2 ⟨hm1, ?_⟩, hg⟩
    rw [scan_matches_iff, Bool.and_eq_true]
    have hp := prefixOk_indexFor c.view (some eid) (some ig) none m
    simp only [indexFor] at hp
    rw [hp]
    simp [optOk, hm2, hm3, hm4]

theorem scopeOK_none {st : ModelState} {c : Ctx} {gs : List Int64} (h : c.graphs = some (none, gs)) (eid : Int64) :
    ¬ ScopeOK st c eid := by
  unfold ScopeOK inScope; rw [h]; simp

/-! ## Graph-scoped searches -/

/-- path-evaluation "Graph-scoped evaluation" (REACH): a graph-scoped REACH search returns each end
of a matching walk within the bound every hop of which has its statement in scope, once, with the
length of a shortest such walk (zero-hop rows do not depend on the scope). -/
theorem reach_graph {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hc : c.graphs = none) (g : Option (Option Int64 × List Int64)) (hx : HopsExact st c R)
    (hd : buildDfa (toRE false e) = .ok c.dfa) {rows : List PathRow}
    (h : ev st (reach { c with graphs := g } x) = .ok (.ok rows)) :
    let G := ScopeOK st { c with graphs := g }
    (∀ r ∈ rows, r = { start := x, «end» := r.end, hops := r.hops } ∧ Within c.maxHops r.hops ∧
      (∃ w, IsWalk R x w r.end ∧ (∀ s ∈ w, G s.2.hop.eid) ∧ word w ∈ lang e ∧ w.length = r.hops) ∧
      ∀ w, IsWalk R x w r.end → (∀ s ∈ w, G s.2.hop.eid) → word w ∈ lang e → r.hops ≤ w.length) ∧
    (∀ y w, IsWalk R x w y → (∀ s ∈ w, G s.2.hop.eid) → word w ∈ lang e → Within c.maxHops w.length →
      ∃ r ∈ rows, r.end = y) ∧
    (rows.map PathRow.end).Nodup := by
  intro G
  obtain ⟨h1, h2, h3⟩ := reach_spec (hopsExact_scoped hc g hx) hd h
  refine ⟨fun r hr => ?_, fun y w hw hg hl hb => h2 y w ((isWalk_scoped R G x y w).2 ⟨hw, hg⟩) hl hb, h3⟩
  obtain ⟨r1, r2, ⟨w, hw, hl, hlen⟩, r4⟩ := h1 r hr
  obtain ⟨hw', hg⟩ := (isWalk_scoped R G x r.end w).1 hw
  exact ⟨r1, r2, ⟨w, hw', hg, hl, hlen⟩, fun w hw hg hl => r4 w ((isWalk_scoped R G x r.end w).2 ⟨hw, hg⟩) hl⟩

theorem walkTau_graphs (c : Ctx) (g : Option (Option Int64 × List Int64)) :
    ∀ (w : List Step) (τ : Option Int), walkTau { c with graphs := g } w τ = walkTau c w τ
  | [], τ => rfl
  | s :: w, τ => by
    simp only [walkTau]
    rw [show ({ c with graphs := g } : Ctx).tstep s.2 τ = c.tstep s.2 τ from rfl]
    cases c.tstep s.2 τ with
    | none => rfl
    | some τ' => exact walkTau_graphs c g w τ'

/-- path-evaluation "Graph-scoped evaluation" (TRAIL): a graph-scoped TRAIL row is exactly an
unscoped TRAIL row every hop statement of which is in scope. -/
theorem trail_graph {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hc : c.graphs = none) (g : Option (Option Int64 × List Int64)) (hx : HopsExact st c R)
    (hnd : HopsNodup st c) (hd : buildDfa (toRE false e) = .ok c.dfa) {rows rowsG : List PathRow}
    (h : ev st (trail c x) = .ok (.ok rows)) (hG : ev st (trail { c with graphs := g } x) = .ok (.ok rowsG))
    (r : PathRow) :
    r ∈ rowsG ↔ r ∈ rows ∧ ∀ p ∈ r.path, ∀ hp ∈ p.hops, ScopeOK st { c with graphs := g } hp.eid := by
  have hS := (trail_spec hx hnd hd h).1
  have hSG := (trail_spec (hopsExact_scoped hc g hx) (hopsNodup_scoped hc g hnd) hd hG).1
  have hrow : ∀ w τ, walkRow { c with graphs := g } x w τ = walkRow c x w τ := fun _ _ => rfl
  have hpath : ∀ {y} w τ, IsWalk R x w y → ((∀ p ∈ (walkRow c x w τ).path, ∀ hp ∈ p.hops,
      ScopeOK st { c with graphs := g } hp.eid) ↔ ∀ s ∈ w, ScopeOK st { c with graphs := g } s.2.hop.eid) := by
    intro y w τ hw
    rw [walkRow_eq hw]
    constructor
    · intro hh s hs
      exact hh _ rfl _ (List.mem_map.2 ⟨s, hs, rfl⟩)
    · intro hh p hp hp' hmem
      simp only [Option.mem_def, Option.some.injEq] at hp
      subst hp
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hmem
      exact hh s hs
  rw [hSG, hS]
  constructor
  · rintro ⟨y, w, τ, hw, htr, hl, hb, ht, rfl⟩
    obtain ⟨hw', hg⟩ := (isWalk_scoped R _ x y w).1 hw
    rw [hrow]
    rw [walkTau_graphs] at ht
    exact ⟨⟨y, w, τ, hw', htr, hl, hb, ht, rfl⟩, (hpath w τ hw').2 hg⟩
  · rintro ⟨⟨y, w, τ, hw, htr, hl, hb, ht, rfl⟩, hg⟩
    exact ⟨y, w, τ, (isWalk_scoped R _ x y w).2 ⟨hw, (hpath w τ hw).1 hg⟩, htr, hl, hb,
      by rw [walkTau_graphs]; exact ht, rfl⟩

/-- path-evaluation "Graph-scoped evaluation" (TRAIL, on a model state): with the graph set `gs`
(and the `sys:inGraph` id `ig`), a graph-scoped row is exactly an unscoped row every hop statement
of which has a visible membership `(e sys:inGraph g)`, `g ∈ gs`, in the path's view. -/
theorem trail_graph_members {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr}
    (hc : c.graphs = none) (ig : Int64) (gs : List Int64) (hx : HopsExact st c R)
    (hnd : HopsNodup st c) (hd : buildDfa (toRE false e) = .ok c.dfa) {rows rowsG : List PathRow}
    (h : ev st (trail c x) = .ok (.ok rows))
    (hG : ev st (trail { c with graphs := some (some ig, gs) } x) = .ok (.ok rowsG)) (r : PathRow) :
    r ∈ rowsG ↔ r ∈ rows ∧ ∀ p ∈ r.path, ∀ hp ∈ p.hops, InGraphs st c.view ig gs hp.eid := by
  rw [trail_graph hc _ hx hnd hd h hG r]
  simp only [scopeOK_iff (c := { c with graphs := some (some ig, gs) }) rfl]

end Tiramemsu.Path
