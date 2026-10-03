/-
path-evaluation "Endpoint binding": a walk read backwards is a walk of a reversible hop relation
whose word is the reversed, direction-flipped word, so the walks matching `^e` from the end are
exactly the reversed walks matching `e` into it. With the REACH and TRAIL theorems this gives:
evaluating from the end with the inverse expression yields exactly the reversed rows of
evaluating from the start (as the engine does for a path pattern bound only at its end).
-/
import TiramemsuProofs.Path.Trail

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Walks read backwards -/

/-- The neighbour reached by stepping back over a hop to `x`. -/
def Nb.back (nb : Nb) (x : Int64) : Nb := ⟨{ nb.hop with dir := nb.hop.dir.flip }, x, nb.vFrom, nb.vTo⟩

@[simp] theorem Nb.back_to (nb : Nb) (x : Int64) : (nb.back x).to = x := rfl
@[simp] theorem Nb.back_identity (nb : Nb) (x : Int64) : (nb.back x).hop.identity = nb.hop.identity := rfl

/-- A reversible hop relation: every hop can be taken backwards with the flipped letter (true of
`ViewHop`: a stored hop's inverse steps over the same statement, a virtual hop's inverse from the
part back to the statement). -/
def HopRel.Symm (R : HopRel) : Prop := ∀ x l nb, R x l nb → R nb.to l.flip (nb.back x)

/-- The hops of a store view are reversible. -/
theorem viewHop_symm (st : ModelState) (V : Store.View) (rel : Int64 → Int64 → Bool) :
    (ViewHop st V rel).Symm := by
  intro x l nb h
  cases h with
  | out hr hv hd => exact .inn hr hv hd
  | inn hr hv hd => exact .out hr hv hd
  | virtOut k hr hv => exact .virtIn k hr hv
  | virtIn k hr hv => exact .virtOut k hr hv

/-- Graph scoping keeps a relation reversible (a hop and its reverse step over one statement). -/
theorem scoped_symm {R : HopRel} (hS : R.Symm) (G : Int64 → Prop) : (R.scoped G).Symm :=
  fun x l nb h => ⟨hS x l nb h.1, h.2⟩

/-- A walk from `x` read backwards (from its end). -/
def revWalk : Int64 → List Step → List Step
  | _, [] => []
  | x, s :: w => revWalk s.2.to w ++ [(s.1.flip, s.2.back x)]

theorem isWalk_rev {R : HopRel} (hS : R.Symm) : ∀ (x y : Int64) (w : List Step),
    IsWalk R x w y → IsWalk R y (revWalk x w) x
  | x, y, [], h => by simp only [isWalk_nil] at h ⊢; exact h.symm
  | x, y, s :: w, h => by
    simp only [revWalk]
    rw [isWalk_snoc]
    exact ⟨s.2.to, isWalk_rev hS s.2.to y w h.2, hS x s.1 s.2 h.1, rfl⟩

theorem word_rev : ∀ (x : Int64) (w : List Step), word (revWalk x w) = flipRev (word w)
  | x, [] => rfl
  | x, s :: w => by
    simp only [revWalk, word_append, word_rev s.2.to w, word_cons, word_nil, flipRev, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil]

theorem length_rev : ∀ (x : Int64) (w : List Step), (revWalk x w).length = w.length
  | x, [] => rfl
  | x, s :: w => by simp [revWalk, length_rev s.2.to w]

theorem ids_rev : ∀ (x : Int64) (w : List Step),
    (revWalk x w).map (·.2.hop.identity) = (w.map (·.2.hop.identity)).reverse
  | x, [] => rfl
  | x, s :: w => by
    simp only [revWalk, List.map_append, ids_rev s.2.to w, List.map_cons, List.map_nil, Nb.back_identity,
      List.reverse_cons]

theorem isTrail_rev (x : Int64) (w : List Step) (h : IsTrail w) : IsTrail (revWalk x w) := by
  unfold IsTrail; rw [ids_rev]; exact List.nodup_reverse.2 h

/-- The path value of a reversed walk is the reversed path value. -/
theorem pathOf_rev {R : HopRel} : ∀ (x y : Int64) (w : List Step), IsWalk R x w y →
    pathOf y (revWalk x w) = (pathOf x w).reversed
  | x, y, [], h => by simp only [isWalk_nil] at h; subst h; rfl
  | x, y, s :: w, h => by
    have ih := pathOf_rev s.2.to y w h.2
    simp only [pathOf, PathValue.reversed, PathValue.mk.injEq] at ih ⊢
    simp only [revWalk, List.map_append, List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩
    · rw [← List.cons_append, ih.1]
      simp
    · rw [ih.2]; simp [Nb.back]

/-- path-evaluation "Endpoint binding" (specification): for a reversible hop relation, the walks
from `y` matching `^e` are exactly the reversed walks into `y` matching `e`, length for length. -/
theorem matchWalk_inv {R : HopRel} (hS : R.Symm) (e : PathExpr) (x y : Int64) (n : Nat) :
    (∃ w, IsWalk R y w x ∧ word w ∈ lang (.inv e) ∧ w.length = n) ↔
      (∃ w, IsWalk R x w y ∧ word w ∈ lang e ∧ w.length = n) := by
  constructor
  · rintro ⟨w, h1, h2, h3⟩
    refine ⟨revWalk y w, isWalk_rev hS y x w h1, ?_, by rw [length_rev, h3]⟩
    rw [word_rev]; exact (mem_lang_inv e _).1 h2
  · rintro ⟨w, h1, h2, h3⟩
    refine ⟨revWalk x w, isWalk_rev hS x y w h1, ?_, by rw [length_rev, h3]⟩
    rw [mem_lang_inv, word_rev, flipRev_flipRev]; exact h2

/-! ## Evaluation from the end -/

/-- A row of an evaluation from the end, read from the start (the engine's reversal for a path
pattern bound only at its end). -/
def PathRow.flip (r : PathRow) : PathRow :=
  { r with start := r.end, «end» := r.start, path := r.path.map PathValue.reversed }

theorem PathValue.reversed_reversed (p : PathValue) : p.reversed.reversed = p := by
  obtain ⟨n, h⟩ := p
  simp only [PathValue.reversed, List.reverse_reverse, List.map_reverse, List.map_map, PathValue.mk.injEq,
    true_and]
  conv_rhs => rw [← List.map_id h]
  apply List.map_congr_left
  intro x _
  simp [Dir.flip_flip]

/-- path-evaluation "Endpoint binding" (REACH): with a reversible hop relation, the rows into `y`
of the search from `x` for `e` are exactly the reversed rows from `x` of the search from `y` for
`^e` (same hop bound). -/
theorem reach_fromEnd {st : ModelState} {c c' : Ctx} {R : HopRel} {x y : Int64} {e : PathExpr}
    (hS : R.Symm) (hx : HopsExact st c R) (hx' : HopsExact st c' R)
    (hd : buildDfa (toRE false e) = .ok c.dfa) (hd' : buildDfa (toRE false (.inv e)) = .ok c'.dfa)
    (hb : c'.maxHops = c.maxHops) {rowsS rowsE : List PathRow}
    (hs : ev st (reach c x) = .ok (.ok rowsS)) (he : ev st (reach c' y) = .ok (.ok rowsE)) (r : PathRow) :
    (r ∈ rowsS ∧ r.end = y) ↔ (r ∈ rowsE.map PathRow.flip ∧ r.start = x) := by
  obtain ⟨hS1, hS2, -⟩ := reach_spec hx hd hs
  obtain ⟨hE1, hE2, -⟩ := reach_spec hx' hd' he
  constructor
  · rintro ⟨hr, rfl⟩
    obtain ⟨hr1, hr2, ⟨w, hw1, hw2, hw3⟩, hr4⟩ := hS1 r hr
    obtain ⟨w', hw'1, hw'2, hw'3⟩ := (matchWalk_inv hS e x r.end r.hops).2 ⟨w, hw1, hw2, hw3⟩
    obtain ⟨r2, hr2m, hr2e⟩ := hE2 x w' hw'1 hw'2 (by rw [hb, hw'3]; exact hr2)
    obtain ⟨h21, -, ⟨v, hv1, hv2, hv3⟩, h24⟩ := hE1 r2 hr2m
    rw [hr2e] at hv1 h24
    have hle1 : r2.hops ≤ r.hops := hw'3 ▸ h24 w' hw'1 hw'2
    obtain ⟨v', hv'1, hv'2, hv'3⟩ := (matchWalk_inv hS e x r.end r2.hops).1 ⟨v, hv1, hv2, hv3⟩
    have hle2 : r.hops ≤ r2.hops := hv'3 ▸ hr4 v' hv'1 hv'2
    refine ⟨List.mem_map.2 ⟨r2, hr2m, ?_⟩, by rw [hr1]⟩
    rw [h21, hr1, hr2e]
    simp only [PathRow.flip, Option.map_none]
    congr 1 <;> first | rfl | omega
  · rintro ⟨hr, hstart⟩
    obtain ⟨r2, hr2m, rfl⟩ := List.mem_map.1 hr
    obtain ⟨h21, h22, ⟨v, hv1, hv2, hv3⟩, h24⟩ := hE1 r2 hr2m
    have hx2 : r2.end = x := hstart
    rw [hx2] at hv1 h24
    obtain ⟨v', hv'1, hv'2, hv'3⟩ := (matchWalk_inv hS e x y r2.hops).1 ⟨v, hv1, hv2, hv3⟩
    obtain ⟨r1, hr1m, hr1e⟩ := hS2 y v' hv'1 hv'2 (by rw [hv'3, ← hb]; exact h22)
    obtain ⟨h11, -, ⟨u, hu1, hu2, hu3⟩, h14⟩ := hS1 r1 hr1m
    rw [hr1e] at hu1 h14
    have hle1 : r1.hops ≤ r2.hops := hv'3 ▸ h14 v' hv'1 hv'2
    obtain ⟨u', hu'1, hu'2, hu'3⟩ := (matchWalk_inv hS e x y r1.hops).2 ⟨u, hu1, hu2, hu3⟩
    have hle2 : r2.hops ≤ r1.hops := hu'3 ▸ h24 u' hu'1 hu'2
    have hflip : r2.flip = r1 := by
      rw [h11, h21, hx2, hr1e]
      simp only [PathRow.flip, Option.map_none]
      congr 1; omega
    refine ⟨hflip ▸ hr1m, ?_⟩
    rw [hflip, hr1e]

theorem walkTau_untimed {c : Ctx} (h : c.timed = none) : ∀ (w : List Step) (τ : Option Int), walkTau c w τ = some τ
  | [], τ => rfl
  | s :: w, τ => by simp only [walkTau, Ctx.tstep, h, Option.bind_some]; exact walkTau_untimed h w τ

theorem isWalk_mono {R R' : HopRel} (h : ∀ x l nb, R x l nb → R' x l nb) :
    ∀ (x y : Int64) (w : List Step), IsWalk R x w y → IsWalk R' x w y
  | x, y, [], hw => hw
  | x, y, s :: w, hw => ⟨h _ _ _ hw.1, isWalk_mono h s.2.to y w hw.2⟩

/-- The trivial hop relation: every hop. -/
def anyHop : HopRel := fun _ _ _ => True

theorem flip_walkRow {R : HopRel} {c c' : Ctx} {x y : Int64} {w : List Step} (hc : c.timed = none)
    (hc' : c'.timed = none) (hw : IsWalk R x w y) :
    (walkRow c' y (revWalk x w) none).flip = walkRow c x w none := by
  have hw0 : IsWalk anyHop x w y := isWalk_mono (fun _ _ _ _ => trivial) x y w hw
  have hw' : IsWalk anyHop y (revWalk x w) x := isWalk_rev (fun _ _ _ _ => trivial) x y w hw0
  rw [walkRow_eq hw', walkRow_eq hw, pathOf_rev x y w hw0]
  simp [PathRow.flip, PathValue.reversed_reversed, length_rev, arrivalOf, hc, hc']

theorem flip_walkRow' {R : HopRel} {c c' : Ctx} {x y : Int64} {w : List Step} (hc : c.timed = none)
    (hc' : c'.timed = none) (hw : IsWalk R y w x) :
    (walkRow c' y w none).flip = walkRow c x (revWalk y w) none := by
  have hw0 : IsWalk anyHop y w x := isWalk_mono (fun _ _ _ _ => trivial) y x w hw
  have hw' : IsWalk anyHop x (revWalk y w) y := isWalk_rev (fun _ _ _ _ => trivial) y x w hw0
  rw [walkRow_eq hw', walkRow_eq hw, pathOf_rev y x w hw0]
  simp [PathRow.flip, length_rev, arrivalOf, hc, hc']

/-- path-evaluation "Endpoint binding" (TRAIL): with a reversible hop relation, the rows into `y`
of the TRAIL search from `x` for `e` are exactly the reversed rows from `x` of the TRAIL search
from `y` for `^e` (same hop bound, neither time-respecting): same trails, path values read from
start to end. -/
theorem trail_fromEnd {st : ModelState} {c c' : Ctx} {R : HopRel} {x y : Int64} {e : PathExpr}
    (hS : R.Symm) (hx : HopsExact st c R) (hnd : HopsNodup st c) (hx' : HopsExact st c' R)
    (hnd' : HopsNodup st c') (hd : buildDfa (toRE false e) = .ok c.dfa)
    (hd' : buildDfa (toRE false (.inv e)) = .ok c'.dfa) (hb : c'.maxHops = c.maxHops)
    (hc : c.timed = none) (hc' : c'.timed = none) {rowsS rowsE : List PathRow}
    (hs : ev st (trail c x) = .ok (.ok rowsS)) (he : ev st (trail c' y) = .ok (.ok rowsE)) (r : PathRow) :
    (r ∈ rowsS ∧ r.end = y) ↔ (r ∈ rowsE.map PathRow.flip ∧ r.start = x) := by
  have hS1 := (trail_spec hx hnd hd hs).1
  have hE1 := (trail_spec hx' hnd' hd' he).1
  have hτ : ∀ (c : Ctx), c.timed = none → ∀ w τ, walkTau c w (c.timed.getD none) = some τ → τ = none := by
    intro c hc w τ h; rw [walkTau_untimed hc, hc] at h; cases h; rfl
  constructor
  · rintro ⟨hr, hend⟩
    obtain ⟨y0, w, τ, hw, htr, hl, hwb, hwt, rfl⟩ := (hS1 r).1 hr
    cases hτ c hc w τ hwt
    have hy : y0 = y := by rw [← hend, walkRow_eq hw]
    subst hy
    refine ⟨List.mem_map.2 ⟨walkRow c' y0 (revWalk x w) none, (hE1 _).2 ⟨x, revWalk x w, none,
      isWalk_rev hS x y0 w hw, isTrail_rev x w htr, ?_, by rw [length_rev, hb]; exact hwb,
      by rw [walkTau_untimed hc', hc']; rfl, rfl⟩, flip_walkRow hc hc' hw⟩, by rw [walkRow_eq hw]⟩
    rw [mem_lang_inv, word_rev, flipRev_flipRev]; exact hl
  · rintro ⟨hr, hstart⟩
    obtain ⟨r2, hr2m, rfl⟩ := List.mem_map.1 hr
    obtain ⟨x0, w, τ, hw, htr, hl, hwb, hwt, rfl⟩ := (hE1 r2).1 hr2m
    cases hτ c' hc' w τ hwt
    have hx0 : x0 = x := by rw [← hstart, flip_walkRow' hc hc' hw, walkRow_eq (isWalk_rev hS y x0 w hw)]
    subst hx0
    rw [flip_walkRow' hc hc' hw]
    refine ⟨(hS1 _).2 ⟨y, revWalk y w, none, isWalk_rev hS y x0 w hw, isTrail_rev y w htr, ?_,
      by rw [length_rev, ← hb]; exact hwb, by rw [walkTau_untimed hc, hc]; rfl, rfl⟩,
      by rw [walkRow_eq (isWalk_rev hS y x0 w hw)]⟩
    rw [word_rev]; exact (mem_lang_inv e _).1 hl

end Tiramemsu.Path
