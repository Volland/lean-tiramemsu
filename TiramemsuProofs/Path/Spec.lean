/-
The declarative path specification (path-evaluation "Path expression language" and "Hop
semantics"), written without automata or search:

- `lang e`: the words (hop-letter sequences) of a path expression, a set defined by the operators;
- `IsWalk R x w y`: a walk from `x` to `y` whose steps are hops of a hop relation `R` (each step a
  letter and the neighbour reached: the hop and its target), with its word, length and path value;
- `ViewHop`: the hop relation of a store view — stored hops forward and inverse over each visible
  statement, virtual hops between a visible statement and its parts;
- trails (no repeated hop identity), time-respecting walks (the hop rule threaded through the
  steps), graph scoping (every hop's statement in the scope) and reversal (a walk read backwards
  is a walk of the flipped relation).

The search theorems (`Reach`, `Trail`, `Timed`, `Graph`, `Inverse`) relate the engine to this
specification through `HopsExact`: the hop layer of a search lists exactly the hops of `R`,
routed by the automaton's transition function.
-/
import TiramemsuProofs.Path.Expr
import TiramemsuProofs.Path.Fuel

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Languages and walks -/

/-- The words of a path expression (path-evaluation "Path expression language"). -/
def lang (e : PathExpr) : Set (List Letter) := {w | e.Lang w}

theorem mem_lang (e : PathExpr) (w : List Letter) : w ∈ lang e ↔ e.Lang w := Iff.rfl

/-- `lang (^e)` is the reversed, direction-flipped words of `lang e`. -/
theorem mem_lang_inv (e : PathExpr) (w : List Letter) : w ∈ lang (.inv e) ↔ flipRev w ∈ lang e :=
  lang_inverse e w

/-- A hop relation: `R x l nb` — from node `x`, a hop with letter `l` reaching the neighbour `nb`
(the hop's statement, predicate, direction and kind, and the node reached). -/
abbrev HopRel := Int64 → Letter → Nb → Prop

/-- A walk step: its letter and the neighbour it reaches. -/
abbrev Step := Letter × Nb

/-- `w` is a walk of `R` from `x` to `y`. -/
def IsWalk (R : HopRel) : Int64 → List Step → Int64 → Prop
  | x, [], y => x = y
  | x, s :: w, y => R x s.1 s.2 ∧ IsWalk R s.2.to w y

/-- The word of a walk. -/
def word (w : List Step) : List Letter := w.map (·.1)

/-- Within an optional hop bound. -/
def Within (b : Option Nat) (n : Nat) : Prop := ∀ m, b = some m → n ≤ m

/-- The path value of a walk from `x`: `hops + 1` nodes and the hops. -/
def pathOf (x : Int64) (w : List Step) : PathValue :=
  { nodes := x :: w.map (·.2.to), hops := w.map (·.2.hop) }

/-- A trail: no hop identity repeats (a stored statement in either direction is one identity; a
virtual hop's identity is its statement and kind). -/
def IsTrail (w : List Step) : Prop := (w.map (·.2.hop.identity)).Nodup

@[simp] theorem isWalk_nil (R : HopRel) (x y : Int64) : IsWalk R x [] y ↔ x = y := Iff.rfl

@[simp] theorem isWalk_cons (R : HopRel) (x y : Int64) (s : Step) (w : List Step) :
    IsWalk R x (s :: w) y ↔ R x s.1 s.2 ∧ IsWalk R s.2.to w y := Iff.rfl

theorem isWalk_append (R : HopRel) : ∀ (x z : Int64) (u v : List Step),
    IsWalk R x (u ++ v) z ↔ ∃ y, IsWalk R x u y ∧ IsWalk R y v z
  | x, z, [], v => by simp
  | x, z, s :: u, v => by
    simp only [List.cons_append, isWalk_cons, isWalk_append R s.2.to z u v]
    constructor
    · rintro ⟨h, y, h1, h2⟩; exact ⟨y, ⟨h, h1⟩, h2⟩
    · rintro ⟨y, ⟨h, h1⟩, h2⟩; exact ⟨h, y, h1, h2⟩

theorem isWalk_snoc (R : HopRel) (x z : Int64) (u : List Step) (s : Step) :
    IsWalk R x (u ++ [s]) z ↔ ∃ y, IsWalk R x u y ∧ R y s.1 s.2 ∧ s.2.to = z := by
  rw [isWalk_append]; simp

@[simp] theorem word_nil : word [] = [] := rfl
@[simp] theorem word_cons (s : Step) (w : List Step) : word (s :: w) = s.1 :: word w := rfl
@[simp] theorem word_append (u v : List Step) : word (u ++ v) = word u ++ word v := by simp [word]
@[simp] theorem length_word (w : List Step) : (word w).length = w.length := by simp [word]

/-- The ends a walk can only take from its start. -/
theorem isWalk_end_unique {R : HopRel} : ∀ {x y y' : Int64} {w : List Step},
    IsWalk R x w y → IsWalk R x w y' → y = y'
  | _, _, _, [], h, h' => h.symm.trans h'
  | _, _, _, _ :: _, h, h' => isWalk_end_unique h.2 h'.2

/-! ## The hops of a store view -/

/-- The neighbour of a virtual hop over statement `r`: forward to the part, inverse to `r`. -/
def virtNb (k : VKind) (d : Dir) (r : TripleRow) : Nb :=
  ⟨⟨r.eid, virtualPredId k, d, k.code⟩, if d == .out then k.part r else r.eid, r.vFrom, r.vTo⟩

/-- The hop relation of a store view (path-evaluation "Hop semantics"). A forward stored hop
steps from `s` to `o` over each visible statement `(s p o)`, its inverse from `o` to `s`; its
letter is the predicate's IRI with the relationship-view flag `rel p o`. A forward virtual hop
steps from a visible statement to its subject, object or predicate; its inverse from the part to
the statement. -/
inductive ViewHop (st : ModelState) (V : Store.View) (rel : Int64 → Int64 → Bool) : HopRel
  | out {r : TripleRow} {iri : String} : r ∈ st.triples → V.admits r = true →
      Sem.decodeId st r.p = .ok (.iri iri) →
      ViewHop st V rel r.s (.stored iri (rel r.p r.o) .out) (storedNb .out r.s r)
  | inn {r : TripleRow} {iri : String} : r ∈ st.triples → V.admits r = true →
      Sem.decodeId st r.p = .ok (.iri iri) →
      ViewHop st V rel r.o (.stored iri (rel r.p r.o) .inn) (storedNb .inn r.o r)
  | virtOut {r : TripleRow} (k : VKind) : r ∈ st.triples → V.admits r = true →
      ViewHop st V rel r.eid (.virt k .out) (virtNb k .out r)
  | virtIn {r : TripleRow} (k : VKind) : r ∈ st.triples → V.admits r = true →
      ViewHop st V rel (k.part r) (.virt k .inn) (virtNb k .inn r)

/-- A statement has a visible membership `(e sys:inGraph g)`, `g ∈ gs`, in the view. -/
def InGraphs (st : ModelState) (V : Store.View) (inGraph : Int64) (gs : List Int64) (e : Int64) : Prop :=
  ∃ m ∈ st.triples, V.admits m = true ∧ m.s = e ∧ m.p = inGraph ∧ m.o ∈ gs

/-- A hop relation confined to the hops whose statement satisfies `G`. -/
def HopRel.scoped (R : HopRel) (G : Int64 → Prop) : HopRel := fun x l nb => R x l nb ∧ G nb.hop.eid

/-- Graph scoping is a filter on walks: a walk of the scoped relation is exactly a walk of the
relation every hop of which has its statement in the scope (zero-hop walks do not depend on it). -/
theorem isWalk_scoped (R : HopRel) (G : Int64 → Prop) : ∀ (x y : Int64) (w : List Step),
    IsWalk (R.scoped G) x w y ↔ IsWalk R x w y ∧ ∀ s ∈ w, G s.2.hop.eid
  | x, y, [] => by simp
  | x, y, s :: w => by
    simp only [isWalk_cons, HopRel.scoped, isWalk_scoped R G s.2.to y w, List.mem_cons, forall_eq_or_imp]
    tauto

/-! ## Walks through the automaton -/

theorem runL_append (d : Dfa) : ∀ (q : Nat) (u v : List Letter),
    d.runL q (u ++ v) = (d.runL q u).bind fun q' => d.runL q' v
  | q, [], v => rfl
  | q, l :: u, v => by
    simp only [List.cons_append, Dfa.runL]
    cases d.stepL q l with
    | none => rfl
    | some q' => exact runL_append d q' u v

/-- A search state `(node, automaton state)`. -/
abbrev SState := Int64 × Nat

/-- `PRf R d a n b`: a walk of `n` hops from `a.1` to `b.1` on which the automaton runs from
`a.2` to `b.2`. -/
def PRf (R : HopRel) (d : Dfa) (a : SState) (n : Nat) (b : SState) : Prop :=
  ∃ w : List Step, w.length = n ∧ IsWalk R a.1 w b.1 ∧ d.runL a.2 (word w) = some b.2

/-- One search transition: a hop of `R` whose letter the automaton takes from `a.2` to `t`. -/
def PStep (R : HopRel) (d : Dfa) (a : SState) (nb : Nb) (t : Nat) : Prop :=
  ∃ l, R a.1 l nb ∧ d.stepL a.2 l = some t

theorem prf_zero (R : HopRel) (d : Dfa) (a b : SState) : PRf R d a 0 b ↔ b = a := by
  constructor
  · rintro ⟨w, hw, h1, h2⟩
    rw [List.length_eq_zero_iff] at hw; subst hw
    simp [Dfa.runL] at h1 h2
    exact Prod.ext h1.symm h2.symm
  · rintro rfl; exact ⟨[], rfl, rfl, rfl⟩

theorem prf_add (R : HopRel) (d : Dfa) (a c : SState) (m n : Nat) :
    PRf R d a (m + n) c ↔ ∃ b, PRf R d a m b ∧ PRf R d b n c := by
  constructor
  · rintro ⟨w, hw, h1, h2⟩
    have hm : m ≤ w.length := by omega
    obtain ⟨u, v, rfl, hu⟩ : ∃ u v, w = u ++ v ∧ u.length = m :=
      ⟨w.take m, w.drop m, (List.take_append_drop m w).symm, by simp; omega⟩
    rw [isWalk_append] at h1
    obtain ⟨y, hy1, hy2⟩ := h1
    rw [word_append, runL_append] at h2
    cases hq : d.runL a.2 (word u) with
    | none => rw [hq] at h2; cases h2
    | some q' =>
      rw [hq] at h2
      refine ⟨(y, q'), ⟨u, hu, hy1, hq⟩, v, ?_, hy2, h2⟩
      simp at hw; omega
  · rintro ⟨b, ⟨u, hu, hu1, hu2⟩, v, hv, hv1, hv2⟩
    refine ⟨u ++ v, by simp; omega, (isWalk_append ..).2 ⟨b.1, hu1, hv1⟩, ?_⟩
    rw [word_append, runL_append, hu2]
    exact hv2

theorem prf_one (R : HopRel) (d : Dfa) (a b : SState) :
    PRf R d a 1 b ↔ ∃ nb, PStep R d a nb b.2 ∧ nb.to = b.1 := by
  constructor
  · rintro ⟨w, hw, h1, h2⟩
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hw
    simp only [isWalk_cons, isWalk_nil, word_cons, word_nil, Dfa.runL] at h1 h2
    cases hs : d.stepL a.2 s.1 with
    | none => rw [hs] at h2; cases h2
    | some t =>
      rw [hs] at h2; simp at h2
      exact ⟨s.2, ⟨s.1, h1.1, h2 ▸ hs⟩, h1.2⟩
  · rintro ⟨nb, ⟨l, hR, hs⟩, hto⟩
    exact ⟨[(l, nb)], rfl, ⟨hR, hto⟩, by simp [Dfa.runL, hs]⟩

theorem prf_succ (R : HopRel) (d : Dfa) (a c : SState) (n : Nat) :
    PRf R d a (n + 1) c ↔ ∃ b nb, PRf R d a n b ∧ PStep R d b nb c.2 ∧ nb.to = c.1 := by
  rw [prf_add]
  simp only [prf_one]
  constructor
  · rintro ⟨b, h1, nb, h2, h3⟩; exact ⟨b, nb, h1, h2, h3⟩
  · rintro ⟨b, nb, h1, h2, h3⟩; exact ⟨b, h1, nb, h2, h3⟩

/-- The hop layer of a search lists exactly the hops of `R` from a node, each with the state the
automaton moves to on its letter (the refinement hypothesis between the engine's sorted range
scans and a declarative hop relation). -/
def HopsExact (st : ModelState) (c : Ctx) (R : HopRel) : Prop :=
  ∀ x q L, ev st (expandOne c x q) = .ok (.ok L) →
    ∀ (nb : Nb) (t : Nat), (nb, t) ∈ L ↔ PStep R c.dfa (x, q) nb t

/-- A walk matches `e` (whose automaton is `d`) exactly when the automaton runs on its word from
the start state to an accepting state. -/
theorem match_iff_run {e : PathExpr} {d : Dfa} (hd : buildDfa (toRE false e) = .ok d) (w : List Step) :
    word w ∈ lang e ↔ ∃ t, d.runL 0 (word w) = some t ∧ d.accepts t = true := by
  rw [dfa_lang e false d hd]; rfl

/-- The ends reachable from `x` by a matching walk of exactly `n` hops. -/
theorem matchWalk_iff {R : HopRel} {e : PathExpr} {d : Dfa} (hd : buildDfa (toRE false e) = .ok d)
    (x y : Int64) (n : Nat) :
    (∃ w, IsWalk R x w y ∧ word w ∈ lang e ∧ w.length = n) ↔
      ∃ t, d.accepts t = true ∧ PRf R d (x, 0) n (y, t) := by
  constructor
  · rintro ⟨w, h1, h2, h3⟩
    obtain ⟨t, ht, ha⟩ := (match_iff_run hd w).1 h2
    exact ⟨t, ha, w, h3, h1, ht⟩
  · rintro ⟨t, ha, w, h3, h1, ht⟩
    exact ⟨w, h1, (match_iff_run hd w).2 ⟨t, ht, ha⟩, h3⟩

end Tiramemsu.Path
