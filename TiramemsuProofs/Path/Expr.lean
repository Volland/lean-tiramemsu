/-
The declarative language of a path expression (path-evaluation "Path expression language"):
the words of hop letters it matches, with `^e` matching the reversed, direction-flipped words of
`e`. The compiled expression (`toRE`, inverse pushed to the atoms, repetition unrolled) has
exactly these words, so the automaton accepts exactly the expression's language.
-/
import TiramemsuProofs.Path.Dfa

namespace Tiramemsu.Path

open Tiramemsu.IR

--# @lat: [[query#Paths#Automaton]]

def Letter.flip : Letter → Letter
  | .stored p rel d => .stored p rel d.flip
  | .virt k d => .virt k d.flip

theorem Dir.flip_flip (d : Dir) : d.flip.flip = d := by cases d <;> rfl

theorem Letter.flip_flip (l : Letter) : l.flip.flip = l := by
  cases l <;> simp [Letter.flip, Dir.flip_flip]

/-- A word read backwards: reversed, every hop direction flipped. -/
def flipRev (w : List Letter) : List Letter := w.reverse.map Letter.flip

theorem flipRev_flipRev (w : List Letter) : flipRev (flipRev w) = w := by
  simp [flipRev, List.map_reverse, Function.comp_def, Letter.flip_flip]

theorem flipRev_append (u v : List Letter) : flipRev (u ++ v) = flipRev v ++ flipRev u := by
  simp [flipRev]

theorem flipRev_flatten (ws : List (List Letter)) : flipRev ws.flatten = (ws.reverse.map flipRev).flatten := by
  induction ws with
  | nil => rfl
  | cons u ws ih => simp [flipRev_append, ih]

end Tiramemsu.Path

namespace Tiramemsu.IR

open Tiramemsu.Path

/-- The words of a path expression. -/
inductive PathExpr.Lang : PathExpr → List Letter → Prop
  | atom {iri : String} {l : Letter} : (atomCls iri .out).matches l = true → PathExpr.Lang (.atom iri) [l]
  | inv {e : PathExpr} {w : List Letter} : PathExpr.Lang e w → PathExpr.Lang (.inv e) (flipRev w)
  | seq {es : List PathExpr} {ws : List (List Letter)} : es.length = ws.length →
      (∀ p ∈ es.zip ws, PathExpr.Lang p.1 p.2) → PathExpr.Lang (.seq es) ws.flatten
  | alt {es : List PathExpr} {e : PathExpr} {w : List Letter} : e ∈ es → PathExpr.Lang e w → PathExpr.Lang (.alt es) w
  | star {e : PathExpr} {ws : List (List Letter)} : (∀ u ∈ ws, PathExpr.Lang e u) → PathExpr.Lang (.star e) ws.flatten
  | plus {e : PathExpr} {ws : List (List Letter)} : ws ≠ [] → (∀ u ∈ ws, PathExpr.Lang e u) →
      PathExpr.Lang (.plus e) ws.flatten
  | optNone {e : PathExpr} : PathExpr.Lang (.opt e) []
  | optSome {e : PathExpr} {w : List Letter} : PathExpr.Lang e w → PathExpr.Lang (.opt e) w
  | rep {e : PathExpr} {lo : Nat} {hi : Option Nat} {ws : List (List Letter)} : lo ≤ ws.length →
      (∀ h, hi = some h → ws.length ≤ max lo h) → (∀ u ∈ ws, PathExpr.Lang e u) →
      PathExpr.Lang (.rep e lo hi) ws.flatten

end Tiramemsu.IR

namespace Tiramemsu.Path

open Tiramemsu.IR

/-! ## Words made of pieces -/

/-- `w` is the concatenation of a number of pieces satisfying `n`, each a word of `P`. -/
def Pieces (P : List Letter → Prop) (n : Nat → Prop) (w : List Letter) : Prop :=
  ∃ ws : List (List Letter), n ws.length ∧ (∀ u ∈ ws, P u) ∧ w = ws.flatten

theorem Pieces.congr {P Q : List Letter → Prop} {n : Nat → Prop} (h : ∀ u, P u ↔ Q u) (w : List Letter) :
    Pieces P n w ↔ Pieces Q n w := by
  unfold Pieces; simp only [h]

theorem Pieces.flip (P : List Letter → Prop) (n : Nat → Prop) (w : List Letter) :
    Pieces P n (flipRev w) ↔ Pieces (fun u => P (flipRev u)) n w := by
  constructor
  · rintro ⟨ws, hn, hp, hw⟩
    refine ⟨(ws.map flipRev).reverse, by simpa using hn, ?_, ?_⟩
    · intro u hu
      simp only [List.mem_reverse, List.mem_map] at hu
      obtain ⟨x, hx, rfl⟩ := hu
      rw [flipRev_flipRev]; exact hp x hx
    · rw [← flipRev_flipRev w, hw, flipRev_flatten]
      simp [List.map_reverse]
  · rintro ⟨ws, hn, hp, rfl⟩
    refine ⟨ws.reverse.map flipRev, by simpa using hn, ?_, flipRev_flatten ws⟩
    intro u hu
    simp only [List.mem_map, List.mem_reverse] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact hp x hx

namespace RE

theorem lang_star_pieces (a : RE) (w : List Letter) : Lang (.star a) w ↔ Pieces a.Lang (fun _ => True) w := by
  rw [lang_star_iff]; unfold Pieces; simp

theorem lang_pow (a : RE) : ∀ (n : Nat) (w : List Letter), Lang (a.pow n) w ↔ Pieces a.Lang (· = n) w
  | 0, w => by
    simp only [pow, lang_eps_iff, Pieces]
    constructor
    · rintro rfl; exact ⟨[], rfl, by simp, rfl⟩
    · rintro ⟨ws, hn, _, rfl⟩; rw [List.length_eq_zero_iff] at hn; subst hn; rfl
  | n + 1, w => by
    simp only [pow, lang_seq_iff, lang_pow a n, Pieces]
    constructor
    · rintro ⟨u, _, rfl, hu, ws, hn, hp, rfl⟩
      exact ⟨u :: ws, by simp [hn], by simpa [hu] using hp, by simp⟩
    · rintro ⟨ws, hn, hp, rfl⟩
      match ws, hn with
      | u :: ws, hn =>
        exact ⟨u, ws.flatten, by simp, hp u (List.mem_cons_self ..), ws, by simpa using hn,
          fun x hx => hp x (List.mem_cons_of_mem _ hx), rfl⟩

theorem lang_upTo (a : RE) : ∀ (n : Nat) (w : List Letter), Lang (a.upTo n) w ↔ Pieces a.Lang (· ≤ n) w
  | 0, w => by
    simp only [upTo, lang_eps_iff, Pieces, Nat.le_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨[], rfl, by simp, rfl⟩
    · rintro ⟨ws, rfl, _, rfl⟩; rfl
  | n + 1, w => by
    simp only [upTo, lang_alt_iff, lang_eps_iff, lang_seq_iff, lang_upTo a n, Pieces]
    constructor
    · rintro (rfl | ⟨u, _, rfl, hu, ws, hn, hp, rfl⟩)
      · exact ⟨[], by simp, by simp, rfl⟩
      · exact ⟨u :: ws, by simp [hn], by simpa [hu] using hp, by simp⟩
    · rintro ⟨ws, hn, hp, rfl⟩
      match ws, hn with
      | [], _ => exact .inl rfl
      | u :: ws, hn =>
        exact .inr ⟨u, ws.flatten, by simp, hp u (List.mem_cons_self ..), ws, by simp at hn; omega,
          fun x hx => hp x (List.mem_cons_of_mem _ hx), rfl⟩

theorem lang_seqs : ∀ (rs : List RE) (w : List Letter),
    Lang (RE.seqs rs) w ↔ ∃ ws : List (List Letter), List.Forall₂ Lang rs ws ∧ w = ws.flatten
  | [], w => by
    simp only [seqs, lang_eps_iff, List.forall₂_nil_left_iff, exists_eq_left, List.flatten_nil]
  | [a], w => by
    simp only [seqs]
    constructor
    · intro h; exact ⟨[w], .cons h .nil, by simp⟩
    · rintro ⟨ws, h, rfl⟩
      match ws, h with
      | [u], .cons h .nil => simpa using h
  | a :: b :: rest, w => by
    have : RE.seqs (a :: b :: rest) = .seq a (RE.seqs (b :: rest)) := rfl
    rw [this, lang_seq_iff]
    simp only [lang_seqs (b :: rest)]
    constructor
    · rintro ⟨u, _, rfl, hu, ws, hws, rfl⟩
      exact ⟨u :: ws, List.Forall₂.cons hu hws, by simp⟩
    · rintro ⟨ws, hws, rfl⟩
      match ws, hws with
      | u :: ws, List.Forall₂.cons hu hws => exact ⟨u, ws.flatten, by simp, hu, ws, hws, rfl⟩

end RE

/-! ## Inversion of the declarative language -/

namespace PathExpr

theorem lang_inv_iff (e : PathExpr) (w : List Letter) : (PathExpr.inv e).Lang w ↔ e.Lang (flipRev w) := by
  constructor
  · intro h; cases h with | inv h => rw [flipRev_flipRev]; exact h
  · intro h; have := PathExpr.Lang.inv h; rwa [flipRev_flipRev] at this

theorem lang_seq_iff (es : List PathExpr) (w : List Letter) :
    (PathExpr.seq es).Lang w ↔ ∃ ws : List (List Letter), List.Forall₂ PathExpr.Lang es ws ∧ w = ws.flatten := by
  constructor
  · intro h
    cases h with
    | seq hl hz => exact ⟨_, List.forall₂_iff_zip.2 ⟨hl, fun hab => hz _ hab⟩, rfl⟩
  · rintro ⟨ws, h, rfl⟩
    obtain ⟨hl, hz⟩ := List.forall₂_iff_zip.1 h
    exact .seq hl fun p hp => hz hp

theorem lang_alt_iff (es : List PathExpr) (w : List Letter) : (PathExpr.alt es).Lang w ↔ ∃ e ∈ es, e.Lang w :=
  ⟨fun h => by cases h with | alt he h => exact ⟨_, he, h⟩, fun ⟨_, he, h⟩ => .alt he h⟩

theorem lang_star_iff (e : PathExpr) (w : List Letter) : (PathExpr.star e).Lang w ↔ Pieces e.Lang (fun _ => True) w :=
  ⟨fun h => by cases h with | star h => exact ⟨_, trivial, h, rfl⟩, fun ⟨_, _, h, hw⟩ => hw ▸ .star h⟩

theorem lang_plus_iff (e : PathExpr) (w : List Letter) : (PathExpr.plus e).Lang w ↔ Pieces e.Lang (· ≠ 0) w :=
  ⟨fun h => by cases h with | plus hn h => exact ⟨_, by simpa using hn, h, rfl⟩,
   fun ⟨_, hn, h, hw⟩ => hw ▸ .plus (by simpa using hn) h⟩

theorem lang_opt_iff (e : PathExpr) (w : List Letter) : (PathExpr.opt e).Lang w ↔ w = [] ∨ e.Lang w :=
  ⟨fun h => by cases h with | optNone => exact .inl rfl | optSome h => exact .inr h,
   fun h => h.elim (fun h => h ▸ .optNone) .optSome⟩

theorem lang_rep_iff (e : PathExpr) (lo : Nat) (hi : Option Nat) (w : List Letter) :
    (PathExpr.rep e lo hi).Lang w ↔ Pieces e.Lang (fun k => lo ≤ k ∧ ∀ h, hi = some h → k ≤ max lo h) w :=
  ⟨fun h => by cases h with | rep h1 h2 h => exact ⟨_, ⟨h1, h2⟩, h, rfl⟩,
   fun ⟨_, ⟨h1, h2⟩, h, hw⟩ => hw ▸ .rep h1 h2 h⟩

theorem lang_atom_iff (iri : String) (w : List Letter) :
    (PathExpr.atom iri).Lang w ↔ ∃ l, w = [l] ∧ (atomCls iri .out).matches l = true :=
  ⟨fun h => by cases h with | atom h => exact ⟨_, rfl, h⟩, fun ⟨_, hw, h⟩ => hw ▸ .atom h⟩

end PathExpr

/-! ## The compiled expression has the expression's words -/

theorem Pieces.congr_n {P : List Letter → Prop} {n n' : Nat → Prop} (h : ∀ k, n k ↔ n' k) (w : List Letter) :
    Pieces P n w ↔ Pieces P n' w := by
  unfold Pieces; simp only [h]

theorem pieces_append_iff (P : List Letter → Prop) (m : Nat) (n : Nat → Prop) (w : List Letter) :
    (∃ u v, w = u ++ v ∧ Pieces P (· = m) u ∧ Pieces P n v) ↔ Pieces P (fun k => m ≤ k ∧ n (k - m)) w := by
  constructor
  · rintro ⟨_, _, rfl, ⟨ws1, rfl, h1, rfl⟩, ⟨ws2, hn, h2, rfl⟩⟩
    refine ⟨ws1 ++ ws2, ⟨by simp, by simpa using hn⟩, ?_, by simp⟩
    intro u hu
    rcases List.mem_append.1 hu with hu | hu
    exacts [h1 u hu, h2 u hu]
  · rintro ⟨ws, ⟨hm, hn⟩, hp, rfl⟩
    refine ⟨(ws.take m).flatten, (ws.drop m).flatten, by rw [← List.flatten_append, List.take_append_drop],
      ⟨ws.take m, by simp; omega, fun u hu => hp u (List.mem_of_mem_take hu), rfl⟩,
      ⟨ws.drop m, by simpa using hn, fun u hu => hp u (List.mem_of_mem_drop hu), rfl⟩⟩

theorem RE.lang_plus_pieces (a : RE) (w : List Letter) :
    RE.Lang (.seq a (.star a)) w ↔ Pieces a.Lang (· ≠ 0) w := by
  rw [RE.lang_seq_iff]
  simp only [RE.lang_star_pieces]
  constructor
  · rintro ⟨u, _, rfl, hu, ws, _, hp, rfl⟩
    exact ⟨u :: ws, by simp, by simpa [hu] using hp, by simp⟩
  · rintro ⟨ws, hn, hp, rfl⟩
    match ws, hn with
    | u :: ws, _ =>
      exact ⟨u, ws.flatten, by simp, hp u (List.mem_cons_self ..), ws, trivial,
        fun x hx => hp x (List.mem_cons_of_mem _ hx), rfl⟩

theorem atomCls_flip (iri : String) (d : Dir) (l : Letter) :
    (atomCls iri d.flip).matches l = (atomCls iri d).matches l.flip := by
  unfold atomCls
  cases l <;> cases d <;> split_ifs <;> simp [Cls.matches, Letter.flip, Dir.flip] <;> aesop

theorem forall₂_congr_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y, R x y ↔ S x y) → ∀ {m : List β}, List.Forall₂ R l m ↔ List.Forall₂ S l m
  | [], _, m => by cases m <;> simp
  | x :: l, h, m => by
    cases m with
    | nil => simp
    | cons y m =>
      simp only [List.forall₂_cons]
      rw [h x (List.mem_cons_self ..) y, forall₂_congr_mem (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem seq_flip (P : PathExpr → List Letter → Prop) (es : List PathExpr) (w : List Letter) :
    (∃ ws : List (List Letter), List.Forall₂ (fun e u => P e (flipRev u)) es.reverse ws ∧ w = ws.flatten) ↔
      (∃ vs : List (List Letter), List.Forall₂ P es vs ∧ flipRev w = vs.flatten) := by
  constructor
  · rintro ⟨ws, h, rfl⟩
    refine ⟨ws.reverse.map flipRev, ?_, flipRev_flatten ws⟩
    rw [← List.forall₂_reverse_iff, List.reverse_reverse] at h
    rw [List.forall₂_map_right_iff]
    exact h
  · rintro ⟨vs, h, hw⟩
    refine ⟨(vs.map flipRev).reverse, ?_, ?_⟩
    · rw [← List.forall₂_reverse_iff, List.reverse_reverse, List.reverse_reverse, List.forall₂_map_right_iff]
      simp only [flipRev_flipRev]; exact h
    · rw [← flipRev_flipRev w, hw, flipRev_flatten]
      simp [List.map_reverse, Function.comp_def, flipRev_flipRev]

theorem flipRev_eq_nil (w : List Letter) : flipRev w = [] ↔ w = [] := by simp [flipRev]

/-- The compiled expression (`inv`: read backwards) has exactly the expression's words. -/
theorem toRE_lang (e : PathExpr) (inv : Bool) (w : List Letter) :
    (toRE inv e).Lang w ↔ e.Lang (if inv then flipRev w else w) := by
  match e with
  | .atom iri =>
    rw [PathExpr.lang_atom_iff]
    simp only [toRE, RE.lang_sym_iff]
    cases inv
    · simp
    · simp only [if_true, ite_true]
      constructor
      · rintro ⟨l, rfl, h⟩
        refine ⟨l.flip, by simp [flipRev], ?_⟩
        rw [← atomCls_flip]; exact h
      · rintro ⟨l, hl, h⟩
        refine ⟨l.flip, ?_, ?_⟩
        · rw [← flipRev_flipRev w, hl]; simp [flipRev]
        · have := atomCls_flip iri .out l.flip
          rw [Letter.flip_flip] at this
          show (atomCls iri Dir.out.flip).matches l.flip = true
          rw [this]; exact h
  | .inv e =>
    simp only [toRE]
    rw [toRE_lang e (!inv) w, PathExpr.lang_inv_iff]
    cases inv <;> simp [flipRev_flipRev]
  | .seq es =>
    have ih : ∀ x ∈ es, ∀ u, (toRE inv x).Lang u ↔ x.Lang (if inv then flipRev u else u) :=
      fun x hx u => toRE_lang x inv u
    simp only [toRE, List.map_attach_eq_pmap, List.pmap_eq_map]
    rw [RE.lang_seqs, PathExpr.lang_seq_iff]
    cases inv
    · simp only [Bool.false_eq_true, if_false, ite_false] at ih ⊢
      simp only [List.forall₂_map_left_iff]
      simp only [forall₂_congr_mem ih]
    · simp only [if_true, ite_true] at ih ⊢
      rw [← List.map_reverse]
      simp only [List.forall₂_map_left_iff]
      rw [← seq_flip PathExpr.Lang es w]
      simp only [forall₂_congr_mem (l := es.reverse) (fun x hx => ih x (List.mem_reverse.1 hx))]
  | .alt es =>
    have ih : ∀ x ∈ es, ∀ u, (toRE inv x).Lang u ↔ x.Lang (if inv then flipRev u else u) :=
      fun x hx u => toRE_lang x inv u
    simp only [toRE, List.map_attach_eq_pmap, List.pmap_eq_map]
    rw [RE.lang_alts, PathExpr.lang_alt_iff]
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩; exact ⟨x, hx, (ih x hx w).1 h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨_, ⟨x, hx, rfl⟩, (ih x hx w).2 h⟩
  | .star e =>
    simp only [toRE]
    rw [RE.lang_star_pieces, PathExpr.lang_star_iff, Pieces.congr (fun u => toRE_lang e inv u)]
    cases inv
    · simp
    · simp only [if_true, ite_true]; rw [Pieces.flip]
  | .plus e =>
    simp only [toRE]
    rw [RE.lang_plus_pieces, PathExpr.lang_plus_iff, Pieces.congr (fun u => toRE_lang e inv u)]
    cases inv
    · simp
    · simp only [if_true, ite_true]; rw [Pieces.flip]
  | .opt e =>
    simp only [toRE]
    rw [RE.lang_alt_iff, RE.lang_eps_iff, PathExpr.lang_opt_iff, toRE_lang e inv w]
    cases inv
    · simp
    · simp [flipRev_eq_nil]
  | .rep e lo hi =>
    unfold toRE
    rw [RE.lang_seq_iff, PathExpr.lang_rep_iff]
    have hpow : ∀ u, (RE.pow (toRE inv e) lo).Lang u ↔ Pieces (toRE inv e).Lang (· = lo) u :=
      RE.lang_pow _ lo
    have htail : ∀ v, (match hi with
        | none => RE.star (toRE inv e)
        | some h => (toRE inv e).upTo (h - lo)).Lang v ↔
        Pieces (toRE inv e).Lang (fun k => ∀ h, hi = some h → k ≤ h - lo) v := by
      intro v
      cases hi with
      | none => rw [RE.lang_star_pieces]; exact Pieces.congr_n (by simp) v
      | some h => rw [RE.lang_upTo]; exact Pieces.congr_n (by simp) v
    simp only [hpow]
    refine (exists_congr fun u => exists_congr fun v => and_congr_right fun _ => and_congr_right fun _ =>
      htail v).trans ?_
    rw [pieces_append_iff, Pieces.congr (fun u => toRE_lang e inv u)]
    have hn : ∀ k, (lo ≤ k ∧ ∀ h, hi = some h → k - lo ≤ h - lo) ↔ (lo ≤ k ∧ ∀ h, hi = some h → k ≤ max lo h) := by
      intro k
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h hh => by have := h2 h hh; omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h hh => by have := h2 h hh; omega⟩
    rw [Pieces.congr_n hn]
    cases inv
    · simp
    · simp only [if_true, ite_true]; rw [Pieces.flip]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega)

/-- `^e` matches exactly the reversed, direction-flipped words of `e`. -/
theorem lang_inverse (e : PathExpr) (w : List Letter) : (PathExpr.inv e).Lang w ↔ e.Lang (flipRev w) :=
  PathExpr.lang_inv_iff e w

/-- path-evaluation "Automaton compilation": the automaton compiled from a path expression accepts
exactly the expression's words, and its run on a word is unique (`runL_unique`). -/
theorem dfa_lang (e : PathExpr) (inv : Bool) (d : Dfa) (h : buildDfa (toRE inv e) = .ok d) (w : List Letter) :
    (∃ q, d.runL 0 w = some q ∧ d.accepts q = true) ↔ e.Lang (if inv then flipRev w else w) := by
  rw [buildDfa_lang _ d h w, toRE_lang]

end Tiramemsu.Path
