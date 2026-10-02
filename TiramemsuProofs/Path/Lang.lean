/-
The language of a regular expression over hop letters, and the laws the automaton
construction relies on: nullability, the smart constructors and normalization preserve the
language, and the derivative by a letter class is the left quotient by any letter of that class.
-/
import Tiramemsu.Path.Automaton
import Mathlib.Tactic

namespace Tiramemsu.Path

open Tiramemsu.IR

--# @lat: [[query#Paths#Automaton]]

/-- The words (hop-letter sequences) of a regular expression. -/
inductive RE.Lang : RE → List Letter → Prop
  | eps : RE.Lang .eps []
  | sym {c : Cls} {l : Letter} : c.matches l = true → RE.Lang (.sym c) [l]
  | seq {a b : RE} {u v : List Letter} : RE.Lang a u → RE.Lang b v → RE.Lang (.seq a b) (u ++ v)
  | altL {a b : RE} {w : List Letter} : RE.Lang a w → RE.Lang (.alt a b) w
  | altR {a b : RE} {w : List Letter} : RE.Lang b w → RE.Lang (.alt a b) w
  | starNil {a : RE} : RE.Lang (.star a) []
  | starCons {a : RE} {u v : List Letter} : RE.Lang a u → RE.Lang (.star a) v → RE.Lang (.star a) (u ++ v)

namespace RE

theorem lang_empty_iff (w : List Letter) : Lang .empty w ↔ False := ⟨fun h => (by cases h), False.elim⟩

theorem lang_eps_iff (w : List Letter) : Lang .eps w ↔ w = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .eps⟩

theorem lang_sym_iff (c : Cls) (w : List Letter) : Lang (.sym c) w ↔ ∃ l, w = [l] ∧ c.matches l = true :=
  ⟨fun h => by cases h with | sym h => exact ⟨_, rfl, h⟩, fun ⟨l, hw, h⟩ => hw ▸ .sym h⟩

theorem lang_seq_iff (a b : RE) (w : List Letter) :
    Lang (.seq a b) w ↔ ∃ u v, w = u ++ v ∧ Lang a u ∧ Lang b v :=
  ⟨fun h => by cases h with | seq ha hb => exact ⟨_, _, rfl, ha, hb⟩, fun ⟨_, _, hw, ha, hb⟩ => hw ▸ .seq ha hb⟩

theorem lang_alt_iff (a b : RE) (w : List Letter) : Lang (.alt a b) w ↔ Lang a w ∨ Lang b w :=
  ⟨fun h => by cases h with | altL h => exact .inl h | altR h => exact .inr h,
   fun h => h.elim .altL .altR⟩

/-- Star words: concatenations of words of the body. -/
theorem lang_star_iff (a : RE) (w : List Letter) :
    Lang (.star a) w ↔ ∃ ws : List (List Letter), (∀ u ∈ ws, Lang a u) ∧ w = ws.flatten := by
  constructor
  · intro h
    generalize hr : RE.star a = r at h
    induction h with
    | starNil => exact ⟨[], by simp, rfl⟩
    | @starCons a' u v hu _ _ ih =>
      cases hr
      obtain ⟨ws, hws, rfl⟩ := ih rfl
      exact ⟨u :: ws, by simpa [hu] using hws, by simp⟩
    | _ => cases hr
  · rintro ⟨ws, hws, rfl⟩
    induction ws with
    | nil => exact .starNil
    | cons u ws ih =>
      exact .starCons (hws u (List.mem_cons_self ..)) (ih fun x hx => hws x (List.mem_cons_of_mem _ hx))

theorem lang_star_append {a : RE} {u v : List Letter} (hu : Lang (.star a) u) (hv : Lang (.star a) v) :
    Lang (.star a) (u ++ v) := by
  rw [lang_star_iff] at *
  obtain ⟨ws, hws, rfl⟩ := hu
  obtain ⟨vs, hvs, rfl⟩ := hv
  exact ⟨ws ++ vs, by simp only [List.mem_append]; rintro x (hx | hx); exacts [hws x hx, hvs x hx], by simp⟩

/-- A non-empty star word starts with a non-empty body word. -/
theorem lang_star_cons {a : RE} {l : Letter} {w : List Letter} :
    Lang (.star a) (l :: w) ↔ ∃ u v, w = u ++ v ∧ Lang a (l :: u) ∧ Lang (.star a) v := by
  constructor
  · rw [lang_star_iff]
    rintro ⟨ws, hws, hw⟩
    induction ws with
    | nil => simp at hw
    | cons x ws ih =>
      cases x with
      | nil => exact ih (fun u hu => hws u (List.mem_cons_of_mem _ hu)) (by simpa using hw)
      | cons y x =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨x, ws.flatten, rfl, hws _ (List.mem_cons_self ..), ?_⟩
        rw [lang_star_iff]
        exact ⟨ws, fun u hu => hws u (List.mem_cons_of_mem _ hu), rfl⟩
  · rintro ⟨u, v, rfl, hu, hv⟩
    exact .starCons (u := l :: u) hu hv

/-! ## Nullability -/

theorem nullable_iff : ∀ r : RE, r.nullable = true ↔ Lang r []
  | .empty => by simp [nullable, lang_empty_iff]
  | .eps => by simp [nullable, lang_eps_iff]
  | .sym c => by simp [nullable, lang_sym_iff]
  | .seq a b => by
    rw [nullable, Bool.and_eq_true, nullable_iff a, nullable_iff b, lang_seq_iff]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨[], [], rfl, ha, hb⟩
    · rintro ⟨u, v, h, ha, hb⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
      exact ⟨ha, hb⟩
  | .alt a b => by rw [nullable, Bool.or_eq_true, nullable_iff a, nullable_iff b, lang_alt_iff]
  | .star a => by simp only [nullable, true_iff]; exact .starNil

/-! ## Smart constructors -/

/-- Two expressions with the same words. -/
def Equiv (a b : RE) : Prop := ∀ w, Lang a w ↔ Lang b w

theorem seq_assoc (a b c : RE) : Equiv (.seq (.seq a b) c) (.seq a (.seq b c)) := by
  intro w
  simp only [lang_seq_iff]
  constructor
  · rintro ⟨_, v, rfl, ⟨u1, u2, rfl, h1, h2⟩, h3⟩
    exact ⟨u1, u2 ++ v, by simp, h1, u2, v, rfl, h2, h3⟩
  · rintro ⟨u1, _, rfl, h1, u2, v, rfl, h2, h3⟩
    exact ⟨u1 ++ u2, v, by simp, ⟨u1, u2, rfl, h1, h2⟩, h3⟩

theorem mkSeq_equiv (a b : RE) : Equiv (mkSeq a b) (.seq a b) := by
  intro w
  unfold mkSeq
  split
  · simp [lang_seq_iff, lang_empty_iff]
  · simp [lang_seq_iff, lang_empty_iff]
  · simp [lang_seq_iff, lang_eps_iff]
  · simp [lang_seq_iff, lang_eps_iff]
  · exact (seq_assoc _ _ _ w).symm
  · exact Iff.rfl

theorem lang_alts (l : List RE) (w : List Letter) : Lang (RE.alts l) w ↔ ∃ x ∈ l, Lang x w := by
  match l with
  | [] => simp [alts, lang_empty_iff]
  | [a] => simp [alts]
  | a :: b :: rest =>
    have : RE.alts (a :: b :: rest) = .alt a (RE.alts (b :: rest)) := rfl
    rw [this, lang_alt_iff, lang_alts (b :: rest) w]
    simp

theorem lang_altsOf : ∀ (r : RE) (w : List Letter), Lang r w ↔ ∃ x ∈ r.altsOf, Lang x w
  | .alt a b, w => by
    rw [altsOf, lang_alt_iff, lang_altsOf a w, lang_altsOf b w]
    simp only [List.mem_append]
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      exacts [⟨x, .inl hx, h⟩, ⟨x, .inr hx, h⟩]
    · rintro ⟨x, hx | hx, h⟩
      exacts [.inl ⟨x, hx, h⟩, .inr ⟨x, hx, h⟩]
  | .empty, w => by simp [altsOf, lang_empty_iff]
  | .eps, w => by simp [altsOf]
  | .sym _, w => by simp [altsOf]
  | .seq _ _, w => by simp [altsOf]
  | .star _, w => by simp [altsOf]

theorem mkAlt_equiv (a b : RE) : Equiv (mkAlt a b) (.alt a b) := by
  intro w
  unfold mkAlt
  rw [lang_alts, lang_alt_iff, lang_altsOf a w, lang_altsOf b w]
  simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_append]
  constructor
  · rintro ⟨x, hx | hx, h⟩
    exacts [.inl ⟨x, hx, h⟩, .inr ⟨x, hx, h⟩]
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    exacts [⟨x, .inl hx, h⟩, ⟨x, .inr hx, h⟩]

theorem star_star (a : RE) : Equiv (.star (.star a)) (.star a) := by
  intro w
  constructor
  · intro h
    rw [lang_star_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    induction ws with
    | nil => exact .starNil
    | cons u ws ih =>
      rw [List.flatten_cons]
      exact lang_star_append (hws u (List.mem_cons_self ..)) (ih fun x hx => hws x (List.mem_cons_of_mem _ hx))
  · intro h
    have := Lang.starCons (a := .star a) h .starNil
    simp at this; exact this

theorem mkStar_equiv (a : RE) : Equiv (mkStar a) (.star a) := by
  intro w
  unfold mkStar
  split
  · rw [lang_eps_iff, lang_star_iff]
    constructor
    · rintro rfl; exact ⟨[], by simp, rfl⟩
    · rintro ⟨ws, hws, rfl⟩
      simp only [List.flatten_eq_nil_iff]
      intro u hu; have := hws u hu; simpa [lang_empty_iff] using this
  · rw [lang_eps_iff, lang_star_iff]
    constructor
    · rintro rfl; exact ⟨[], by simp, rfl⟩
    · rintro ⟨ws, hws, rfl⟩
      simp only [List.flatten_eq_nil_iff]
      intro u hu; exact (lang_eps_iff u).1 (hws u hu)
  · exact (star_star _ w).symm
  · exact Iff.rfl

theorem norm_equiv : ∀ r : RE, Equiv r.norm r
  | .seq a b => fun w => by
    rw [norm, mkSeq_equiv, lang_seq_iff, lang_seq_iff]
    simp only [norm_equiv a _, norm_equiv b _]
  | .alt a b => fun w => by
    rw [norm, mkAlt_equiv, lang_alt_iff, lang_alt_iff, norm_equiv a, norm_equiv b]
  | .star a => fun w => by
    rw [norm, mkStar_equiv, lang_star_iff, lang_star_iff]
    simp only [norm_equiv a _]
  | .empty => fun _ => Iff.rfl
  | .eps => fun _ => Iff.rfl
  | .sym _ => fun _ => Iff.rfl

/-! ## Symbols -/

theorem syms_alts (l : List RE) (s : Cls) (h : s ∈ (RE.alts l).syms) : ∃ x ∈ l, s ∈ x.syms := by
  match l with
  | [] => simp [alts, syms] at h
  | [a] => exact ⟨a, by simp, by simpa [alts] using h⟩
  | a :: b :: rest =>
    simp only [alts, syms, List.mem_append] at h
    rcases h with h | h
    · exact ⟨a, by simp, h⟩
    · obtain ⟨x, hx, hs⟩ := syms_alts (b :: rest) s h
      exact ⟨x, List.mem_cons_of_mem _ hx, hs⟩

theorem syms_altsOf : ∀ (r x : RE) (s : Cls), x ∈ r.altsOf → s ∈ x.syms → s ∈ r.syms
  | .alt a b, x, s, hx, hs => by
    simp only [altsOf, List.mem_append] at hx
    simp only [syms, List.mem_append]
    rcases hx with hx | hx
    exacts [.inl (syms_altsOf a x s hx hs), .inr (syms_altsOf b x s hx hs)]
  | .empty, x, s, hx, _ => by simp [altsOf] at hx
  | .eps, x, s, hx, hs => by simp [altsOf] at hx; subst hx; exact hs
  | .sym _, x, s, hx, hs => by simp [altsOf] at hx; subst hx; exact hs
  | .seq _ _, x, s, hx, hs => by simp [altsOf] at hx; subst hx; exact hs
  | .star _, x, s, hx, hs => by simp [altsOf] at hx; subst hx; exact hs

theorem syms_mkSeq (a b : RE) (s : Cls) (h : s ∈ (mkSeq a b).syms) : s ∈ a.syms ∨ s ∈ b.syms := by
  unfold mkSeq at h
  split at h <;> simp_all [syms]
  tauto

theorem syms_mkAlt (a b : RE) (s : Cls) (h : s ∈ (mkAlt a b).syms) : s ∈ a.syms ∨ s ∈ b.syms := by
  unfold mkAlt at h
  obtain ⟨x, hx, hs⟩ := syms_alts _ s h
  simp only [List.mem_mergeSort, List.mem_eraseDups, List.mem_append] at hx
  rcases hx with hx | hx
  exacts [.inl (syms_altsOf a x s hx hs), .inr (syms_altsOf b x s hx hs)]

theorem syms_mkStar (a : RE) (s : Cls) (h : s ∈ (mkStar a).syms) : s ∈ a.syms := by
  unfold mkStar at h
  split at h <;> simp_all [syms]

theorem syms_norm : ∀ (r : RE) (s : Cls), s ∈ r.norm.syms → s ∈ r.syms
  | .seq a b, s, h => by
    simp only [norm] at h; simp only [syms, List.mem_append]
    rcases syms_mkSeq _ _ s h with h | h
    exacts [.inl (syms_norm a s h), .inr (syms_norm b s h)]
  | .alt a b, s, h => by
    simp only [norm] at h; simp only [syms, List.mem_append]
    rcases syms_mkAlt _ _ s h with h | h
    exacts [.inl (syms_norm a s h), .inr (syms_norm b s h)]
  | .star a, s, h => by
    simp only [norm] at h; simp only [syms]
    exact syms_norm a s (syms_mkStar _ s h)
  | .empty, _, h => h
  | .eps, _, h => h
  | .sym _, _, h => h

theorem syms_deriv (c : LClass) : ∀ (r : RE) (s : Cls), s ∈ (r.deriv c).syms → s ∈ r.syms
  | .empty, s, h => by simp [deriv, syms] at h
  | .eps, s, h => by simp [deriv, syms] at h
  | .sym x, s, h => by simp only [deriv] at h; split at h <;> simp [syms] at h
  | .seq a b, s, h => by
    simp only [deriv] at h; simp only [syms, List.mem_append]
    have hseq : s ∈ (mkSeq (a.deriv c) b).syms → s ∈ a.syms ∨ s ∈ b.syms := fun h => by
      rcases syms_mkSeq _ _ s h with h | h
      exacts [.inl (syms_deriv c a s h), .inr h]
    split at h
    · rcases syms_mkAlt _ _ s h with h | h
      exacts [hseq h, .inr (syms_deriv c b s h)]
    · exact hseq h
  | .alt a b, s, h => by
    simp only [deriv] at h; simp only [syms, List.mem_append]
    rcases syms_mkAlt _ _ s h with h | h
    exacts [.inl (syms_deriv c a s h), .inr (syms_deriv c b s h)]
  | .star a, s, h => by
    simp only [deriv] at h; simp only [syms]
    rcases syms_mkSeq _ _ s h with h | h
    exacts [syms_deriv c a s h, syms_mkStar a s h]

/-- Every letter of a word is matched by a symbol of the expression. -/
theorem lang_letters {r : RE} {w : List Letter} (h : Lang r w) : ∀ l ∈ w, ∃ s ∈ r.syms, s.matches l = true := by
  induction h with
  | eps => simp
  | sym hm => intro l hl; simp at hl; subst hl; exact ⟨_, by simp [syms], hm⟩
  | seq _ _ iha ihb =>
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨s, hs, hm⟩ := iha l hl; exact ⟨s, by simp [syms, hs], hm⟩
    · obtain ⟨s, hs, hm⟩ := ihb l hl; exact ⟨s, by simp [syms, hs], hm⟩
  | altL _ ih => intro l hl; obtain ⟨s, hs, hm⟩ := ih l hl; exact ⟨s, by simp [syms, hs], hm⟩
  | altR _ ih => intro l hl; obtain ⟨s, hs, hm⟩ := ih l hl; exact ⟨s, by simp [syms, hs], hm⟩
  | starNil => simp
  | starCons _ _ iha ihb =>
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨s, hs, hm⟩ := iha l hl; exact ⟨s, by simpa [syms] using hs, hm⟩
    · exact ihb l hl

/-! ## Derivatives -/

/-- The derivative by a class is the left quotient by a letter of that class, when the class
and the letter agree on every symbol of the expression. -/
theorem deriv_lang (c : LClass) (l : Letter) :
    ∀ (r : RE), (∀ s ∈ r.syms, s.matchesClass c = s.matches l) →
      ∀ w, Lang (r.deriv c) w ↔ Lang r (l :: w)
  | .empty, _, w => by simp [deriv, lang_empty_iff]
  | .eps, _, w => by simp [deriv, lang_empty_iff, lang_eps_iff]
  | .sym s, hc, w => by
    have hs := hc s (by simp [syms])
    simp only [deriv, lang_sym_iff, List.cons.injEq]
    split
    · rename_i hm
      rw [lang_eps_iff]
      constructor
      · rintro rfl; exact ⟨l, ⟨rfl, rfl⟩, hs ▸ hm⟩
      · rintro ⟨_, ⟨rfl, rfl⟩, _⟩; rfl
    · rename_i hm
      rw [lang_empty_iff]
      constructor
      · exact False.elim
      · rintro ⟨_, ⟨rfl, rfl⟩, h⟩; exact hm (hs ▸ h)
  | .seq a b, hc, w => by
    have hca : ∀ s ∈ a.syms, s.matchesClass c = s.matches l := fun s hs => hc s (by simp [syms, hs])
    have hcb : ∀ s ∈ b.syms, s.matchesClass c = s.matches l := fun s hs => hc s (by simp [syms, hs])
    have hseq : Lang (mkSeq (a.deriv c) b) w ↔ ∃ u v, w = u ++ v ∧ Lang a (l :: u) ∧ Lang b v := by
      rw [mkSeq_equiv, lang_seq_iff]
      simp only [deriv_lang c l a hca]
    rw [lang_seq_iff]
    have hsplit : (∃ u v, l :: w = u ++ v ∧ Lang a u ∧ Lang b v) ↔
        (∃ u v, w = u ++ v ∧ Lang a (l :: u) ∧ Lang b v) ∨ (Lang a [] ∧ Lang b (l :: w)) := by
      constructor
      · rintro ⟨u, v, h, ha, hb⟩
        cases u with
        | nil => simp at h; subst h; exact .inr ⟨ha, hb⟩
        | cons x u =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inl ⟨u, v, rfl, ha, hb⟩
      · rintro (⟨u, v, rfl, ha, hb⟩ | ⟨ha, hb⟩)
        · exact ⟨l :: u, v, rfl, ha, hb⟩
        · exact ⟨[], l :: w, rfl, ha, hb⟩
    rw [hsplit]
    simp only [deriv]
    split
    · rename_i hn
      rw [mkAlt_equiv, lang_alt_iff, hseq, deriv_lang c l b hcb, ← nullable_iff]
      simp [hn]
    · rename_i hn
      rw [hseq, ← nullable_iff]
      simp [hn]
  | .alt a b, hc, w => by
    have hca : ∀ s ∈ a.syms, s.matchesClass c = s.matches l := fun s hs => hc s (by simp [syms, hs])
    have hcb : ∀ s ∈ b.syms, s.matchesClass c = s.matches l := fun s hs => hc s (by simp [syms, hs])
    simp only [deriv]
    rw [mkAlt_equiv, lang_alt_iff, lang_alt_iff, deriv_lang c l a hca, deriv_lang c l b hcb]
  | .star a, hc, w => by
    have hca : ∀ s ∈ a.syms, s.matchesClass c = s.matches l := fun s hs => hc s (by simpa [syms] using hs)
    simp only [deriv]
    rw [mkSeq_equiv, lang_seq_iff, lang_star_cons]
    simp only [deriv_lang c l a hca, mkStar_equiv _ _]

end RE

end Tiramemsu.Path
