/-
path-evaluation "Time-respecting evaluation": the hop rule is monotone in the time (a later time
allows no more hops and arrives no earlier); on a model state, whenever the hop layer lists
exactly the hops of `R`, a successful time-respecting REACH search reports each end of a
time-respecting matching walk within the bound once, with the length of a shortest such walk and
the earliest arrival over all of them; its loop's fuel suffices; and a later start instant reaches
no more ends and arrives no earlier.

The search is label-correcting by layers: the label of a search state is the earliest arrival
found so far; every improved label is expanded in the next layer, so after `depth` layers every
walk of at most `depth` hops is dominated by a label.
-/
import TiramemsuProofs.Path.Graph

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## Times and the hop rule -/

/-- The order of times (`none` is −∞). -/
def tle : Option Int → Option Int → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a ≤ b

theorem tle_refl : ∀ a : Option Int, tle a a
  | none => trivial
  | some a => le_refl a

theorem tle_trans : ∀ {a b c : Option Int}, tle a b → tle b c → tle a c
  | none, _, _, _, _ => trivial
  | some _, none, _, h, _ => h.elim
  | some _, some _, none, _, h => h.elim
  | some _, some _, some _, h1, h2 => le_trans h1 h2

theorem tle_total : ∀ a b : Option Int, tle a b ∨ tle b a
  | none, _ => .inl trivial
  | some _, none => .inr trivial
  | some a, some b => le_total a b

theorem better_iff : ∀ a b : Option Int, better a b = true ↔ ¬ tle b a
  | none, none => by simp [better, tle]
  | none, some _ => by simp [better, tle]
  | some _, none => by simp [better, tle]
  | some a, some b => by simp [better, tle]

theorem tmin_tle_left : ∀ a b : Option Int, tle (tmin a b) a
  | a, b => by
    unfold tmin
    split
    · rename_i h; rw [better_iff] at h; exact (tle_total a b).resolve_left h
    · exact tle_refl a

theorem tmin_tle_right : ∀ a b : Option Int, tle (tmin a b) b
  | a, b => by
    unfold tmin
    split
    · exact tle_refl b
    · rename_i h; rw [better_iff] at h; push Not at h; exact h

theorem tmin_cases (a b : Option Int) : tmin a b = a ∨ tmin a b = b := by
  unfold tmin; split <;> simp

/-- The hop rule is monotone: at an earlier time a hop allowed later is allowed, and arrives no
later. -/
theorem stepTime_mono (nb : Nb) {τ τ' : Option Int} (h : tle τ τ') {a' : Option Int}
    (h' : stepTime nb τ' = some a') : ∃ a, stepTime nb τ = some a ∧ tle a a' := by
  unfold stepTime at h' ⊢
  by_cases hk : (nb.hop.kind != 0) = true
  · rw [if_pos hk] at h' ⊢; cases h'; exact ⟨τ, rfl, h⟩
  · rw [if_neg hk] at h' ⊢
    rcases hvt : nb.vTo with _ | vt <;> rcases hvf : nb.vFrom with _ | vf <;>
      rcases τ with _ | t <;> rcases τ' with _ | t' <;>
      simp only [hvt, hvf, tle, Option.map_none, Option.getD_none, Option.map_some, Option.getD_some] at h h' ⊢
    all_goals (try split_ifs at h' ⊢) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h') <;> (try subst h')
    all_goals first
      | omega
      | exact h'.elim
      | exact ⟨_, rfl, trivial⟩
      | (refine ⟨_, rfl, ?_⟩; simp only [tle]; omega)
      | (refine ⟨_, rfl, ?_⟩; simp only [tle, max_def]; split_ifs <;> omega)


/-- The time after the hops of a walk under the hop rule (`none`: some hop is not allowed). -/
def timeWalk : List Step → Option Int → Option (Option Int)
  | [], τ => some τ
  | s :: w, τ => (stepTime s.2 τ).bind (timeWalk w)

theorem timeWalk_append : ∀ (u v : List Step) (τ : Option Int),
    timeWalk (u ++ v) τ = (timeWalk u τ).bind (timeWalk v)
  | [], v, τ => rfl
  | s :: u, v, τ => by
    simp only [List.cons_append, timeWalk]
    cases stepTime s.2 τ with
    | none => rfl
    | some τ' => exact timeWalk_append u v τ'

/-- A walk allowed from a later time is allowed from an earlier one and arrives no later. -/
theorem timeWalk_mono : ∀ (w : List Step) {τ τ' : Option Int}, tle τ τ' → ∀ {a' : Option Int},
    timeWalk w τ' = some a' → ∃ a, timeWalk w τ = some a ∧ tle a a'
  | [], τ, τ', h, a', h' => by cases h'; exact ⟨τ, rfl, h⟩
  | s :: w, τ, τ', h, a', h' => by
    simp only [timeWalk] at h' ⊢
    cases hs : stepTime s.2 τ' with
    | none => rw [hs] at h'; cases h'
    | some b' =>
      rw [hs] at h'
      obtain ⟨b, hb, hbb⟩ := stepTime_mono s.2 h hs
      rw [hb]
      exact timeWalk_mono w hbb h'

/-- The timed hop rule of a time-respecting search is the plain one. -/
theorem walkTau_timed {c : Ctx} {t : Option Int} (hc : c.timed = some t) :
    ∀ (w : List Step) (τ : Option Int), walkTau c w τ = timeWalk w τ
  | [], τ => rfl
  | s :: w, τ => by
    simp only [walkTau, timeWalk, Ctx.tstep, hc]
    cases stepTime s.2 τ with
    | none => rfl
    | some τ' => exact walkTau_timed hc w τ'

/-- `TW R d x τ0 n p a`: a walk of `n` hops from `x` to `p.1` on which the automaton runs to
`p.2` and the hop rule from `τ0` arrives at `a`. -/
def TW (R : HopRel) (d : Dfa) (x : Int64) (τ0 : Option Int) (n : Nat) (p : SState) (a : Option Int) : Prop :=
  ∃ w : List Step, w.length = n ∧ IsWalk R x w p.1 ∧ d.runL 0 (word w) = some p.2 ∧ timeWalk w τ0 = some a

theorem tw_zero (R : HopRel) (d : Dfa) (x : Int64) (τ0 : Option Int) (p : SState) (a : Option Int) :
    TW R d x τ0 0 p a ↔ p = (x, 0) ∧ a = τ0 := by
  constructor
  · rintro ⟨w, hw, h1, h2, h3⟩
    rw [List.length_eq_zero_iff] at hw; subst hw
    simp only [isWalk_nil, word_nil, Dfa.runL, Option.some.injEq, timeWalk] at h1 h2 h3
    exact ⟨Prod.ext h1.symm h2.symm, h3.symm⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨[], rfl, rfl, rfl, rfl⟩

theorem tw_succ (R : HopRel) (d : Dfa) (x : Int64) (τ0 : Option Int) (n : Nat) (p' : SState) (a' : Option Int) :
    TW R d x τ0 (n + 1) p' a' ↔ ∃ p a nb, TW R d x τ0 n p a ∧ PStep R d p nb p'.2 ∧ nb.to = p'.1 ∧
      stepTime nb a = some a' := by
  constructor
  · rintro ⟨w, hw, h1, h2, h3⟩
    have hne : w ≠ [] := by rintro rfl; simp at hw
    obtain ⟨u, s, rfl⟩ : ∃ u s, w = u ++ [s] := ⟨w.dropLast, w.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨y, hu, hR, hto⟩ := (isWalk_snoc ..).1 h1
    rw [word_append, runL_append] at h2
    rw [timeWalk_append] at h3
    cases hq : d.runL 0 (word u) with
    | none => rw [hq] at h2; cases h2
    | some q =>
      cases ht : timeWalk u τ0 with
      | none => rw [ht] at h3; cases h3
      | some a =>
        rw [hq] at h2; rw [ht] at h3
        simp only [Option.bind_some, word_cons, word_nil, Dfa.runL, timeWalk] at h2 h3
        refine ⟨(y, q), a, s.2, ⟨u, by simp at hw; omega, hu, hq, ht⟩, ⟨s.1, hR, ?_⟩, hto, ?_⟩
        · cases hs : d.stepL q s.1 with
          | none => rw [hs] at h2; cases h2
          | some q' => rw [hs] at h2; simpa using h2
        · cases hs : stepTime s.2 a with
          | none => rw [hs] at h3; cases h3
          | some a'' => rw [hs] at h3; simpa using h3
  · rintro ⟨p, a, nb, ⟨u, hu, h1, h2, h3⟩, ⟨l, hR, hs⟩, hto, ht⟩
    refine ⟨u ++ [(l, nb)], by simp [hu], (isWalk_snoc ..).2 ⟨p.1, h1, hR, hto⟩, ?_, ?_⟩
    · rw [word_append, runL_append, h2]; simp only [Option.bind_some, word_cons, word_nil, Dfa.runL, hs]
    · rw [timeWalk_append, h3]; simp only [Option.bind_some, timeWalk, ht]

/-! ## The next layer and the arrivals -/

/-- The search state of a layer entry. -/
def ekey (e : Int64 × Nat × Option Int) : SState := (e.1, e.2.1)

theorem upsertNext_spec (next : List (Int64 × Nat × Option Int)) (n : Int64) (t : Nat) (a : Option Int)
    (hnd : (next.map ekey).Nodup) :
    ((upsertNext next n t a).map ekey).Nodup ∧ next.length ≤ (upsertNext next n t a).length ∧
      ∀ e, e ∈ upsertNext next n t a ↔ e = (n, t, a) ∨ (e ∈ next ∧ ekey e ≠ (n, t)) := by
  have hkey : ∀ e : Int64 × Nat × Option Int, (e.1 == n && e.2.1 == t) = true ↔ ekey e = (n, t) := by
    intro e; simp [ekey, Prod.ext_iff]
  unfold upsertNext
  split
  · rename_i i hi
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    have hki : ekey next[i] = (n, t) := (hkey _).1 hp
    have hmap : (next.set i (n, t, a)).map ekey = next.map ekey := by
      rw [List.map_set]
      have : ekey (n, t, a) = (next.map ekey)[i]'(by simpa using hlt) := by rw [List.getElem_map, hki]; rfl
      rw [this, List.set_getElem_self]
    refine ⟨hmap ▸ hnd, by simp, fun e => ?_⟩
    constructor
    · intro he
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
      rw [List.getElem_set]
      split
      · exact .inl rfl
      · rename_i hij
        refine .inr ⟨List.getElem_mem _, fun hk => hij ?_⟩
        have hj' : j < next.length := by simpa using hj
        have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simpa using hlt)
          (hj := by simpa using hj')).1 (by simp [hki, hk])
        exact this
    · rintro (rfl | ⟨he, hk⟩)
      · exact List.mem_set hlt _
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
        have hij : i ≠ j := by rintro rfl; exact hk hki
        refine List.mem_iff_getElem.2 ⟨j, by simpa using hj, ?_⟩
        rw [List.getElem_set, if_neg hij]
  · rename_i hi
    have hnone := List.findIdx?_eq_none_iff.1 hi
    have hnot : ∀ e ∈ next, ekey e ≠ (n, t) := fun e he hk => by
      have := hnone e he; rw [(hkey e).2 hk] at this; cases this
    refine ⟨?_, by simp, fun e => ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, fun k hk k' hk' hkk => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk'
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      exact hnot e he (hkk.trans hk')
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h); exact .inr ⟨h, hnot e h⟩; exact .inl h
      · rintro (h | ⟨h, -⟩); exact .inr h; exact .inl h

theorem recordEnd_get (ends : Std.HashMap Int64 (Nat × Option Int)) (n : Int64) (depth : Nat) (at_ : Option Int)
    (y : Int64) :
    (recordEnd ends n depth at_)[y]? =
      if n = y then (match ends[n]? with | some (h, a) => some (h, tmin a at_) | none => some (depth + 1, at_))
      else ends[y]? := by
  unfold recordEnd
  rw [Std.HashMap.get?_eq_getElem?]
  split
  · rename_i h a heq
    rw [Std.HashMap.getElem?_insert, heq]
    by_cases hy : n = y <;> simp [hy]
  · rename_i heq
    rw [Std.HashMap.getElem?_insert, heq]
    by_cases hy : n = y <;> simp [hy]

/-! ## The time-respecting REACH layer -/

section TimedLayer

variable (R : HopRel) (c : Ctx) (x : Int64) (τ0 : Option Int)

/-- An end reached by a time-respecting matching walk of exactly `n` hops. -/
def AccT (n : Nat) (y : Int64) : Prop := ∃ q a, c.dfa.accepts q = true ∧ TW R c.dfa x τ0 n (y, q) a

/-- A label whose successors are all dominated. -/
def Expd (best : Std.HashMap SState (Option Int)) (p : SState) (b : Option Int) : Prop :=
  ∀ nb t a', PStep R c.dfa p nb t → stepTime nb b = some a' → ∃ b', best[(nb.to, t)]? = some b' ∧ tle b' a'

/-- The fold state of one time-respecting REACH layer at depth `d` after processing `done`. -/
structure TLayer (d : Nat) (best0 : Std.HashMap SState (Option Int)) (ends0 : Std.HashMap Int64 (Nat × Option Int))
    (used0 : Nat) (done : List ((Nb × Nat) × Option Int))
    (acc : List (Int64 × Nat × Option Int) × Std.HashMap SState (Option Int) ×
      Std.HashMap Int64 (Nat × Option Int) × Nat) : Prop where
  dec : ∀ (p : SState) (b : Option Int), best0[p]? = some b → ∃ b', acc.2.1[p]? = some b' ∧ tle b' b
  sound : ∀ (p : SState) (b' : Option Int), acc.2.1[p]? = some b' →
    best0[p]? = some b' ∨ TW R c.dfa x τ0 (d + 1) p b'
  next : ∀ e ∈ acc.1, acc.2.1[(e.1, e.2.1)]? = some e.2.2 ∧ TW R c.dfa x τ0 (d + 1) (e.1, e.2.1) e.2.2
  nextKeys : (acc.1.map fun e => (e.1, e.2.1)).Nodup
  changed : ∀ (p : SState) (b' : Option Int), acc.2.1[p]? = some b' → best0[p]? ≠ some b' → (p.1, p.2, b') ∈ acc.1
  dom : ∀ a ∈ done, ∀ a', stepTime a.1.1 a.2 = some a' →
    ∃ b', acc.2.1[(a.1.1.to, a.1.2)]? = some b' ∧ tle b' a'
  endsKeys : ∀ y : Int64, ends0[y]? ≠ none → acc.2.2.1[y]? ≠ none
  endsSound : ∀ (y : Int64) (h : Nat) (a : Option Int), acc.2.2.1[y]? = some (h, a) → h ≤ d + 1 ∧ AccT R c x τ0 h y ∧
    (∀ n < h, ¬ AccT R c x τ0 n y) ∧ ∃ n ≤ d + 1, ∃ q, c.dfa.accepts q = true ∧ TW R c.dfa x τ0 n (y, q) a
  endsDom : ∀ (y : Int64) (q : Nat) (b : Option Int), c.dfa.accepts q = true → acc.2.1[(y, q)]? = some b →
    ∃ h a, acc.2.2.1[y]? = some (h, a) ∧ tle a b
  used : acc.2.2.2 ≤ c.limit ∧ used0 + acc.1.length ≤ acc.2.2.2

end TimedLayer

theorem upsertNext_length_le (next : List (Int64 × Nat × Option Int)) (n : Int64) (t : Nat) (a : Option Int) :
    (upsertNext next n t a).length ≤ next.length + 1 := by
  unfold upsertNext; split <;> simp

theorem tle_of_better {a b : Option Int} (h : better a b = true) : tle a b :=
  ((tle_total b a).resolve_left ((better_iff a b).1 h))

/-- One transition of a time-respecting REACH layer preserves the layer invariant. -/
theorem reachTimedStep_layer {st : ModelState} {R : HopRel} {c : Ctx} {x : Int64} {τ0 : Option Int} {d : Nat}
    {best0 : Std.HashMap SState (Option Int)} {ends0 : Std.HashMap Int64 (Nat × Option Int)} {used0 : Nat}
    (hB2 : ∀ n ≤ d, ∀ p a, TW R c.dfa x τ0 n p a → ∃ b, best0[p]? = some b ∧ tle b a)
    (hE2 : ∀ (y : Int64) (q : Nat) (b : Option Int), c.dfa.accepts q = true → best0[(y, q)]? = some b →
      ∃ h a, ends0[y]? = some (h, a) ∧ tle a b)
    {done : List ((Nb × Nat) × Option Int)}
    {acc acc' : List (Int64 × Nat × Option Int) × Std.HashMap SState (Option Int) ×
      Std.HashMap Int64 (Nat × Option Int) × Nat} {a : (Nb × Nat) × Option Int}
    (horig : ∃ src, TW R c.dfa x τ0 d src a.2 ∧ PStep R c.dfa src a.1.1 a.1.2)
    (hI : TLayer R c x τ0 d best0 ends0 used0 done acc)
    (h : ev st (reachTimedStep c d acc a) = .ok (.ok acc')) :
    TLayer R c x τ0 d best0 ends0 used0 (done ++ [a]) acc' := by
  obtain ⟨next, best, ends, used⟩ := acc
  obtain ⟨⟨nb, t⟩, tau⟩ := a
  obtain ⟨hdec, hsound, hnext, hkeys, hchg, hdom, heK, heS, heD, hused⟩ := hI
  simp only at hdec hsound hnext hkeys hchg hdom heK heS heD hused horig
  unfold reachTimedStep at h
  simp only at h
  have hmem_done : ∀ a ∈ done ++ [((nb, t), tau)], a ∈ done ∨ a = ((nb, t), tau) := by
    intro a ha; simpa using ha
  cases hs : stepTime nb tau with
  | none =>
    rw [hs] at h; simp only at h
    cases ev_pure_inj h
    refine ⟨hdec, hsound, hnext, hkeys, hchg, fun a ha a' ha' => ?_, heK, heS, heD, hused⟩
    rcases hmem_done a ha with ha | rfl
    · exact hdom a ha a' ha'
    · simp only [hs] at ha'; cases ha'
  | some at_ =>
    rw [hs] at h; simp only at h
    split at h
    · rename_i hc
      cases ev_pure_inj h
      refine ⟨hdec, hsound, hnext, hkeys, hchg, fun a ha a' ha' => ?_, heK, heS, heD, hused⟩
      rcases hmem_done a ha with ha | rfl
      · exact hdom a ha a' ha'
      · simp only [hs, Option.some.injEq] at ha'; subst ha'
        rw [Std.HashMap.get?_eq_getElem?] at hc
        cases hb : best[(nb.to, t)]? with
        | none => rw [hb] at hc; cases hc
        | some b =>
          rw [hb] at hc
          simp only [Option.any_some, Bool.not_eq_true'] at hc
          refine ⟨b, rfl, ?_⟩
          have := (better_iff at_ b).not.1 (by simp [hc])
          push Not at this; exact this
    · rename_i hc
      obtain ⟨u, hu, h⟩ := ev_bind_ok h
      obtain ⟨rfl, hul⟩ := charge_ok hu
      cases ev_pure_inj h
      rw [Std.HashMap.get?_eq_getElem?] at hc
      have himp : ∀ b, best[(nb.to, t)]? = some b → tle at_ b := by
        intro b hb; rw [hb] at hc
        simp only [Option.any_some, Bool.not_eq_true', Bool.not_eq_false] at hc
        exact tle_of_better (by simpa using hc)
      obtain ⟨src, hsrc, hstep⟩ := horig
      have htw : TW R c.dfa x τ0 (d + 1) (nb.to, t) at_ :=
        (tw_succ R c.dfa x τ0 d (nb.to, t) at_).2 ⟨src, tau, nb, hsrc, hstep, rfl, hs⟩
      have hins : ∀ q : SState, (best.insert (nb.to, t) at_)[q]? = if (nb.to, t) = q then some at_ else best[q]? := by
        intro q; rw [Std.HashMap.getElem?_insert]; simp only [beq_iff_eq]
      obtain ⟨hukeys, -, hupm⟩ := upsertNext_spec next nb.to t at_ hkeys
      refine ⟨fun q b hb => ?_, fun q b' hb' => ?_, fun e he => ?_, hukeys, fun q b' hb' hne => ?_,
        fun a ha a' ha' => ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨b', hb', hle⟩ := hdec q b hb
        by_cases hq : (nb.to, t) = q
        · subst hq
          exact ⟨at_, by rw [hins, if_pos rfl], tle_trans (himp b' hb') hle⟩
        · exact ⟨b', by rw [hins, if_neg hq]; exact hb', hle⟩
      · rw [hins] at hb'
        split at hb'
        · rename_i hq; subst hq; cases hb'; exact .inr htw
        · exact hsound q b' hb'
      · rcases (hupm e).1 he with rfl | ⟨he, hk⟩
        · exact ⟨by rw [hins, if_pos rfl], htw⟩
        · obtain ⟨h1, h2⟩ := hnext e he
          refine ⟨?_, h2⟩
          rw [hins, if_neg (fun h' => hk h'.symm)]; exact h1
      · rw [hins] at hb'
        split at hb'
        · rename_i hq; subst hq; cases hb'; exact (hupm _).2 (.inl rfl)
        · rename_i hq
          exact (hupm _).2 (.inr ⟨hchg q b' hb' hne, fun h' => hq h'.symm⟩)
      · rcases hmem_done a ha with ha | rfl
        · obtain ⟨b', hb', hle⟩ := hdom a ha a' ha'
          by_cases hq : (nb.to, t) = (a.1.1.to, a.1.2)
          · exact ⟨at_, by rw [hins, if_pos hq], tle_trans (himp b' (hq ▸ hb')) hle⟩
          · exact ⟨b', by rw [hins, if_neg hq]; exact hb', hle⟩
        · simp only [hs, Option.some.injEq] at ha'; subst ha'
          exact ⟨at_, by rw [hins, if_pos rfl], tle_refl _⟩
      · intro y hy
        have hy' := heK y hy
        simp only
        split
        · rw [recordEnd_get]
          split
          · split <;> simp
          · exact hy'
        · exact hy'
      · intro y hh a ha
        simp only at ha
        split at ha
        · rename_i hacc
          rw [recordEnd_get] at ha
          split at ha
          · rename_i hy
            subst hy
            split at ha
            · rename_i h0 a0 he0
              cases ha
              obtain ⟨r1, r2, r3, n, hn, q, hq, htq⟩ := heS nb.to hh a0 he0
              refine ⟨r1, r2, r3, ?_⟩
              rcases tmin_cases a0 at_ with h' | h'
              · rw [h']; exact ⟨n, hn, q, hq, htq⟩
              · rw [h']; exact ⟨d + 1, le_refl _, t, hacc, htw⟩
            · rename_i he0
              cases ha
              refine ⟨le_refl _, ⟨t, at_, hacc, htw⟩, fun n hn ⟨q, a'', hq, htq⟩ => ?_, d + 1, le_refl _, t, hacc, htw⟩
              obtain ⟨b, hb, -⟩ := hB2 n (by omega) _ _ htq
              obtain ⟨h1, a1, he1, -⟩ := hE2 nb.to q b hq hb
              exact heK nb.to (by rw [he1]; simp) he0
          · exact heS y hh a ha
        · exact heS y hh a ha
      · intro y q b hq hb
        rw [hins] at hb
        simp only
        split at hb
        · rename_i hyq
          cases hb
          simp only [Prod.mk.injEq] at hyq
          obtain ⟨rfl, rfl⟩ := hyq
          rw [if_pos hq, recordEnd_get, if_pos rfl]
          split
          · rename_i h0 a0 _
            exact ⟨h0, tmin a0 at_, rfl, tmin_tle_right a0 at_⟩
          · exact ⟨d + 1, at_, rfl, tle_refl _⟩
        · obtain ⟨h1, a1, he1, hle⟩ := heD y q b hq hb
          split
          · rw [recordEnd_get]
            split
            · rename_i hy
              subst hy
              rw [he1]
              exact ⟨h1, tmin a1 at_, rfl, tle_trans (tmin_tle_left a1 at_) hle⟩
            · exact ⟨h1, a1, he1, hle⟩
          · exact ⟨h1, a1, he1, hle⟩
      · simp only
        have := upsertNext_length_le next nb.to t at_
        exact ⟨hul, by omega⟩

/-- A fold invariant indexed by the processed prefix, for the elements of a fixed list. -/
theorem ev_foldlM_pre_in {α β : Type} (st : ModelState) (f : β → α → EvM β) (P : List α → β → Prop) (S : List α)
    (hf : ∀ done b a b', a ∈ S → P done b → ev st (f b a) = .ok (.ok b') → P (done ++ [a]) b') :
    ∀ (l done : List α) (init b : β), (∀ a ∈ l, a ∈ S) → P done init →
      ev st (l.foldlM f init) = .ok (.ok b) → P (done ++ l) b
  | [], done, init, b, _, hi, h => by
    simp only [List.foldlM_nil] at h
    rw [ev_pure] at h; cases h; simpa using hi
  | a :: l, done, init, b, hS, hi, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', h1, h2⟩ := ev_bind_ok h
    have := ev_foldlM_pre_in st f P S hf l (done ++ [a]) b' b (fun x hx => hS x (List.mem_cons_of_mem _ hx))
      (hf done init a b' (hS a (List.mem_cons_self ..)) hi h1) h2
    simpa using this

/-- The state of the time-respecting REACH search after `d` layers. -/
structure TInv (R : HopRel) (c : Ctx) (x : Int64) (τ0 : Option Int) (fr : List (Int64 × Nat × Option Int))
    (best : Std.HashMap SState (Option Int)) (ends : Std.HashMap Int64 (Nat × Option Int)) (d used : Nat) : Prop where
  fr1 : ∀ e ∈ fr, best[ekey e]? = some e.2.2 ∧ TW R c.dfa x τ0 d (ekey e) e.2.2
  b1 : ∀ (p : SState) (b : Option Int), best[p]? = some b → ∃ n ≤ d, TW R c.dfa x τ0 n p b
  b2 : ∀ n ≤ d, ∀ p a, TW R c.dfa x τ0 n p a → ∃ b, best[p]? = some b ∧ tle b a
  b3 : ∀ (p : SState) (b : Option Int), best[p]? = some b → (p.1, p.2, b) ∈ fr ∨ Expd R c best p b
  e1 : ∀ (y : Int64) (h : Nat) (a : Option Int), ends[y]? = some (h, a) → h ≤ d ∧ AccT R c x τ0 h y ∧
    (∀ n < h, ¬ AccT R c x τ0 n y) ∧ ∃ n ≤ d, ∃ q, c.dfa.accepts q = true ∧ TW R c.dfa x τ0 n (y, q) a
  e2 : ∀ (y : Int64) (q : Nat) (b : Option Int), c.dfa.accepts q = true → best[(y, q)]? = some b →
    ∃ h a, ends[y]? = some (h, a) ∧ tle a b
  bound : Within c.maxHops d
  usedLe : used ≤ c.limit
  fuel : fr ≠ [] → d + 1 ≤ used

/-- One time-respecting REACH layer preserves the invariant, one hop deeper. -/
theorem tinv_step {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {τ0 : Option Int} (hx : HopsExact st c R)
    {fr next : List (Int64 × Nat × Option Int)} {best best' : Std.HashMap SState (Option Int)}
    {ends ends' : Std.HashMap Int64 (Nat × Option Int)} {d used used' : Nat}
    {exps : List (List ((Nb × Nat) × Option Int))}
    (hI : TInv R c x τ0 fr best ends d used) (hne : fr ≠ []) (hok : c.depthOk d = true)
    (hm : ev st (fr.mapM fun (n, q, tau) => do return ((← expandOne c n q).map (·, tau))) = .ok (.ok exps))
    (hf : ev st (exps.flatten.foldlM (reachTimedStep c d) ([], best, ends, used)) =
      .ok (.ok (next, best', ends', used'))) :
    TInv R c x τ0 next best' ends' (d + 1) used' := by
  have h2 := ev_mapM_forall₂ st _ fr exps hm
  have hexpL : ∀ e L, ev st ((fun (e : Int64 × Nat × Option Int) => match e with
      | (n, q, tau) => (do return ((← expandOne c n q).map (·, tau)) : EvM _)) e) = .ok (.ok L) →
      ∃ L0, ev st (expandOne c e.1 e.2.1) = .ok (.ok L0) ∧ L = L0.map (·, e.2.2) := by
    rintro ⟨n, q, tau⟩ L hL
    obtain ⟨L0, hL0, hL⟩ := ev_bind_ok hL
    exact ⟨L0, hL0, (ev_pure_inj hL).symm⟩
  have horig : ∀ a ∈ exps.flatten, ∃ src, TW R c.dfa x τ0 d src a.2 ∧ PStep R c.dfa src a.1.1 a.1.2 := by
    intro a ha
    obtain ⟨L, hL, ha⟩ := List.mem_flatten.1 ha
    obtain ⟨e, he, hev⟩ := forall₂_mem_right h2 L hL
    obtain ⟨L0, hL0, rfl⟩ := hexpL e L hev
    obtain ⟨⟨nb, t⟩, hin, rfl⟩ := List.mem_map.1 ha
    exact ⟨ekey e, (hI.fr1 e he).2, (hx e.1 e.2.1 L0 hL0 nb t).1 hin⟩
  have hcover : ∀ e ∈ fr, ∀ nb t, PStep R c.dfa (ekey e) nb t → ((nb, t), e.2.2) ∈ exps.flatten := by
    intro e he nb t hs
    obtain ⟨L, hL, hev⟩ := forall₂_mem_left h2 e he
    obtain ⟨L0, hL0, rfl⟩ := hexpL e L hev
    exact List.mem_flatten.2 ⟨_, hL, List.mem_map.2 ⟨(nb, t), (hx e.1 e.2.1 L0 hL0 nb t).2 hs, rfl⟩⟩
  have hT := ev_foldlM_pre_in st (reachTimedStep c d) (fun done acc => TLayer R c x τ0 d best ends used done acc)
    exps.flatten (fun done b a b' ha hb hs => reachTimedStep_layer hI.b2 hI.e2 (horig a ha) hb hs)
    exps.flatten [] _ _ (fun a ha => ha) ?_ hf
  · obtain ⟨hdec, hsound, hnext, -, hchg, hdom, -, heS, heD, hused⟩ := hT
    simp only [List.nil_append] at hdec hsound hnext hchg hdom heS heD hused
    have hdec' : ∀ (q : SState) (b : Option Int), best[q]? = some b → ∀ a, tle b a →
        ∃ b', best'[q]? = some b' ∧ tle b' a := by
      intro q b hb a hba
      obtain ⟨b', hb', hle⟩ := hdec q b hb
      exact ⟨b', hb', tle_trans hle hba⟩
    refine ⟨fun e he => hnext e he, fun p b hb => ?_, fun n hn p a ha => ?_, fun p b hb => ?_, heS, heD,
      within_succ hok, hused.1, fun hne' => ?_⟩
    · rcases hsound p b hb with h | h
      · obtain ⟨n, hn, hw⟩ := hI.b1 p b h; exact ⟨n, by omega, hw⟩
      · exact ⟨d + 1, le_refl _, h⟩
    · by_cases hnd : n ≤ d
      · obtain ⟨b, hb, hle⟩ := hI.b2 n hnd p a ha
        exact hdec' p b hb a hle
      · have : n = d + 1 := by omega
        subst this
        obtain ⟨p0, a0, nb, h0, hs, hto, hst⟩ := (tw_succ R c.dfa x τ0 d p a).1 ha
        obtain ⟨b0, hb0, hle0⟩ := hI.b2 d (le_refl _) p0 a0 h0
        obtain ⟨b0', hb0', hle0'⟩ := stepTime_mono nb hle0 hst
        have hp : p = (nb.to, p.2) := by rw [hto]
        rcases hI.b3 p0 b0 hb0 with hfr | hexp
        · obtain ⟨b', hb', hle⟩ := hdom _ (hcover _ hfr nb p.2 hs) b0' hb0'
          rw [hp]; exact ⟨b', hb', tle_trans hle hle0'⟩
        · obtain ⟨b', hb', hle⟩ := hexp nb p.2 b0' hs hb0'
          rw [hp]; exact hdec' _ b' hb' a (tle_trans hle hle0')
    · by_cases hchanged : best[p]? = some b
      · rcases hI.b3 p b hchanged with hfr | hexp
        · refine .inr fun nb t a' hs hst => ?_
          exact hdom _ (hcover _ hfr nb t hs) a' hst
        · refine .inr fun nb t a' hs hst => ?_
          obtain ⟨b', hb', hle⟩ := hexp nb t a' hs hst
          exact hdec' _ b' hb' a' hle
      · exact .inl (hchg p b hb hchanged)
    · have := hI.fuel hne
      have : 0 < next.length := List.length_pos_of_ne_nil hne'
      omega
  · refine ⟨fun p b hb => ⟨b, hb, tle_refl b⟩, fun p b hb => .inl hb, fun e he => (by cases he), List.nodup_nil,
      fun p b hb hne => absurd hb hne, fun a ha => (by cases ha), fun y hy => hy, fun y h a ha => ?_,
      hI.e2, hI.usedLe, (by simp)⟩
    obtain ⟨r1, r2, r3, n, hn, r4⟩ := hI.e1 y h a ha
    exact ⟨by omega, r2, r3, n, by omega, r4⟩

/-- The time-respecting REACH loop ends in a state satisfying the invariant whose frontier is
empty or whose depth is the hop bound; the fuel never runs out first. -/
theorem reachTimedLoop_inv {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {τ0 : Option Int}
    (hx : HopsExact st c R) :
    ∀ (fuel : Nat) (fr : List (Int64 × Nat × Option Int)) (best : Std.HashMap SState (Option Int))
      (ends res : Std.HashMap Int64 (Nat × Option Int)) (d used : Nat),
      TInv R c x τ0 fr best ends d used → c.limit + 1 ≤ fuel + d →
      ev st (reachTimedLoop c fuel fr best ends d used) = .ok (.ok res) →
      ∃ fr' best' d' used', TInv R c x τ0 fr' best' res d' used' ∧ (fr' = [] ∨ c.depthOk d' = false)
  | 0, fr, best, ends, res, d, used, hI, hf, h => by
    simp only [reachTimedLoop] at h
    cases ev_pure_inj h
    refine ⟨fr, best, d, used, hI, .inl ?_⟩
    by_contra hne
    have := hI.fuel hne; have := hI.usedLe; omega
  | fuel + 1, fr, best, ends, res, d, used, hI, hf, h => by
    simp only [reachTimedLoop] at h
    split at h
    · rename_i hc
      cases ev_pure_inj h
      refine ⟨fr, best, d, used, hI, ?_⟩
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hc
      exact hc
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      obtain ⟨exps, hm, h⟩ := ev_bind_ok h
      obtain ⟨⟨next, best', ends', used'⟩, hl, h⟩ := ev_bind_ok h
      exact reachTimedLoop_inv hx fuel next best' ends' res (d + 1) used'
        (tinv_step hx hI hc.1 hc.2 hm hl) (by omega) h

/-- With an empty frontier every label is expanded, so every time-respecting walk, of any length,
is dominated by a label. -/
theorem tinv_closed {R : HopRel} {c : Ctx} {x : Int64} {τ0 : Option Int} {best : Std.HashMap SState (Option Int)}
    {ends : Std.HashMap Int64 (Nat × Option Int)} {d used : Nat} (hI : TInv R c x τ0 [] best ends d used) :
    ∀ n p a, TW R c.dfa x τ0 n p a → ∃ b, best[p]? = some b ∧ tle b a := by
  intro n
  induction n with
  | zero => exact hI.b2 0 (Nat.zero_le _)
  | succ n ih =>
    intro p a ha
    obtain ⟨p0, a0, nb, h0, hs, hto, hst⟩ := (tw_succ R c.dfa x τ0 n p a).1 ha
    obtain ⟨b0, hb0, hle0⟩ := ih p0 a0 h0
    obtain ⟨b0', hb0', hle0'⟩ := stepTime_mono nb hle0 hst
    rcases hI.b3 p0 b0 hb0 with hfr | hexp
    · cases hfr
    · obtain ⟨b', hb', hle⟩ := hexp nb p.2 b0' hs hb0'
      have hp : p = (nb.to, p.2) := by rw [hto]
      rw [hp]; exact ⟨b', hb', tle_trans hle hle0'⟩

/-- Time-respecting REACH in terms of search states: on success, each row is an end with an
accepting time-respecting walk of its (minimal) hop count within the bound, and its arrival is
achieved within the bound and no later than any time-respecting matching walk within the bound;
every such end has a row; no end repeats. -/
theorem reachTimed_tw {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {τ0 : Option Int}
    (hx : HopsExact st c R) {rows : List PathRow} (h : ev st (reachTimed c x τ0) = .ok (.ok rows)) :
    (∀ r ∈ rows, r = { start := x, «end» := r.end, hops := r.hops, arrival := r.arrival } ∧
      Within c.maxHops r.hops ∧ AccT R c x τ0 r.hops r.end ∧ (∀ n < r.hops, ¬ AccT R c x τ0 n r.end) ∧
      (∃ n, Within c.maxHops n ∧ ∃ q, c.dfa.accepts q = true ∧ TW R c.dfa x τ0 n (r.end, q) r.arrival) ∧
      ∀ n q a, Within c.maxHops n → c.dfa.accepts q = true → TW R c.dfa x τ0 n (r.end, q) a → tle r.arrival a) ∧
    (∀ y n q a, Within c.maxHops n → c.dfa.accepts q = true → TW R c.dfa x τ0 n (y, q) a →
      ∃ r ∈ rows, r.end = y) ∧
    (rows.map PathRow.end).Nodup := by
  unfold reachTimed at h
  obtain ⟨u, hu, h⟩ := ev_bind_ok h
  obtain ⟨rfl, hul⟩ := charge_ok hu
  obtain ⟨ends, hl, h⟩ := ev_bind_ok h
  have hrows := ev_pure_inj h
  have hb : ∀ p, ((∅ : Std.HashMap SState (Option Int)).insert (x, 0) τ0)[p]? =
      if (x, 0) = p then some τ0 else none := by
    intro p; rw [Std.HashMap.getElem?_insert]; simp
  have htw0 : TW R c.dfa x τ0 0 (x, 0) τ0 := (tw_zero ..).2 ⟨rfl, rfl⟩
  have hI : TInv R c x τ0 [(x, 0, τ0)] ((∅ : Std.HashMap SState (Option Int)).insert (x, 0) τ0)
      (if c.dfa.accepts 0 then (∅ : Std.HashMap Int64 (Nat × Option Int)).insert x (0, τ0) else ∅) 0 (0 + 1) := by
    refine ⟨fun e he => ?_, fun p b hp => ?_, fun n hn p a ha => ?_, fun p b hp => ?_, fun y hh a ha => ?_,
      fun y q b hq hp => ?_, fun m _ => Nat.zero_le m, hul, fun _ => le_refl _⟩
    · simp only [List.mem_singleton] at he; subst he
      exact ⟨by rw [hb]; simp [ekey], htw0⟩
    · rw [hb] at hp
      split at hp
      · rename_i he; subst he; cases hp; exact ⟨0, le_refl _, htw0⟩
      · cases hp
    · have : n = 0 := by omega
      subst this
      obtain ⟨rfl, rfl⟩ := (tw_zero ..).1 ha
      exact ⟨_, by rw [hb, if_pos rfl], tle_refl _⟩
    · rw [hb] at hp
      split at hp
      · rename_i he; subst he; cases hp; exact .inl (by simp)
      · cases hp
    · split at ha
      · rename_i hacc
        rw [Std.HashMap.getElem?_insert] at ha
        split at ha
        · rename_i hy
          simp only [beq_iff_eq] at hy; subst hy
          simp only [Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          exact ⟨le_refl _, ⟨0, τ0, hacc, htw0⟩, fun n hn => absurd hn (Nat.not_lt_zero _), 0, le_refl _, 0,
            hacc, htw0⟩
        · simp at ha
      · simp at ha
    · rw [hb] at hp
      split at hp
      · rename_i he
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        cases hp
        rw [if_pos hq, Std.HashMap.getElem?_insert]
        exact ⟨0, τ0, by simp, tle_refl _⟩
      · cases hp
  obtain ⟨fr, best, d, used, hF, hend⟩ := reachTimedLoop_inv hx _ _ _ _ ends _ _ hI (by omega) hl
  have hdomW : ∀ n p a, Within c.maxHops n → TW R c.dfa x τ0 n p a → ∃ b, best[p]? = some b ∧ tle b a := by
    intro n p a hn ha
    rcases hend with hfr | hd
    · subst hfr; exact tinv_closed hF n p a ha
    · cases hm : c.maxHops with
      | none => simp [Ctx.depthOk, hm] at hd
      | some m =>
        simp only [Ctx.depthOk, hm, Option.all_some, decide_eq_false_iff_not, Nat.not_lt] at hd
        have := hF.bound m hm; have := hn m hm
        exact hF.b2 n (by omega) p a ha
  have hmem : ∀ r, r ∈ rows ↔ ∃ y h a, ends[y]? = some (h, a) ∧
      r = { start := x, «end» := y, hops := h, arrival := a } := by
    intro r
    rw [← hrows, List.mem_mergeSort, List.mem_map]
    constructor
    · rintro ⟨⟨y, h, a⟩, hm, rfl⟩
      exact ⟨y, h, a, Std.HashMap.mem_toList_iff_getElem?_eq_some.1 hm, rfl⟩
    · rintro ⟨y, h, a, hm, rfl⟩
      exact ⟨(y, h, a), Std.HashMap.mem_toList_iff_getElem?_eq_some.2 hm, rfl⟩
  refine ⟨fun r hr => ?_, fun y n q a hn hq ha => ?_, ?_⟩
  · obtain ⟨y, h, a, hy, rfl⟩ := (hmem r).1 hr
    obtain ⟨r1, r2, r3, n, hn, q, hq, htq⟩ := hF.e1 y h a hy
    refine ⟨rfl, fun m hm => by have := hF.bound m hm; show h ≤ m; omega, r2, r3,
      ⟨n, fun m hm => by have := hF.bound m hm; omega, q, hq, htq⟩, fun n' q' a' hn' hq' ha' => ?_⟩
    obtain ⟨b, hb, hle⟩ := hdomW n' _ a' hn' ha'
    obtain ⟨h'', a'', he'', hle''⟩ := hF.e2 y q' b hq' hb
    rw [hy] at he''
    simp only [Option.some.injEq, Prod.mk.injEq] at he''
    obtain ⟨-, rfl⟩ := he''
    exact tle_trans hle'' hle
  · obtain ⟨b, hb, -⟩ := hdomW n _ a hn ha
    obtain ⟨h', a', he', -⟩ := hF.e2 y q b hq hb
    exact ⟨_, (hmem _).2 ⟨y, h', a', he', rfl⟩, rfl⟩
  · rw [← hrows, ((List.mergeSort_perm _ _).map _).nodup_iff, List.map_map]
    have hf : (PathRow.end ∘ fun (z : Int64 × Nat × Option Int) => match z with
        | (e, h, a) => ({ start := x, «end» := e, hops := h, arrival := a } : PathRow)) = Prod.fst := by
      funext z; obtain ⟨e, h, a⟩ := z; rfl
    rw [hf]
    have hd := (Std.HashMap.distinct_keys_toList (m := ends))
    unfold List.Nodup
    rw [List.pairwise_map]
    exact hd.imp fun {a b} hab heq => by rw [heq] at hab; simp at hab

theorem tw_mono {R : HopRel} {d : Dfa} {x : Int64} {τ0 τ0' : Option Int} (hτ : tle τ0 τ0') {n : Nat} {p : SState}
    {a' : Option Int} (h : TW R d x τ0' n p a') : ∃ a, TW R d x τ0 n p a ∧ tle a a' := by
  obtain ⟨w, h1, h2, h3, h4⟩ := h
  obtain ⟨a, ha, hle⟩ := timeWalk_mono w hτ h4
  exact ⟨a, ⟨w, h1, h2, h3, ha⟩, hle⟩

theorem tw_acc_iff {R : HopRel} {e : PathExpr} {d : Dfa} (hd : buildDfa (toRE false e) = .ok d) (x y : Int64)
    (τ0 : Option Int) (n : Nat) (a : Option Int) :
    (∃ q, d.accepts q = true ∧ TW R d x τ0 n (y, q) a) ↔
      ∃ w, IsWalk R x w y ∧ word w ∈ lang e ∧ w.length = n ∧ timeWalk w τ0 = some a := by
  constructor
  · rintro ⟨q, hq, w, h1, h2, h3, h4⟩
    exact ⟨w, h2, (match_iff_run hd w).2 ⟨q, h3, hq⟩, h1, h4⟩
  · rintro ⟨w, h1, h2, h3, h4⟩
    obtain ⟨q, hq, hacc⟩ := (match_iff_run hd w).1 h2
    exact ⟨q, hacc, w, h3, h1, hq, h4⟩

/-- path-evaluation "Time-respecting evaluation" (REACH): when the hop layer lists exactly the hops
of `R` and the automaton is compiled from `e`, a successful time-respecting REACH search from `x`
starting at `τ0` returns, once each, the ends of the time-respecting walks of `R` from `x` whose word
is in `lang e` and whose length is within the bound; each row carries the length of a shortest
such walk and the earliest arrival over all of them within the bound (achieved by one). -/
theorem reachTimed_spec {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {e : PathExpr} {τ0 : Option Int}
    (hx : HopsExact st c R) (hd : buildDfa (toRE false e) = .ok c.dfa) {rows : List PathRow}
    (h : ev st (reachTimed c x τ0) = .ok (.ok rows)) :
    (∀ r ∈ rows, r = { start := x, «end» := r.end, hops := r.hops, arrival := r.arrival } ∧
      Within c.maxHops r.hops ∧
      (∃ w a, IsWalk R x w r.end ∧ word w ∈ lang e ∧ w.length = r.hops ∧ timeWalk w τ0 = some a) ∧
      (∀ w a, IsWalk R x w r.end → word w ∈ lang e → timeWalk w τ0 = some a → r.hops ≤ w.length) ∧
      (∃ w, IsWalk R x w r.end ∧ word w ∈ lang e ∧ Within c.maxHops w.length ∧ timeWalk w τ0 = some r.arrival) ∧
      ∀ w a, IsWalk R x w r.end → word w ∈ lang e → Within c.maxHops w.length → timeWalk w τ0 = some a →
        tle r.arrival a) ∧
    (∀ y w a, IsWalk R x w y → word w ∈ lang e → Within c.maxHops w.length → timeWalk w τ0 = some a →
      ∃ r ∈ rows, r.end = y) ∧
    (rows.map PathRow.end).Nodup := by
  obtain ⟨h1, h2, h3⟩ := reachTimed_tw hx h
  refine ⟨fun r hr => ?_, fun y w a hw hl hb ht => ?_, h3⟩
  · obtain ⟨r1, r2, ⟨q, a, hq, htw⟩, r4, ⟨n, hn, q', hq', htw'⟩, r6⟩ := h1 r hr
    refine ⟨r1, r2, ?_, fun w a hw hl ht => ?_, ?_, fun w a hw hl hb ht => ?_⟩
    · obtain ⟨w, h1, h2, h3, h4⟩ := (tw_acc_iff hd x r.end τ0 r.hops a).1 ⟨q, hq, htw⟩
      exact ⟨w, a, h1, h2, h3, h4⟩
    · by_contra hlt
      push Not at hlt
      obtain ⟨q, hq, htw⟩ := (tw_acc_iff hd x r.end τ0 w.length a).2 ⟨w, hw, hl, rfl, ht⟩
      exact r4 w.length hlt ⟨q, a, hq, htw⟩
    · obtain ⟨w, h1, h2, h3, h4⟩ := (tw_acc_iff hd x r.end τ0 n r.arrival).1 ⟨q', hq', htw'⟩
      exact ⟨w, h1, h2, h3 ▸ hn, h4⟩
    · obtain ⟨q, hq, htw⟩ := (tw_acc_iff hd x r.end τ0 w.length a).2 ⟨w, hw, hl, rfl, ht⟩
      exact r6 w.length q a hb hq htw
  · obtain ⟨q, hq, htw⟩ := (tw_acc_iff hd x y τ0 w.length a).2 ⟨w, hw, hl, rfl, ht⟩
    exact h2 y w.length q a hb hq htw

/-- path-evaluation "Time-respecting evaluation" (antitonicity): a later start instant reaches no
more ends, with no fewer hops, and arrives no earlier. -/
theorem reachTimed_antitone {st : ModelState} {c : Ctx} {R : HopRel} {x : Int64} {τ0 τ0' : Option Int}
    (hx : HopsExact st c R) (hτ : tle τ0 τ0') {rows rows' : List PathRow}
    (h : ev st (reachTimed c x τ0) = .ok (.ok rows)) (h' : ev st (reachTimed c x τ0') = .ok (.ok rows')) :
    ∀ r' ∈ rows', ∃ r ∈ rows, r.end = r'.end ∧ r.hops ≤ r'.hops ∧ tle r.arrival r'.arrival := by
  obtain ⟨h1, h2, -⟩ := reachTimed_tw hx h
  obtain ⟨h1', -, -⟩ := reachTimed_tw hx h'
  intro r' hr'
  obtain ⟨-, hb', ⟨q, a', hq, htw'⟩, -, ⟨n, hn, q2, hq2, htw2⟩, -⟩ := h1' r' hr'
  obtain ⟨a, htw, -⟩ := tw_mono hτ htw'
  obtain ⟨r, hr, hre⟩ := h2 r'.end r'.hops q a hb' hq htw
  obtain ⟨-, -, -, hmin, -, hearly⟩ := h1 r hr
  rw [hre] at hmin hearly
  refine ⟨r, hr, hre, ?_, ?_⟩
  · by_contra hlt; push Not at hlt
    exact hmin r'.hops hlt ⟨q, a, hq, htw⟩
  · obtain ⟨a2, htwa2, hle2⟩ := tw_mono hτ htw2
    exact tle_trans (hearly n q2 a2 hn hq2 htwa2) hle2

/-! ## Fuel -/

theorem reachTimedStep_used {st : ModelState} {c : Ctx} {d used0 : Nat}
    {acc acc' : List (Int64 × Nat × Option Int) × Std.HashMap SState (Option Int) ×
      Std.HashMap Int64 (Nat × Option Int) × Nat} {a : (Nb × Nat) × Option Int}
    (hP : acc.2.2.2 ≤ c.limit ∧ used0 + acc.1.length ≤ acc.2.2.2)
    (h : ev st (reachTimedStep c d acc a) = .ok (.ok acc')) :
    acc'.2.2.2 ≤ c.limit ∧ used0 + acc'.1.length ≤ acc'.2.2.2 := by
  obtain ⟨next, best, ends, used⟩ := acc
  obtain ⟨⟨nb, t⟩, tau⟩ := a
  unfold reachTimedStep at h
  simp only at h hP
  cases hs : stepTime nb tau with
  | none => rw [hs] at h; simp only at h; cases ev_pure_inj h; exact hP
  | some at_ =>
    rw [hs] at h; simp only at h
    split at h
    · cases ev_pure_inj h; exact hP
    · obtain ⟨u, hu, h⟩ := ev_bind_ok h
      obtain ⟨rfl, hul⟩ := charge_ok hu
      cases ev_pure_inj h
      have := upsertNext_length_le next nb.to t at_
      simp only
      omega

/-- path-evaluation "Termination and search bound" (time-respecting REACH): every improved label
is a charged search state and a layer is non-empty only after one, so the loop with fuel `f`
(`f + depth ≥ pathMaxStates + 1`, as for the initial call) has the same outcome as with any larger
fuel. -/
theorem reachTimedLoop_fuel {st : ModelState} {c : Ctx} :
    ∀ (f k : Nat) (fr : List (Int64 × Nat × Option Int)) (best : Std.HashMap SState (Option Int))
      (ends : Std.HashMap Int64 (Nat × Option Int)) (d used : Nat),
      used ≤ c.limit → (fr ≠ [] → d + 1 ≤ used) → c.limit + 1 ≤ f + d →
      ev st (reachTimedLoop c f fr best ends d used) = ev st (reachTimedLoop c (f + k) fr best ends d used)
  | 0, k, fr, best, ends, d, used, hle, hfu, hf => by
    have hfr : fr = [] := by
      by_contra hne; have := hfu hne; omega
    subst hfr
    cases k with
    | zero => rfl
    | succ k => simp [reachTimedLoop]
  | f + 1, k, fr, best, ends, d, used, hle, hfu, hf => by
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [reachTimedLoop]
    split
    · rfl
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      apply ev_bind_congr
      intro exps _
      apply ev_bind_congr
      rintro ⟨next, best', ends', used'⟩ hl
      have hP := ev_foldlM_inv (fun acc : List (Int64 × Nat × Option Int) × Std.HashMap SState (Option Int) ×
          Std.HashMap Int64 (Nat × Option Int) × Nat => acc.2.2.2 ≤ c.limit ∧ used + acc.1.length ≤ acc.2.2.2)
        (reachTimedStep c d) st (fun b a b' hb hs => reachTimedStep_used hb hs) exps.flatten _ _ ⟨hle, by simp⟩ hl
      simp only at hP
      refine reachTimedLoop_fuel f k next best' ends' (d + 1) used' hP.1 (fun hne => ?_) (by omega)
      have := hfu hc.1; have : 0 < next.length := List.length_pos_of_ne_nil hne; omega

end Tiramemsu.Path
