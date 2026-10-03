/-
path-evaluation "Time-respecting evaluation", the search bound: the time-respecting REACH search
improves the label of each search state at most once per possible arrival value, so it charges
at most `card U · card Tv` labels, where `U` holds the search states (`N · Q`) and `Tv` the
arrival values (the start instant and the statements' start times, `card T + 1`). Hence the loop
with fuel `card U · card Tv + 1` layers already has the same outcome as with any larger fuel,
whatever the state budget.

The proof is a potential argument: each label counts the possible arrival values strictly before
it (a missing label counts all of them); every charged improvement lowers the sum by at least one.
-/
import TiramemsuProofs.Path.Timed

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Store Tiramemsu.Exec

--# @lat: [[query#Paths#Path Specification]]

/-! ## The potential -/

/-- The possible arrival values strictly before `b`. -/
def lowerCount (Tv : Finset (Option Int)) (b : Option Int) : Nat := (Tv.filter fun v => better v b = true).card

/-- The potential of a label table over the search states `U`. -/
def pot (U : Finset SState) (Tv : Finset (Option Int)) (best : Std.HashMap SState (Option Int)) : Nat :=
  ∑ p ∈ U, match best[p]? with
    | none => Tv.card
    | some b => lowerCount Tv b

theorem better_irrefl (a : Option Int) : better a a = false := by
  cases a <;> simp [better]

theorem better_trans {a b c : Option Int} (h1 : better a b = true) (h2 : better b c = true) : better a c = true := by
  rw [better_iff] at *
  intro h
  rcases tle_total a b with h' | h'
  · exact h2 (tle_trans h h')
  · exact h1 h'

theorem lowerCount_lt_card {Tv : Finset (Option Int)} {b : Option Int} (hb : b ∈ Tv) : lowerCount Tv b < Tv.card := by
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := h hb
  simp [better_irrefl] at this

theorem lowerCount_lt {Tv : Finset (Option Int)} {b b' : Option Int} (hb' : b' ∈ Tv) (h : better b' b = true) :
    lowerCount Tv b' < lowerCount Tv b := by
  apply Finset.card_lt_card
  refine ⟨fun v hv => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, better_trans hv.2 h⟩
  · have := hsub (Finset.mem_filter.2 ⟨hb', h⟩)
    simp [better_irrefl] at this

/-- Recording a strictly earlier label (or a first one) lowers the potential. -/
theorem pot_insert_lt {U : Finset SState} {Tv : Finset (Option Int)} {best : Std.HashMap SState (Option Int)}
    {p : SState} {b' : Option Int} (hp : p ∈ U) (hb' : b' ∈ Tv)
    (hold : ∀ b, best[p]? = some b → better b' b = true) :
    pot U Tv (best.insert p b') < pot U Tv best := by
  unfold pot
  rw [← Finset.add_sum_erase _ _ hp, ← Finset.add_sum_erase _ _ hp]
  have hrest : ∑ q ∈ U.erase p, (match (best.insert p b')[q]? with
      | none => Tv.card | some b => lowerCount Tv b) =
      ∑ q ∈ U.erase p, (match best[q]? with | none => Tv.card | some b => lowerCount Tv b) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Std.HashMap.getElem?_insert]
    have : (p == q) = false := by simpa using (Finset.ne_of_mem_erase hq).symm
    rw [this]; rfl
  rw [hrest, Std.HashMap.getElem?_insert]
  simp only [beq_self_eq_true, if_true]
  apply Nat.add_lt_add_right
  cases hb : best[p]? with
  | none => exact lowerCount_lt_card hb'
  | some b => exact lowerCount_lt hb' (hold b hb)

theorem pot_le (U : Finset SState) (Tv : Finset (Option Int)) (best : Std.HashMap SState (Option Int)) :
    pot U Tv best ≤ U.card * Tv.card := by
  unfold pot
  calc _ ≤ ∑ _p ∈ U, Tv.card := Finset.sum_le_sum fun q _ => by
        split
        · exact le_refl _
        · exact Finset.card_filter_le _ _
    _ = U.card * Tv.card := by simp

/-! ## Each charge lowers the potential -/

/-- The fold state of a time-respecting REACH layer under the potential. -/
structure PLayer (U : Finset SState) (Tv : Finset (Option Int)) (C used0 : Nat)
    (acc : List (Int64 × Nat × Option Int) × Std.HashMap SState (Option Int) ×
      Std.HashMap Int64 (Nat × Option Int) × Nat) : Prop where
  labels : ∀ (p : SState) (b : Option Int), acc.2.1[p]? = some b → p ∈ U ∧ b ∈ Tv
  potLe : acc.2.2.2 + pot U Tv acc.2.1 ≤ C
  grow : used0 + acc.1.length ≤ acc.2.2.2
  next : ∀ e ∈ acc.1, acc.2.1[ekey e]? = some e.2.2
  keys : (acc.1.map ekey).Nodup

theorem reachTimedStep_pot {st : ModelState} {c : Ctx} {d : Nat} {U : Finset SState} {Tv : Finset (Option Int)}
    {C used0 : Nat} {acc acc' : List (Int64 × Nat × Option Int) × Std.HashMap SState (Option Int) ×
      Std.HashMap Int64 (Nat × Option Int) × Nat} {a : (Nb × Nat) × Option Int}
    (hU : (a.1.1.to, a.1.2) ∈ U) (hT : ∀ a', stepTime a.1.1 a.2 = some a' → a' ∈ Tv)
    (hP : PLayer U Tv C used0 acc) (h : ev st (reachTimedStep c d acc a) = .ok (.ok acc')) :
    PLayer U Tv C used0 acc' := by
  obtain ⟨next, best, ends, used⟩ := acc
  obtain ⟨⟨nb, t⟩, tau⟩ := a
  obtain ⟨hl, hpot, hgrow, hnext, hkeys⟩ := hP
  simp only at hl hpot hgrow hnext hkeys hU hT
  unfold reachTimedStep at h
  simp only at h
  cases hs : stepTime nb tau with
  | none => rw [hs] at h; simp only at h; cases ev_pure_inj h; exact ⟨hl, hpot, hgrow, hnext, hkeys⟩
  | some at_ =>
    rw [hs] at h; simp only at h
    split at h
    · cases ev_pure_inj h; exact ⟨hl, hpot, hgrow, hnext, hkeys⟩
    · rename_i hc
      obtain ⟨u, hu, h⟩ := ev_bind_ok h
      obtain ⟨rfl, -⟩ := charge_ok hu
      cases ev_pure_inj h
      rw [Std.HashMap.get?_eq_getElem?] at hc
      have hat : at_ ∈ Tv := hT at_ hs
      have hold : ∀ b, best[(nb.to, t)]? = some b → better at_ b = true := by
        intro b hb; rw [hb] at hc
        simpa using hc
      have hlt := pot_insert_lt hU hat hold
      obtain ⟨hukeys, -, hupm⟩ := upsertNext_spec next nb.to t at_ hkeys
      have hins : ∀ q : SState, (best.insert (nb.to, t) at_)[q]? = if (nb.to, t) = q then some at_ else best[q]? := by
        intro q; rw [Std.HashMap.getElem?_insert]; simp only [beq_iff_eq]
      refine ⟨fun q b hb => ?_, by simp only; omega, ?_, fun e he => ?_, hukeys⟩
      · rw [hins] at hb
        split at hb
        · rename_i hq; subst hq; cases hb; exact ⟨hU, hat⟩
        · exact hl q b hb
      · simp only
        have := upsertNext_length_le next nb.to t at_
        omega
      · rcases (hupm e).1 he with rfl | ⟨he, hk⟩
        · rw [hins]; simp [ekey]
        · rw [hins, if_neg (fun h' => hk h'.symm)]; exact hnext e he

/-! ## The search bound -/

/-- The loop state under the potential: labels and frontier within `U × Tv`, and the charged
labels plus the potential at most `card U · card Tv`. -/
structure PInv (U : Finset SState) (Tv : Finset (Option Int)) (fr : List (Int64 × Nat × Option Int))
    (best : Std.HashMap SState (Option Int)) (d used : Nat) : Prop where
  labels : ∀ (p : SState) (b : Option Int), best[p]? = some b → p ∈ U ∧ b ∈ Tv
  front : ∀ e ∈ fr, best[ekey e]? = some e.2.2
  potLe : used + pot U Tv best ≤ U.card * Tv.card
  fuel : fr ≠ [] → d + 1 ≤ used

/-- path-evaluation "Time-respecting evaluation" (search bound): when every search transition
stays in the search states `U` and the hop rule keeps arrivals in `Tv`, the time-respecting REACH
loop with fuel `f` (`f + depth ≥ card U · card Tv + 1`) has the same outcome as with any larger
fuel — independently of the state budget. For a store, `U` is the nodes times the automaton states
(`N · Q`) and `Tv` the start instant and the statements' start times (`card T + 1`). -/
theorem reachTimedLoop_bound {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R)
    {U : Finset SState} {Tv : Finset (Option Int)}
    (hU : ∀ p nb t, PStep R c.dfa p nb t → (nb.to, t) ∈ U)
    (hT : ∀ p nb t a a', PStep R c.dfa p nb t → a ∈ Tv → stepTime nb a = some a' → a' ∈ Tv) :
    ∀ (f k : Nat) (fr : List (Int64 × Nat × Option Int)) (best : Std.HashMap SState (Option Int))
      (ends : Std.HashMap Int64 (Nat × Option Int)) (d used : Nat),
      PInv U Tv fr best d used → U.card * Tv.card + 1 ≤ f + d →
      ev st (reachTimedLoop c f fr best ends d used) = ev st (reachTimedLoop c (f + k) fr best ends d used)
  | 0, k, fr, best, ends, d, used, hI, hf => by
    have hfr : fr = [] := by
      by_contra hne; have := hI.fuel hne; have := hI.potLe; omega
    subst hfr
    cases k with
    | zero => rfl
    | succ k => simp [reachTimedLoop]
  | f + 1, k, fr, best, ends, d, used, hI, hf => by
    rw [show f + 1 + k = (f + k) + 1 by omega]
    simp only [reachTimedLoop]
    split
    · rfl
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff, not_or, Bool.not_eq_false] at hc
      apply ev_bind_congr
      intro exps hm
      apply ev_bind_congr
      rintro ⟨next, best', ends', used'⟩ hl
      have h2 := ev_mapM_forall₂ st _ fr exps hm
      have horig : ∀ a ∈ exps.flatten, (a.1.1.to, a.1.2) ∈ U ∧ ∀ a', stepTime a.1.1 a.2 = some a' → a' ∈ Tv := by
        intro a ha
        obtain ⟨L, hL, ha⟩ := List.mem_flatten.1 ha
        obtain ⟨e, he, hev⟩ := forall₂_mem_right h2 L hL
        obtain ⟨n, q, tau⟩ := e
        obtain ⟨L0, hL0, hL⟩ := ev_bind_ok hev
        cases ev_pure_inj hL
        obtain ⟨⟨nb, t⟩, hin, rfl⟩ := List.mem_map.1 ha
        have hs := (hx n q L0 hL0 nb t).1 hin
        have hlab := hI.labels _ _ (hI.front _ he)
        exact ⟨hU _ nb t hs, fun a' ha' => hT _ nb t tau a' hs hlab.2 ha'⟩
      have hP := ev_foldlM_pre_in st (reachTimedStep c d) (fun _ acc => PLayer U Tv (used + pot U Tv best) used acc)
        exps.flatten (fun done b a b' ha hb hs => reachTimedStep_pot (horig a ha).1 (horig a ha).2 hb hs)
        exps.flatten [] _ _ (fun a ha => ha) ⟨hI.labels, le_refl _, by simp, by simp, by simp⟩ hl
      obtain ⟨hl', hpot', hgrow', hnext', -⟩ := hP
      simp only at hl' hpot' hgrow' hnext'
      refine reachTimedLoop_bound hx hU hT f k next best' ends' (d + 1) used'
        ⟨hl', hnext', by have := hI.potLe; omega, fun hne => ?_⟩ (by omega)
      have := hI.fuel hc.1; have : 0 < next.length := List.length_pos_of_ne_nil hne; omega

/-- The search bound for a whole time-respecting REACH search from `x` at `τ0`: its loop, run with
the state budget's fuel `pathMaxStates + 1`, has the outcome of the loop run with fuel
`card U · card Tv + 1` (`N · Q · (card T + 1) + 1` layers for a store). -/
theorem reachTimed_bound {st : ModelState} {c : Ctx} {R : HopRel} (hx : HopsExact st c R)
    {U : Finset SState} {Tv : Finset (Option Int)}
    (hU : ∀ p nb t, PStep R c.dfa p nb t → (nb.to, t) ∈ U)
    (hT : ∀ p nb t a a', PStep R c.dfa p nb t → a ∈ Tv → stepTime nb a = some a' → a' ∈ Tv)
    {x : Int64} {τ0 : Option Int} (hx0 : (x, 0) ∈ U) (hτ0 : τ0 ∈ Tv) (hl : 1 ≤ c.limit)
    (ends : Std.HashMap Int64 (Nat × Option Int)) :
    ev st (reachTimedLoop c (c.limit + 1) [(x, 0, τ0)] ((∅ : Std.HashMap SState (Option Int)).insert (x, 0) τ0)
        ends 0 1) =
      ev st (reachTimedLoop c (U.card * Tv.card + 1) [(x, 0, τ0)]
        ((∅ : Std.HashMap SState (Option Int)).insert (x, 0) τ0) ends 0 1) := by
  have hpot0 : pot U Tv (∅ : Std.HashMap SState (Option Int)) = U.card * Tv.card := by
    unfold pot; simp
  have hpot := pot_insert_lt (best := (∅ : Std.HashMap SState (Option Int))) hx0 hτ0 (fun b hb => by simp at hb)
  have hI : PInv U Tv [(x, 0, τ0)] ((∅ : Std.HashMap SState (Option Int)).insert (x, 0) τ0) 0 1 := by
    refine ⟨fun p b hb => ?_, fun e he => ?_, by omega, fun _ => le_refl _⟩
    · rw [Std.HashMap.getElem?_insert] at hb
      split at hb
      · rename_i hp; simp only [beq_iff_eq] at hp; subst hp; cases hb; exact ⟨hx0, hτ0⟩
      · simp at hb
    · simp only [List.mem_singleton] at he; subst he
      simp [ekey]
  rw [reachTimedLoop_fuel (c.limit + 1) (U.card * Tv.card + 1) _ _ _ 0 1 hl (fun _ => le_refl _) (by omega),
    reachTimedLoop_bound hx hU hT (U.card * Tv.card + 1) (c.limit + 1) _ _ _ 0 1 hI (by omega),
    show c.limit + 1 + (U.card * Tv.card + 1) = U.card * Tv.card + 1 + (c.limit + 1) by omega]

end Tiramemsu.Path
