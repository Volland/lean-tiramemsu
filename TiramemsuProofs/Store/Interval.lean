/-
Valid time and instants.
Requirements: temporal-views / "Valid-at is half-open"; transaction-log / "Strictly increasing
instants for any clock" (the step lemma).
-/
import Tiramemsu.Engine.Transact
import Mathlib.Tactic

namespace Tiramemsu.Engine

--# @lat: [[verification#Proven Store State Machine]]

namespace Valid

/-- Valid-at is half-open: `[vFrom, vTo)`, absent bounds unbounded. -/
theorem containsInt_iff (v : Valid) (d : Int) :
    v.containsInt d = true ↔
      (∀ a, v.vFrom = some a → a.toInt ≤ d) ∧ (∀ b, v.vTo = some b → d < b.toInt) := by
  rcases v with ⟨f, t⟩
  cases f <;> cases t <;> simp [containsInt]

theorem validAt_iff (v : Valid) (d : Int64) :
    v.validAt d = true ↔
      (∀ a, v.vFrom = some a → a.toInt ≤ d.toInt) ∧ (∀ b, v.vTo = some b → d.toInt < b.toInt) :=
  containsInt_iff v d.toInt

theorem nonempty_iff (v : Valid) :
    v.nonempty = true ↔ ∀ a b, v.vFrom = some a → v.vTo = some b → a.toInt < b.toInt := by
  rcases v with ⟨f, t⟩
  cases f <;> cases t <;> simp [nonempty]

/-- `check` fails exactly on empty intervals. -/
theorem check_ok_iff (v : Valid) : v.check = .ok () ↔ v.nonempty = true := by
  rcases v with ⟨f, t⟩
  cases f <;> cases t <;> simp [check, nonempty]

/-- On nonempty intervals, the overlap test of assert and cardinality one holds exactly when
some instant lies in both. -/
theorem overlaps_iff {i j : Valid} (hi : i.nonempty = true) (hj : j.nonempty = true) :
    overlaps i j = true ↔ ∃ d : Int, i.containsInt d = true ∧ j.containsInt d = true := by
  rcases i with ⟨f1, t1⟩
  rcases j with ⟨f2, t2⟩
  simp only [nonempty] at hi hj
  constructor
  · intro h
    simp only [overlaps, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    -- the larger lower bound (or one below the smaller upper bound) is in both
    let lo : Option Int := match f1, f2 with
      | some a, some b => some (max a.toInt b.toInt)
      | some a, none => some a.toInt
      | none, some b => some b.toInt
      | none, none => none
    let hiB : Option Int := match t1, t2 with
      | some a, some b => some (min a.toInt b.toInt)
      | some a, none => some a.toInt
      | none, some b => some b.toInt
      | none, none => none
    refine ⟨match lo, hiB with
      | some l, _ => l
      | none, some h => h - 1
      | none, none => 0, ?_⟩
    cases f1 <;> cases f2 <;> cases t1 <;> cases t2 <;>
      simp_all [containsInt, lo, hiB]
  · rintro ⟨d, h1, h2⟩
    cases f1 <;> cases f2 <;> cases t1 <;> cases t2 <;>
      simp_all [containsInt, overlaps] <;> omega

end Valid

/-- The next instant is always after the previous one, whatever the clock reads. -/
theorem lt_nextInstant (prev now : Int) : prev < nextInstant prev now := by
  unfold nextInstant; omega

/-- The next instant is the clock reading when the clock is ahead. -/
theorem nextInstant_of_le {prev now : Int} (h : prev < now) : nextInstant prev now = now := by
  unfold nextInstant; omega

/-- Instants assigned by any sequence of clock readings are strictly increasing. -/
def instantsOf (start : Int) : List Int → List Int
  | [] => []
  | now :: rest => nextInstant start now :: instantsOf (nextInstant start now) rest

theorem lt_instantsOf (start : Int) (clock : List Int) : ∀ x ∈ instantsOf start clock, start < x := by
  induction clock generalizing start with
  | nil => simp [instantsOf]
  | cons now rest ih =>
    intro x hx
    simp only [instantsOf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact lt_nextInstant start now
    · exact lt_trans (lt_nextInstant start now) (ih _ x hx)

/-- Whatever the clock readings (standing still or moving backwards), the instants of
consecutive commits are strictly increasing. -/
theorem instantsOf_increasing (start : Int) (clock : List Int) :
    (start :: instantsOf start clock).Pairwise (· < ·) := by
  induction clock generalizing start with
  | nil => simp [instantsOf]
  | cons now rest ih =>
    refine List.Pairwise.cons ?_ ?_
    · intro x hx
      simp only [instantsOf, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact lt_nextInstant start now
      · exact lt_trans (lt_nextInstant start now) (lt_instantsOf _ _ x hx)
    · simpa [instantsOf] using ih (nextInstant start now)

end Tiramemsu.Engine
