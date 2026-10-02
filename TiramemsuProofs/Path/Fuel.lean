/-
path-evaluation "Termination and search bound": every search loop runs on explicit fuel
`pathMaxStates + 1`, and searching with that fuel returns the same result as searching with any
larger fuel. A layer is searched only when the previous one charged a new search state, and
more than `pathMaxStates` charged states fail with `PathLimitExceeded`, so the loop always stops
(empty layer, hop bound or limit) before the fuel runs out.
-/
import Tiramemsu.Path.Search
import TiramemsuProofs.Store.Reads
import Mathlib.Tactic

namespace Tiramemsu.Path

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Exec
open Tiramemsu.Engine (RProg ROp)

--# @lat: [[query#Paths#Search]]

/-! ## Evaluator programs on a model state -/

/-- An evaluator program run on a model state. -/
def ev {α : Type} (st : ModelState) (x : EvM α) : Except StoreError (Except QError α) :=
  RProg.onModel st x.run

theorem ev_bind {α β : Type} (st : ModelState) (x : EvM α) (f : α → EvM β) :
    ev st (x >>= f) = match ev st x with
      | .ok (.ok a) => ev st (f a)
      | .ok (.error e) => .ok (.error e)
      | .error e => .error e := by
  unfold ev RProg.onModel
  rw [ExceptT.run_bind, Engine.RProg.runPure_bind]
  cases RProg.runPure ROp.model st x.run with
  | error e => rfl
  | ok r => cases r <;> rfl

@[simp] theorem ev_pure {α : Type} (st : ModelState) (a : α) : ev st (pure a : EvM α) = .ok (.ok a) := rfl

@[simp] theorem ev_throw {α : Type} (st : ModelState) (e : QError) : ev st (throw e : EvM α) = .ok (.error e) := rfl

theorem ev_bind_ok {α β : Type} {st : ModelState} {x : EvM α} {f : α → EvM β} {b : β}
    (h : ev st (x >>= f) = .ok (.ok b)) : ∃ a, ev st x = .ok (.ok a) ∧ ev st (f a) = .ok (.ok b) := by
  rw [ev_bind] at h
  split at h
  · rename_i a ha; exact ⟨a, ha, h⟩
  · cases h
  · cases h

theorem ev_bind_congr {α β : Type} (st : ModelState) (x : EvM α) {f g : α → EvM β}
    (h : ∀ a, ev st x = .ok (.ok a) → ev st (f a) = ev st (g a)) : ev st (x >>= f) = ev st (x >>= g) := by
  rw [ev_bind, ev_bind]
  split
  · rename_i a ha; exact h a ha
  · rfl
  · rfl

theorem ev_foldlM_inv {α β : Type} (P : β → Prop) (f : β → α → EvM β) (st : ModelState)
    (hf : ∀ b a b', P b → ev st (f b a) = .ok (.ok b') → P b') :
    ∀ (l : List α) (init b : β), P init → ev st (l.foldlM f init) = .ok (.ok b) → P b
  | [], init, b, hi, h => by
    simp only [List.foldlM_nil] at h
    have : (pure init : EvM β) = pure b := by
      have h' : ev st (pure init : EvM β) = .ok (.ok b) := h
      simp at h'; rw [h']
    simp at h; subst h; exact hi
  | a :: l, init, b, hi, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b', h1, h2⟩ := ev_bind_ok h
    exact ev_foldlM_inv P f st hf l b' b (hf init a b' hi h1) h2

theorem charge_ok {c : Ctx} {used n u : Nat} {st : ModelState} (h : ev st (charge c used n) = .ok (.ok u)) :
    u = used + n ∧ u ≤ c.limit := by
  unfold charge at h
  split at h
  · simp at h
  · rename_i hle
    simp at h
    omega

end Tiramemsu.Path
