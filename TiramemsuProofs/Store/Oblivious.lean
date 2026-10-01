/-
Body operations never look at the savepoint stack: running one on a store with other savepoints
gives the same result and the same store up to the savepoints. Speculation and dry runs open a
savepoint before the body, so their bodies compute exactly what a commit's body computes.
-/
import TiramemsuProofs.Store.Transact
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-- The store with another savepoint stack. -/
def withSps (s : ModelStore) (l : List (String × ModelState)) : ModelStore := { s with sps := l }

/-- A computation that ignores the savepoint stack. -/
def Ob {α : Type} (x : ModelM α) : Prop :=
  ∀ s l, x (withSps s l) = match x s with
    | .ok (a, s') => .ok (a, withSps s' l)
    | .error e => .error e

theorem Ob.pure {α : Type} (a : α) : Ob (pure a : ModelM α) := fun _ _ => rfl

theorem Ob.throw {α : Type} (e : StoreError) : Ob (throw e : ModelM α) := fun _ _ => rfl

theorem Ob.bind {α β : Type} {x : ModelM α} {f : α → ModelM β} (hx : Ob x) (hf : ∀ a, Ob (f a)) :
    Ob (x >>= f) := by
  intro s l
  rw [mbind, mbind, hx]
  cases x s with
  | ok p => rcases p with ⟨a, s'⟩; exact hf a s' l
  | error e => rfl

theorem Ob.ite {α : Type} {c : Prop} [Decidable c] {x y : ModelM α} (hx : Ob x) (hy : Ob y) :
    Ob (if c then x else y) := by
  by_cases h : c
  · rw [if_pos h]; exact hx
  · rw [if_neg h]; exact hy

theorem Ob.read {α : Type} (f : ModelState → α) : Ob (ModelM.read f) := fun _ _ => rfl

theorem Ob.counter (n : String) : Ob (ReadStore.counter n : ModelM (Option Int64)) := fun _ _ => rfl
theorem Ob.base (n : String) : Ob (WriteStore.baseCounter n : ModelM (Option Int64)) := fun _ _ => rfl
theorem Ob.triple (e : Int64) : Ob (ReadStore.triple e : ModelM (Option TripleRow)) := fun _ _ => rfl
theorem Ob.predMulti (p : Int64) : Ob (ReadStore.predMulti p : ModelM Bool) := fun _ _ => rfl

theorem Ob.data {op : WriteOp} (hd : op.isData = true) : Ob op.exec := by
  intro s l
  rw [mexec, mexec, run_data hd, run_data hd]
  simp only [withSps]
  by_cases htx : s.inTx = true
  · simp only [htx, if_true]
    cases op.step s.current <;> rfl
  · simp only [htx]; rfl

theorem Ob.read_op (r : ROp) : Ob (ROp.run r : ModelM r.Res) := by
  intro s l
  rw [read_model, read_model]
  simp only [withSps]
  cases ROp.model r s.current <;> rfl

theorem ob_needCounter (n : String) : Ob (needCounter (m := ModelM) n) := by
  unfold needCounter
  refine Ob.bind (Ob.counter n) fun o => ?_
  cases o
  · exact Ob.throw _
  · exact Ob.pure _

theorem ob_needBase (n : String) : Ob (needBase (m := ModelM) n) := by
  unfold needBase
  refine Ob.bind (Ob.base n) fun o => ?_
  cases o
  · exact Ob.throw _
  · exact Ob.pure _

theorem Ob.op (o : Op) : Ob (Op.run o : ModelM o.Res) := by
  cases o with
  | read r => exact Ob.read_op r
  | alloc c =>
    unfold Op.run allocRun
    exact Ob.bind (ob_needCounter _) fun n =>
      Ob.ite (Ob.bind (Ob.data rfl) fun _ => Ob.pure _) (Ob.pure _)
  | insert r =>
    unfold Op.run insertRun
    exact Ob.bind (ob_needBase _) fun _ => Ob.bind (ob_needBase _) fun _ => Ob.bind (ob_needCounter _) fun _ =>
      Ob.ite (Ob.data rfl) (Ob.throw _)
  | retract e k =>
    unfold Op.run retractRun
    refine Ob.bind (ob_needBase _) fun _ => Ob.ite (Ob.bind (Ob.triple _) fun o => ?_) (Ob.throw _)
    cases o with
    | none => exact Ob.pure _
    | some r => exact Ob.ite (Ob.bind (Ob.data rfl) fun _ => Ob.pure _) (Ob.pure _)
  | intern k num =>
    unfold Op.run internKey
    refine Ob.bind (Ob.read _) fun o => ?_
    cases o with
    | some _ => exact Ob.pure _
    | none =>
      exact Ob.bind (Ob.bind (Ob.counter _) fun _ => Ob.pure _) fun _ =>
        Ob.ite (Ob.bind (Ob.data rfl) fun _ => Ob.bind (Ob.data rfl) fun _ => Ob.pure _) (Ob.pure _)
  | volPut r => exact Ob.data rfl
  | volDel a k => exact Ob.data rfl
  | markMulti p =>
    unfold Op.run markMultiRun
    exact Ob.bind (Ob.predMulti _) fun _ =>
      Ob.ite (Ob.bind (Ob.data rfl) fun _ => Ob.bind (ob_needCounter _) fun _ => Ob.data rfl) (Ob.pure _)

/-- A body program ignores the savepoint stack. -/
theorem runModel_withSps {α : Type} : ∀ (p : SProg α) (s : ModelStore) (l : List (String × ModelState)),
    SProg.runModel p (withSps s l) = match SProg.runModel p s with
      | .ok (a, s') => .ok (a, withSps s' l)
      | .error e => .error e
  | .pure a, s, l => rfl
  | .op o k, s, l => by
    simp only [SProg.runModel]
    rw [Ob.op o s l]
    cases (Op.run o : ModelM o.Res) s with
    | ok p => rcases p with ⟨x, s'⟩; exact runModel_withSps (k x) s' l
    | error e => rfl

end Tiramemsu.Engine
