/-
The engine's store operations on the model store, computed: what each body operation does to
the current state, and that none touches the committed state, the transaction flag or the
savepoints.
-/
import Tiramemsu.Engine.Op
import TiramemsuProofs.Store.Reads
import Mathlib.Tactic

namespace Tiramemsu.Engine

open Tiramemsu.Store Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Proven Store State Machine]]

/-! ## The model monad, computed -/

section
variable {α β : Type}

theorem mbind (x : ModelM α) (f : α → ModelM β) (s : ModelStore) :
    (x >>= f) s = (match x s with | .ok (a, s') => f a s' | .error e => .error e) := by
  show (StateT.bind x f) s = _
  simp only [StateT.bind]
  show (do let (a, s) ← x s; f a s : Except StoreError (β × ModelStore)) = _
  cases x s with
  | ok p => rcases p with ⟨a, s'⟩; rfl
  | error e => rfl

theorem mpure (a : α) (s : ModelStore) : (pure a : ModelM α) s = .ok (a, s) := rfl

theorem mthrow (e : StoreError) (s : ModelStore) : (throw e : ModelM α) s = .error e := rfl

theorem mexec (op : WriteOp) (s : ModelStore) :
    op.exec s = match op.run s with | .ok s' => .ok ((), s') | .error e => .error e := rfl

theorem mcounter (n : String) (s : ModelStore) :
    (ReadStore.counter n : ModelM (Option Int64)) s = .ok (s.current.counter n, s) := rfl
theorem mbase (n : String) (s : ModelStore) :
    (WriteStore.baseCounter n : ModelM (Option Int64)) s = .ok (s.committed.counter n, s) := rfl
theorem mtriple (e : Int64) (s : ModelStore) :
    (ReadStore.triple e : ModelM (Option TripleRow)) s = .ok (s.current.triple e, s) := rfl
theorem mpredMulti (p : Int64) (s : ModelStore) :
    (ReadStore.predMulti p : ModelM Bool) s = .ok (s.current.isPredMulti p, s) := rfl
theorem mlookupKey (k : TermKey) (s : ModelStore) :
    (TermReader.lookupKey k : ModelM (Option Nat)) s = .ok (modelLookupKey s.current k, s) := rfl
theorem mrowById (i : Nat) (s : ModelStore) :
    (TermReader.rowById i : ModelM (Option Row)) s = .ok (modelRowById s.current i, s) := rfl

theorem minsertTriple (r : TripleRow) (s : ModelStore) :
    (WriteStore.insertTriple r : ModelM Unit) s = (WriteOp.insertTriple r).exec s := rfl
theorem mretract (e t k : Int64) (s : ModelStore) :
    (WriteStore.retract e t k : ModelM Unit) s = (WriteOp.retract e t k).exec s := rfl
theorem msetCounter (n : String) (v : Int64) (s : ModelStore) :
    (WriteStore.setCounter n v : ModelM Unit) s = (WriteOp.setCounter n v).exec s := rfl
theorem minsertTerm (r : TermRow) (s : ModelStore) :
    (WriteStore.insertTerm r : ModelM Unit) s = (WriteOp.insertTerm r).exec s := rfl
theorem mvolPut (r : VolatileRow) (s : ModelStore) :
    (WriteStore.volatilePut r : ModelM Unit) s = (WriteOp.volatilePut r).exec s := rfl
theorem mvolDel (a k : Int64) (s : ModelStore) :
    (WriteStore.volatileDel a k : ModelM Unit) s = (WriteOp.volatileDel a k).exec s := rfl
theorem maddPredMulti (p : Int64) (s : ModelStore) :
    (WriteStore.addPredMulti p : ModelM Unit) s = (WriteOp.addPredMulti p).exec s := rfl

/-- A data write on the model: in a transaction, the step on the current state. -/
theorem data_exec {op : WriteOp} (hd : op.isData = true) {s s' : ModelStore} {u : Unit}
    (h : op.exec s = .ok (u, s')) :
    s.inTx = true ∧ ∃ c, op.step s.current = .ok c ∧ s' = { s with current := c } := by
  rw [mexec] at h
  cases hr : op.run s with
  | ok s'' => rw [hr] at h; cases h; exact run_data_ok hd hr
  | error e => rw [hr] at h; cases h

end

/-! ## Counters -/

theorem find_map_set (l : List (String × Int64)) (n m : String) (v : Int64) :
    (l.map (fun kv => if kv.1 == n then (kv.1, v) else kv)).find? (·.1 == m) =
      if m = n then (if l.any (·.1 == n) then some (n, v) else none) else l.find? (·.1 == m) := by
  induction l with
  | nil => by_cases h : m = n <;> simp [h]
  | cons a as ih =>
    rcases a with ⟨k, x⟩
    by_cases hk : k = n
    · subst hk
      by_cases hm : m = k
      · subst hm
        simp only [List.map_cons, List.find?_cons, beq_self_eq_true, if_true, List.any_cons, Bool.true_or]
      · have : (k == m) = false := by simpa using Ne.symm hm
        simp only [List.map_cons, List.find?_cons, beq_self_eq_true, if_true, this, ih, if_neg hm]
    · have hkn : (k == n) = false := by simpa using hk
      by_cases hm : k = m
      · subst hm
        simp only [List.map_cons, List.find?_cons, hkn, Bool.false_eq_true, if_false, beq_self_eq_true]
        rw [if_neg hk]
      · have hkm : (k == m) = false := by simpa using hm
        simp only [List.map_cons, List.find?_cons, hkn, Bool.false_eq_true, if_false, hkm, ih, List.any_cons,
          Bool.false_or]

theorem find_append_none (l : List (String × Int64)) (n m : String) (v : Int64)
    (h : l.any (·.1 == n) = false) :
    (l ++ [(n, v)]).find? (·.1 == m) = if m = n then some (n, v) else l.find? (·.1 == m) := by
  rw [List.find?_append]
  by_cases hm : m = n
  · subst hm
    have : l.find? (·.1 == m) = none := by
      rw [List.find?_eq_none]; intro x hx
      have := List.any_eq_false.1 h x hx
      simpa using this
    simp [this]
  · rw [if_neg hm]
    cases l.find? (·.1 == m) with
    | some x => rfl
    | none => simp [Ne.symm hm]

theorem counter_setCounter (st : ModelState) (n m : String) (v : Int64) (c : ModelState)
    (h : st.setCounter n v = .ok c) : c.counter m = if m = n then some v else st.counter m := by
  unfold ModelState.setCounter at h
  cases h
  unfold ModelState.counter
  by_cases hany : st.counters.any (·.1 == n) = true
  · simp only [hany, if_true, find_map_set]
    by_cases hm : m = n <;> simp [hm]
  · simp only [hany, Bool.false_eq_true, if_false]
    rw [find_append_none _ _ _ _ (Bool.eq_false_iff.2 hany)]
    by_cases hm : m = n <;> simp [hm]

/-- A counter's integer value (absent: 0). -/
def ctr (st : ModelState) (n : String) : Int := ((st.counter n).getD 0).toInt

theorem toInt_add_one {n : Int64} (h0 : -2 ^ 63 ≤ n.toInt) (h : n.toInt < 2 ^ 63 - 1) :
    (n + 1).toInt = n.toInt + 1 := by
  rw [Int64.toInt_add]
  have : (1 : Int64).toInt = 1 := rfl
  rw [this, ← Int64.toInt_ofInt]
  · exact Int64.toInt_ofInt_of_le (by omega) (by omega)

end Tiramemsu.Engine
