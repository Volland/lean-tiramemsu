/-
query-semantics "Reference semantics" and path-evaluation (task 9.3): for every query, every
plan (any per-predicate statistics, hence any greedy join order) and every model state with the
id bridge, the evaluator with the path engine returns the reference bag whenever the reference
semantics returns one, and the reference list when the prepared root is an `OrderLimit`. Path
patterns are covered: the reference semantics of a path pattern is the path engine run on the
model state, so the evaluator's path semantics agrees with it by construction (`pathSim_engine`).
-/
import TiramemsuProofs.Query.EvalSim
import Tiramemsu.Path.Engine

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-- The path engine agrees with the reference path semantics, which runs the same engine on the
model state: path-evaluation needs no hypothesis for the evaluator theorem. -/
theorem pathSim_engine (opts : Path.PathOpts) (st : ModelState) (E : Env) :
    PathSim st E (Path.evalPath opts) (Path.denotePath opts) := by
  intro p a b h
  have he : Path.evalPath opts E p a = Path.evalPath opts (E.at st) p a := rfl
  unfold Path.denotePath at h
  refine ⟨b, ?_, List.Perm.refl _⟩
  unfold ev
  rw [he]
  have hst : (Path.evalPath opts (E.at st) p a).run.onModel (E.at st).st =
      RProg.onModel st (Path.evalPath opts (E.at st) p a).run := rfl
  rw [hst] at h
  revert h
  generalize RProg.onModel st (Path.evalPath opts (E.at st) p a).run = r
  intro h
  rcases r with e | (e | b')
  · cases h
  · cases e <;> cases h
  · cases h; rfl

section
variable {st : ModelState} (hB : IdBridge st) {E : Env} {pathE : PathE} {pb : PathSem} (hp : PathSim st E pathE pb)
include hB hp

/-- Under a root `OrderLimit` the evaluator returns the reference list itself. -/
theorem eval_orderLimit_eq (keys : List (Expr × Bool)) (s l : Option TermOrVar) (x : IR.Op)
    (hok : OpOk E.iso E.vars (.orderLimit keys s l x)) {b : Bag} (hd : denote (E.at st) pb (.orderLimit keys s l x) = .ok b) :
    ev st (eval E pathE (.orderLimit keys s l x)) = .ok (.ok b) := by
  obtain ⟨hk, hx⟩ := hok
  rw [denote.eq_11] at hd
  obtain ⟨u, hc, hd⟩ := bind_ok hd
  obtain ⟨ks', hk', hd⟩ := bind_ok hd
  obtain ⟨sk, hs, hd⟩ := bind_ok hd
  obtain ⟨lm, hl, hd⟩ := bind_ok hd
  obtain ⟨bx, hbx, hd⟩ := bind_ok hd
  cases hd
  obtain ⟨ks'', hk'', hkeq⟩ := resolveKeysX_sim hB hp keys hk ks' hk'
  obtain ⟨bx', hbx', hxp⟩ := eval_sim hB hp x hx bx hbx
  rw [eval.eq_11, hc, ev_bind_ok st (ev_liftEx_ok st u), ev_bind, hk'']
  simp only []
  rw [ev_bind, hs, ev_liftEx_ok]
  simp only []
  rw [ev_bind, hl, ev_liftEx_ok]
  simp only []
  rw [ev_bind, hbx']
  show Except.ok (Except.ok _) = _
  rw [orderLimitB_congr _ hkeq, orderLimitB_perm _ _ _ _ hxp]
  rfl

end

/-- query-semantics "Reference semantics": for every query, every plan (any statistics) and every
model state with the id bridge, whenever the reference semantics returns a bag the evaluator with
the path engine returns a permutation of it, and exactly it under a prepared root `OrderLimit`. -/
theorem eval_eq_denote (opts : Path.PathOpts) {st : ModelState} (hB : IdBridge st) (ps : Params) (q : Query)
    (counts : Value → Option Nat) (hok : ∀ p, prepare ps q = .ok p → OpOk p.iso p.vars p.root)
    {b : Bag} (hd : Query.denote opts st ps q = .ok b) :
    ∃ p b', prepare ps q = .ok p ∧ ev st (Query.eval opts ps q counts) = .ok (.ok (p, b')) ∧ b'.Perm b ∧
      (∀ keys s l x, p.root = .orderLimit keys s l x → b' = b) := by
  unfold Query.denote denoteWith at hd
  obtain ⟨p, hp, hd⟩ := bind_ok hd
  set E : Env := { p.env {} with predCount := counts }
  have hE : E.at st = p.env st := rfl
  rw [← hE] at hd
  have hok' : OpOk E.iso E.vars p.root := hok p hp
  obtain ⟨b', h1, h2⟩ := eval_sim hB (pathSim_engine opts st E) p.root hok' b hd
  refine ⟨p, b', hp, ?_, h2, ?_⟩
  · unfold Query.eval evalQueryWith
    rw [ev_bind, hp, ev_liftEx_ok]
    simp only []
    rw [ev_bind, h1]
    rfl
  · intro keys s l x hr
    rw [hr] at hd hok' h1
    have := eval_orderLimit_eq hB (pathSim_engine opts st E) keys s l x hok' hd
    rw [this] at h1
    cases h1; rfl

end Tiramemsu.Exec
