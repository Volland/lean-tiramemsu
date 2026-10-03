/-
The evaluator theorem on reachable states: the store half of the id bridge (`IdBridge.wf`,
unique statement ids) is derived from the M2 invariant for every state reachable from the
initial store by transactions; the dictionary half (`TermBridge`) remains a hypothesis.

Why the dictionary half is not derived: the M2 invariant (`Engine.WF`, kept by every body
operation through `TxInv`) constrains a stored statement only by the tags of its positions
(`RowOK`); that every position names a dictionary row of its tag, or a valid inline id, is
enforced by the engine's write pipeline (`checkPositions`), which a transaction body written
directly against the operations (`EngM`, as `transactE` accepts) can bypass, so `decodes` is
not an invariant of every reachable state. The term table is likewise not tracked by M2 (only
its prefix growth, `Extends.terms`), so the dictionary laws of M1 (`Dict.WF` on reachable
dictionaries) do not transfer to `ModelState.terms` without a new invariant over every
operation and the transaction lifecycle. `complete`, `sound` and `idInj` additionally need the
codec's encode-after-decode law on inline ids, which M1 does not state.
-/
import TiramemsuProofs.Query.EvalDenoteTop
import TiramemsuProofs.Store.Lifecycle
import Tiramemsu.Storage.Meta

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics#Reachable States]]

/-- The initial store: no statements, terms or transactions; the format-1 counters. -/
def initState : ModelState := { counters := Storage.initialMeta.toList }

/-- States reachable from the initial store by transactions: any engine body, clock reading
and options (the verb programs `Model.transact` runs are such bodies). -/
inductive Reachable : ModelState → Prop
  | init : Reachable initState
  | step {α : Type} (now : Int) (opts : TxOptions) (body : EngM α) {st : ModelState} :
      Reachable st → Reachable (Model.transactE now opts body st).2

theorem Reachable.transact {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) {st : ModelState}
    (h : Reachable st) : Reachable (Model.transact now opts prog st).2 :=
  Reachable.step now opts prog.run h

theorem wf_init : Engine.WF initState := by
  refine ⟨List.Pairwise.nil, fun r h => (by cases h), ?_, ?_, ?_, ?_, List.Pairwise.nil, fun r h => (by cases h)⟩
  · simp [lastT, ctr, initState, ModelState.counter, Storage.initialMeta]
  · simp [lastT, ctr, initState, ModelState.counter, Storage.initialMeta, counterMax]
  · simp [nextStmt, ctr, initState, ModelState.counter, Storage.initialMeta]
  · simp [lastT, ctr, initState, ModelState.counter, Storage.initialMeta]

/-- Every reachable state is well-formed (M2 "never forget"). -/
theorem reachable_wf {st : ModelState} (h : Reachable st) : Engine.WF st := by
  induction h with
  | init => exact wf_init
  | step now opts body _ ih => exact (transactE_wf_extends now opts body _ ih).1

/-- The dictionary half of the id bridge: every statement id decodes, lookups are complete and
sound on stored ids, and a stored id is the only id decoding to its value. -/
structure TermBridge (st : ModelState) : Prop where
  decodes : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∃ v, decodeId st x = .ok v
  complete : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∀ v, decodeId st x = .ok v → lookupId st v = some x
  sound : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∀ v, lookupId st v = some x → decodeId st x = .ok v.canonical
  idInj : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∀ y v, decodeId st y = .ok v → decodeId st x = .ok v → y = x

/-- The id bridge of a reachable state, given its dictionary half. -/
theorem idBridge_of_reachable {st : ModelState} (h : Reachable st) (ht : TermBridge st) : IdBridge st :=
  ⟨(reachable_wf h).uniq, ht.decodes, ht.complete, ht.sound, ht.idInj⟩

/-- query-semantics "Reference semantics" on reachable states: for every state reachable from
the initial store by transactions whose dictionary half of the id bridge holds, the evaluator
returns a permutation of the reference bag (exactly it under a root `OrderLimit`). -/
theorem eval_eq_denote_reachable (opts : Path.PathOpts) {st : ModelState} (h : Reachable st)
    (ht : TermBridge st) (ps : Params) (q : Query) (counts : Value → Option Nat)
    (hok : ∀ p, prepare ps q = .ok p → OpOk p.iso p.vars p.root)
    {b : Bag} (hd : Query.denote opts st ps q = .ok b) :
    ∃ p b', prepare ps q = .ok p ∧ ev st (Query.eval opts ps q counts) = .ok (.ok (p, b')) ∧ b'.Perm b ∧
      (∀ keys s l x, p.root = .orderLimit keys s l x → b' = b) :=
  eval_eq_denote opts (idBridge_of_reachable h ht) ps q counts hok hd

end Tiramemsu.Exec
