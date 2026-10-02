/-
Evaluator programs run on the model store, and the id bridge between them and the reference
semantics: dictionary decode and lookup through read programs equal the snapshot reads, views
resolve alike, and `IdBridge` states the M1 encode/decode bijection on the ids of a state's
statements (every statement id decodes, lookups are complete and sound on stored ids,
statement ids are unique) — the hypothesis under which the evaluator equals `denote`.
-/
import Tiramemsu.Exec.Eval
import TiramemsuProofs.Store.Reads
import TiramemsuProofs.Query.Scan
import TiramemsuProofs.Store.Temporal

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem

--# @lat: [[verification#Proven Query Semantics]]

/-- An evaluator program run on a model state. -/
def ev {α : Type} (st : ModelState) (x : EvM α) : Except StoreError (Except QError α) :=
  RProg.onModel st x.run

theorem onModel_bind {α β : Type} (st : ModelState) (p : RProg α) (f : α → RProg β) :
    RProg.onModel st (p >>= f) = (RProg.onModel st p) >>= fun a => RProg.onModel st (f a) :=
  RProg.runPure_bind _ _ p f

@[simp] theorem onModel_pure {α : Type} (st : ModelState) (a : α) : RProg.onModel st (pure a) = .ok a := rfl

@[simp] theorem onModel_rowById (st : ModelState) (i : Nat) :
    RProg.onModel st (Term.TermReader.rowById (m := RProg) i) = .ok (Term.modelRowById st i) := rfl

@[simp] theorem onModel_lookupKey (st : ModelState) (k : Term.TermKey) :
    RProg.onModel st (Term.TermReader.lookupKey (m := RProg) k) = .ok (Term.modelLookupKey st k) := rfl

theorem snap_rowById_bind {β : Type} (st : ModelState) (i : Nat) (f : Option Term.Row → SnapM β) :
    (Term.TermReader.rowById (m := SnapM) i >>= f) st = f (Term.modelRowById st i) st := rfl

theorem snap_lookupKey_bind {β : Type} (st : ModelState) (k : Term.TermKey) (f : Option Nat → SnapM β) :
    (Term.TermReader.lookupKey (m := SnapM) k >>= f) st = f (Term.modelLookupKey st k) st := rfl

theorem decode_onModel (st : ModelState) (x : ObjectId) :
    (Term.decode (m := RProg) x).onModel st = (Term.decode (m := SnapM) x) st := by
  unfold Term.decode
  cases hd : decodeInline x with
  | error e => rfl
  | ok o =>
    cases o with
    | some v => rfl
    | none =>
      cases ht : x.tag with
      | error e => rfl
      | ok t =>
        simp only [onModel_bind, onModel_rowById, snap_rowById_bind]
        cases hr : Term.modelRowById st x.upayload.toNat with
        | none => rfl
        | some r =>
          simp only [bind, Except.bind]
          by_cases htg : (r.tag != t) = true
          · simp only [htg, ite_true]; rfl
          · simp only [htg]
            cases hdt : r.dt with
            | none => rfl
            | some raw =>
              by_cases hb : ((ObjectId.mk raw).tagBits == Tag.iri.toUInt64) = true
              · simp only [hb, ite_true]
                show RProg.runPure _ _ (RProg.bind _ _) = _
                rw [RProg.runPure_rbind]
                show _ = (Term.TermReader.rowById (m := SnapM) _ >>= _) st
                rw [snap_rowById_bind]
                have e : RProg.runPure ROp.model st (Term.TermReader.rowById (m := RProg)
                    (ObjectId.upayload ⟨raw⟩).toNat) = .ok (Term.modelRowById st (ObjectId.upayload ⟨raw⟩).toNat) := rfl
                rw [e]
                cases Term.modelRowById st (ObjectId.upayload ⟨raw⟩).toNat <;> rfl
              · simp only [hb]; rfl

theorem lookupValue_onModel (st : ModelState) (v : Value) :
    (Term.lookupValue (m := RProg) v).onModel st = (Term.lookupValue (m := SnapM) v) st := by
  unfold Term.lookupValue
  cases he : encode v with
  | error e => rfl
  | ok enc =>
    cases enc with
    | inline x => rfl
    | term t =>
      simp only
      cases hdt : t.datatype with
      | none =>
        simp only [bind]
        rfl
      | some iri =>
        show RProg.runPure _ _ (RProg.bind _ _) = (Term.TermReader.lookupKey (m := SnapM) _ >>= _) st
        rw [RProg.runPure_rbind, snap_lookupKey_bind]
        have e : RProg.runPure ROp.model st (Term.TermReader.lookupKey (m := RProg) ⟨.iri, iri, none, none⟩) =
            .ok (Term.modelLookupKey st ⟨.iri, iri, none, none⟩) := rfl
        rw [e]
        cases Term.modelLookupKey st ⟨.iri, iri, none, none⟩ with
        | none => rfl
        | some j => rfl

/-- The id of a value by dictionary lookup on a model state (`none`: not stored). -/
def lookupId (st : ModelState) (v : Value) : Option Int64 :=
  match (Term.lookupValue (m := SnapM) v) st with
  | .ok (.ok o) => o.map (·.raw)
  | _ => none

theorem lookupValue_snap_ok (st : ModelState) (v : Value) :
    ∃ r, (Term.lookupValue (m := SnapM) v) st = .ok r := by
  unfold Term.lookupValue
  cases he : encode v with
  | error e => exact ⟨_, rfl⟩
  | ok enc =>
    cases enc with
    | inline x => exact ⟨_, rfl⟩
    | term t =>
      simp only
      cases hdt : t.datatype with
      | none => exact ⟨_, rfl⟩
      | some iri =>
        show ∃ r, (Term.TermReader.lookupKey (m := SnapM) _ >>= _) st = _
        rw [snap_lookupKey_bind]
        cases Term.modelLookupKey st ⟨.iri, iri, none, none⟩ with
        | none => exact ⟨_, rfl⟩
        | some j => exact ⟨_, rfl⟩

/-! ## Evaluator programs on the model -/

section
variable {α β : Type} (st : ModelState)

@[simp] theorem ev_pure (a : α) : ev st (pure a : EvM α) = .ok (.ok a) := rfl

theorem ev_bind (x : EvM α) (f : α → EvM β) :
    ev st (x >>= f) = match ev st x with
      | .ok (.ok a) => ev st (f a)
      | .ok (.error e) => .ok (.error e)
      | .error e => .error e := by
  unfold ev
  show RProg.onModel st (x.run >>= ExceptT.bindCont f) = _
  rw [onModel_bind]
  cases RProg.onModel st x.run with
  | error e => rfl
  | ok r => cases r <;> rfl

theorem ev_bind_ok {x : EvM α} {a : α} (h : ev st x = .ok (.ok a)) (f : α → EvM β) :
    ev st (x >>= f) = ev st (f a) := by
  rw [ev_bind, h]

@[simp] theorem ev_liftR (p : RProg α) : ev st (liftR p) = (p.onModel st).map .ok := by
  unfold ev liftR
  show RProg.onModel st (Except.ok <$> p) = _
  show RProg.onModel st (p >>= fun a => pure (Except.ok a)) = _
  rw [onModel_bind]
  cases RProg.onModel st p <;> rfl

@[simp] theorem ev_throw (e : QError) : ev st (throw e : EvM α) = .ok (.error e) := rfl

theorem ev_lookupE (v : Value) : ev st (lookupE v) = .ok (.ok (lookupId st v)) := by
  unfold lookupE
  rw [ev_bind, ev_liftR, lookupValue_onModel]
  obtain ⟨r, hr⟩ := lookupValue_snap_ok st v
  rw [hr]
  unfold lookupId
  rw [hr]
  cases r <;> rfl

theorem ev_decodeE {x : Int64} {v : Value} (h : decodeId st x = .ok v) : ev st (decodeE x) = .ok (.ok v) := by
  unfold decodeE
  rw [ev_bind, ev_liftR, decode_onModel]
  unfold decodeId at h
  split at h
  · next w hw => rw [hw]; cases h; rfl
  · cases h
  · cases h

/-- A list map whose every step succeeds. -/
theorem ev_mapM {f : α → EvM β} {g : α → β} :
    ∀ (xs : List α), (∀ x ∈ xs, ev st (f x) = .ok (.ok (g x))) → ev st (xs.mapM f) = .ok (.ok (xs.map g))
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, ev_bind, h x (List.mem_cons_self ..)]
    simp only
    rw [ev_bind, ev_mapM xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem ev_resolveViewE (v : View.ViewSpec) : ev st (resolveViewE v) = .ok (.ok (resolveView st v)) := by
  unfold resolveViewE resolveView View.resolve
  rw [ev_liftR]
  rcases v with ⟨tx, valid⟩
  cases tx with
  | now => rfl
  | history => rfl
  | asOf a =>
    cases a with
    | tx t => rfl
    | instant ms =>
      show (RProg.onModel st (View.resolveInstant ms >>= _)).map _ = _
      rw [onModel_bind]
      unfold View.resolveInstant
      show (RProg.onModel st (RProg.lift (.txAtOrBefore ms) >>= _) >>= _).map _ = _
      rw [onModel_bind]
      show ((ROp.model (.txAtOrBefore ms) st >>= _) >>= _).map _ = _
      rw [ROp.model_txAtOrBefore]
      cases h : st.txAtOrBefore ms <;> simp [h] <;> rfl

theorem ev_rangeScan (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (h : pfx.length ≤ 3) :
    ev st (liftR (rangeScan ord v pfx)) = .ok (.ok (st.scanList (scanSpec ord v pfx))) := by
  rw [ev_liftR, rangeScan_model st ord v pfx h]; rfl

theorem ev_lookupEid (v : Store.View) (e : Int64) :
    ev st (liftR (lookupEid v e)) = .ok (.ok ((st.triple e).filter v.admits)) := by
  rw [ev_liftR]
  unfold lookupEid
  rw [onModel_bind]
  show ((ROp.model (.triple e) st) >>= _).map _ = _
  rw [ROp.model_triple]
  cases h : st.triple e with
  | none => rfl
  | some r => by_cases ha : v.admits r = true <;> simp [ha, Option.filter, bind, Except.bind] <;> rfl

end

/-! ## The id bridge -/

/-- The environment of the reference semantics for an evaluator environment: the model state
read by `denote` (the evaluator reads the store through its programs). -/
def _root_.Tiramemsu.Sem.Env.at (E : Env) (st : ModelState) : Env :=
  { E with st := st, predCount := fun _ => none }

@[simp] theorem _root_.Tiramemsu.Sem.Env.at_n (E : Env) (st : ModelState) : (E.at st).n = E.n := rfl
@[simp] theorem _root_.Tiramemsu.Sem.Env.at_st (E : Env) (st : ModelState) : (E.at st).st = st := rfl
@[simp] theorem _root_.Tiramemsu.Sem.Env.at_vars (E : Env) (st : ModelState) : (E.at st).vars = E.vars := rfl
@[simp] theorem _root_.Tiramemsu.Sem.Env.at_sem (E : Env) (st : ModelState) : (E.at st).sem = E.sem := rfl
@[simp] theorem _root_.Tiramemsu.Sem.Env.at_iso (E : Env) (st : ModelState) : (E.at st).iso = E.iso := rfl
@[simp] theorem _root_.Tiramemsu.Sem.Env.at_idx (E : Env) (st : ModelState) : (E.at st).idx = E.idx := rfl
@[simp] theorem _root_.Tiramemsu.Sem.Env.at_schemaOf (E : Env) (st : ModelState) : (E.at st).schemaOf = E.schemaOf := rfl
@[simp] theorem bindVal_at (E : Env) (st : ModelState) : bindVal (E.at st) = bindVal E := rfl

/-- The ids a statement carries. -/
def stmtIds (r : TripleRow) : List Int64 := [r.s, r.p, r.o, r.eid]

/-- The M1 encode/decode bijection on the ids of a state's statements, as the evaluator needs
it: every statement id decodes; a stored id is the dictionary lookup of its value (so a lookup
finds every statement whose position decodes to the value); a lookup that returns a stored id
returns the id of the value's canonical form; statement ids are unique; an id that decodes to the
value of a stored statement position is that position's id. -/
structure IdBridge (st : ModelState) : Prop where
  wf : st.WF
  decodes : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∃ v, decodeId st x = .ok v
  complete : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∀ v, decodeId st x = .ok v → lookupId st v = some x
  sound : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∀ v, lookupId st v = some x → decodeId st x = .ok v.canonical
  idInj : ∀ r ∈ st.triples, ∀ x ∈ stmtIds r, ∀ y v, decodeId st y = .ok v → decodeId st x = .ok v → y = x

end Tiramemsu.Exec
