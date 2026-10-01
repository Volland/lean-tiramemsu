/-
Views and the reads through them, as read programs (`RProg`): run on a snapshot reader, on the
writer inside a speculation, or on a model state.

- `ViewSpec`: a transaction-time selector (`now`, `asOf` a transaction or an instant,
  `history`) and a valid-time selector; deriving a view reads nothing.
- `triples`: lookup with optional positions, ascending eid, as-of rows masked; it never
  interns, so a constant that is not stored matches nothing (the caller looks it up).
- `values`, `dependents`, `eventsSince`, `graphMembers`, `graphs`, `resolveInstant`,
  `basisT`, as in Rust's `read.rs`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Walk
import Tiramemsu.Engine.Vocab
import Tiramemsu.Engine.Prog

namespace Tiramemsu.View

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term Tiramemsu.Engine

--# @lat: [[engine#Views]]

/-- A point in transaction time. -/
inductive TimeRef where
  | tx (t : Int64)
  | instant (ms : Int64)
  deriving Repr, DecidableEq, Inhabited

/-- Transaction-time selector. -/
inductive TxSpec where
  | now
  | asOf (r : TimeRef)
  | history
  deriving Repr, DecidableEq, Inhabited

/-- A view: transaction-time and valid-time selectors. -/
structure ViewSpec where
  tx : TxSpec := .now
  valid : ValidSel := .unfiltered
  deriving Repr, DecidableEq, Inhabited

def ViewSpec.now : ViewSpec := {}
def ViewSpec.asOfT (t : Int64) : ViewSpec := { tx := .asOf (.tx t) }
def ViewSpec.history : ViewSpec := { tx := .history }
def ViewSpec.validAt (v : ViewSpec) (d : Int64) : ViewSpec := { v with valid := .at d }

/-! ## Reads -/

def scan (sp : ScanSpec) : RProg (Array TripleRow) := RProg.lift (.scan sp)

/-- The last committed transaction of the snapshot (`meta.last_t`). -/
def basisT : RProg Int64 := do
  return ((← RProg.lift (.counter "last_t")).getD 0)

/-- The largest committed `t` whose instant is at or before `ms`, or 0. -/
def resolveInstant (ms : Int64) : RProg Int64 := do
  match ← RProg.lift (.txAtOrBefore ms) with
  | some r => pure r.t
  | none => pure 0

/-- The store view of a view spec (an instant resolves within the snapshot). -/
def resolve (v : ViewSpec) : RProg View := do
  match v.tx with
  | .now => pure { tx := .now, valid := v.valid }
  | .history => pure { tx := .history, valid := v.valid }
  | .asOf (.tx t) => pure { tx := .asOf t, valid := v.valid }
  | .asOf (.instant ms) => do
    let t ← resolveInstant ms
    pure { tx := .asOf t, valid := v.valid }

/-- Ascending eid order. -/
def byEid (xs : List TripleRow) : List TripleRow :=
  xs.mergeSort fun a b => decide (a.eid.toInt ≤ b.eid.toInt)

/-- As-of rows report no retraction. -/
def mask (v : View) (r : TripleRow) : TripleRow :=
  match v.tx with
  | .asOf _ => { r with tRet := none, retKind := none }
  | _ => r

/-- The scan that serves a lookup with bound positions. -/
def lookupScan (v : View) (s p o : Option ObjectId) : ScanSpec :=
  let live := v.tx == .now
  let fam (l h : Family) := if live then l else h
  match s, p, o with
  | some s, some p, some o => { family := fam .liveSpo .histSpo, pre := #[s.raw, p.raw, o.raw], view := v }
  | some s, some p, none => { family := fam .liveSpo .histSpo, pre := #[s.raw, p.raw], view := v }
  | some s, none, some o => { family := fam .liveOsp .histOsp, pre := #[o.raw, s.raw], view := v }
  | some s, none, none => { family := fam .liveSpo .histSpo, pre := #[s.raw], view := v }
  | none, some p, some o => { family := fam .livePos .histPos, pre := #[p.raw, o.raw], view := v }
  | none, some p, none => { family := fam .livePos .histPos, pre := #[p.raw], view := v }
  | none, none, some o => { family := fam .liveOsp .histOsp, pre := #[o.raw], view := v }
  | none, none, none => { family := fam .liveSpo .histSpo, view := v }

/-- The statements of a resolved view matching the bound positions, ascending eid. -/
def triplesIn (v : View) (s p o : Option ObjectId) : RProg (List TripleRow) := do
  let rows ← scan (lookupScan v s p o)
  pure ((byEid rows.toList).map (mask v))

/-- Every statement selected by the view that matches the bound positions, ascending eid;
as-of rows report `t_ret` and `ret_kind` as absent. -/
def triples (v : ViewSpec) (s p o : Option ObjectId) : RProg (List TripleRow) := do
  triplesIn (← resolve v) s p o

/-- The values of `(s, key)`: objects of the selected statements, or, only under now and only
when there is none, the volatile value. -/
def values (v : ViewSpec) (s key : ObjectId) : RProg (List ObjectId) := do
  let objs := (← triples v (some s) (some key) none).map fun r => (⟨r.o⟩ : ObjectId)
  if !objs.isEmpty || v.tx != .now then return objs
  match ← RProg.lift (.volatileGet s.raw key.raw) with
  | some r => pure [⟨r.value⟩]
  | none => pure []

/-- Whether a statement is selected by a resolved view. -/
def visible (v : View) (e : Int64) : RProg Bool := do
  match ← RProg.lift (.triple e) with
  | some r => pure (v.admits r)
  | none => pure false

/-- What stands on `root` in the view: `root` first, then breadth-first every selected
statement whose subject or object was reached; empty when `root` is not selected. Never
truncated. -/
def dependentsIn (v : View) (root : Int64) : RProg (List Int64) := do
  if !(← visible v root) then return []
  let fuel ← walkFuel
  match ← walk (neighbors v) none root fuel with
  | .done order => pure order.toList
  | _ => pure []

def dependents (v : ViewSpec) (root : ObjectId) : RProg (List ObjectId) := do
  let xs ← dependentsIn (← resolve v) root.raw
  pure (xs.map (⟨·⟩))

/-- The log order: time, asserts before retracts, then eid. -/
def eventLe (a b : Event) : Bool :=
  if a.t.toInt != b.t.toInt then decide (a.t.toInt < b.t.toInt)
  else if a.op != b.op then a.op == .assert
  else decide (a.eid.raw.toInt ≤ b.eid.raw.toInt)

/-- The events of a row list: one assert per row, one retract per retracted row. -/
def eventsOf (rows : List TripleRow) : List Event :=
  rows.flatMap fun r =>
    { t := r.tAdd, eid := ⟨r.eid⟩, op := .assert, kind := none } ::
    (match r.tRet with
     | some t => [{ t, eid := ⟨r.eid⟩, op := .retract, kind := r.retKind.bind RetKind.ofCode? }]
     | none => [])

/-- Every event with time `> since`, ordered by time, asserts before retracts, then eid. -/
def eventsSince (since : Int64) : RProg (List Event) := do
  let added ← scan { family := .logAdd, lo := some (.excl since), view := { tx := .history } }
  let retracted ← scan { family := .logRet, lo := some (.excl since), view := { tx := .history } }
  let asserts := added.toList.map fun r => ({ t := r.tAdd, eid := ⟨r.eid⟩, op := .assert, kind := none } : Event)
  let retracts := retracted.toList.filterMap fun r => r.tRet.map fun t =>
    ({ t, eid := ⟨r.eid⟩, op := .retract, kind := r.retKind.bind RetKind.ofCode? } : Event)
  pure ((asserts ++ retracts).mergeSort eventLe)

/-- The id of an IRI without interning it. -/
def iriId (iri : String) : RProg (Option ObjectId) := do
  return (← RProg.lift (.lookupKey ⟨.iri, iri, none, none⟩)).map (termId .iri)

/-- The members of `g`: statements visible in the view with a visible membership in `g`. -/
def graphMembersIn (v : View) (g : ObjectId) : RProg (List Int64) := do
  match ← iriId Vocab.sysInGraph with
  | none => pure []
  | some ig =>
    let ms ← scan { family := if v.tx == .now then .livePos else .histPos, pre := #[ig.raw, g.raw], view := v }
    let mut out := []
    for m in ms do
      if ← visible v m.s then out := m.s :: out
    pure (sortDedup out)

def graphMembers (v : ViewSpec) (g : ObjectId) : RProg (List ObjectId) := do
  let xs ← graphMembersIn (← resolve v) g
  pure (xs.map (⟨·⟩))

/-- The graphs: those with a visible membership of a visible statement, and those declared. -/
def graphsIn (v : View) : RProg (List Int64) := do
  let fam := if v.tx == .now then Family.livePos else .histPos
  let mut out := []
  if let some ig ← iriId Vocab.sysInGraph then
    for m in ← scan { family := fam, pre := #[ig.raw], view := v } do
      if ← visible v m.s then out := m.o :: out
  if let some ty ← iriId Vocab.rdfType then
    if let some sg ← iriId Vocab.sysGraph then
      for d in ← scan { family := fam, pre := #[ty.raw, sg.raw], view := v } do
        out := d.s :: out
  pure (sortDedup out)

def graphs (v : ViewSpec) : RProg (List ObjectId) := do
  let xs ← graphsIn (← resolve v)
  pure (xs.map (⟨·⟩))

end Tiramemsu.View
