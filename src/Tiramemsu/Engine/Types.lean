/-
Engine types: retraction kinds, valid intervals, patches, assert results and options,
transaction options and reports, events, and the engine error with Rust's variant names.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Encode
import Tiramemsu.Store.Types

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store

--# @lat: [[engine#Types]]

/-- Why a statement was retracted (stored as `ret_kind` 0–3). -/
inductive RetKind where
  | explicit
  | cascade
  | supersede
  | cardinality
  deriving Repr, DecidableEq, Inhabited

namespace RetKind

def code : RetKind → Int64
  | .explicit => 0 | .cascade => 1 | .supersede => 2 | .cardinality => 3

def ofCode? (c : Int64) : Option RetKind :=
  if c == 0 then some .explicit else if c == 1 then some .cascade
  else if c == 2 then some .supersede else if c == 3 then some .cardinality else none

def name : RetKind → String
  | .explicit => "explicit" | .cascade => "cascade" | .supersede => "supersede"
  | .cardinality => "cardinality"

/-- The order used when two retractions are compared (merge laws): by code. -/
def toNat : RetKind → Nat
  | .explicit => 0 | .cascade => 1 | .supersede => 2 | .cardinality => 3

end RetKind

/-- A retraction: the transaction number and the kind. -/
structure Retraction where
  t : Int64
  kind : RetKind
  deriving Repr, DecidableEq, Inhabited

/-- A half-open valid-time interval `[vFrom, vTo)` in epoch ms; `none` is unbounded. -/
structure Valid where
  vFrom : Option Int64 := none
  vTo : Option Int64 := none
  deriving Repr, DecidableEq, Inhabited

/-- What assert does when a live overlapping match exists. -/
inductive OnExisting where
  | return_
  | confirm
  deriving Repr, DecidableEq, Inhabited

/-- Options of an assert. -/
structure AssertOpts where
  valid : Valid := {}
  onExisting : OnExisting := .return_
  deriving Repr, DecidableEq, Inhabited

/-- The result of an assert. -/
inductive Asserted where
  | new (e : ObjectId)
  | existing (e : ObjectId)
  deriving Repr, DecidableEq, Inhabited

def Asserted.eid : Asserted → ObjectId
  | .new e | .existing e => e

def Asserted.isNew : Asserted → Bool
  | .new _ => true
  | .existing _ => false

/-- A supersede patch: only the object and the valid bounds can change. `vFrom`/`vTo`:
`none` keeps the bound, `some none` clears it, `some (some x)` sets it. A patch has no subject
or predicate field, so patching them is unrepresentable. -/
structure Patch where
  o : Option Value := none
  vFrom : Option (Option Int64) := none
  vTo : Option (Option Int64) := none
  deriving Repr, Inhabited

/-- Options of a transaction. -/
structure TxOptions where
  dryRun : Bool := false
  maxCascade : Nat := 10000
  deriving Repr, DecidableEq, Inhabited

/-- What a committed (or dry-run) transaction did. Eids are `STMT` ids. -/
structure TxReport where
  t : Int64 := 0
  instant : Int64 := 0
  asserted : Array ObjectId := #[]
  existing : Array ObjectId := #[]
  retracted : Array (ObjectId × RetKind) := #[]
  superseded : Array (ObjectId × ObjectId) := #[]
  memberships : Array ObjectId := #[]
  membershipsRetracted : Array (ObjectId × RetKind) := #[]
  deriving Repr, DecidableEq, Inhabited

/-- The operation of an event. -/
inductive EventOp where
  | assert
  | retract
  deriving Repr, DecidableEq, Inhabited

/-- One entry of the event log. -/
structure Event where
  t : Int64
  eid : ObjectId
  op : EventOp
  kind : Option RetKind
  deriving Repr, DecidableEq, Inhabited

/-- Where a value was used. -/
inductive Position where
  | subject
  | predicate
  | object
  | key
  | value
  deriving Repr, DecidableEq, Inhabited

/-- Every engine failure; the names are Rust's `Error` variants. -/
inductive Error where
  | uniqueViolation (p o existing : ObjectId)
  | valueTypeMismatch (p expected : ObjectId) (got : Tag)
  | subjectTypeMismatch (p : ObjectId) (expected : List ObjectId) (got : Tag)
  | cascadeLimitExceeded (root : ObjectId) (limit : Nat)
  | notLive (e : ObjectId)
  | invalidPatch (msg : String)
  | selfReference (e : ObjectId)
  | reservedNamespace (iri : String)
  | invalidGraphName (term : String)
  | schemaConflict (violating : List ObjectId)
  | unsupported (feature : String)
  | invalidTerm (pos : Position) (reason : String)
  | invalidInterval (vFrom vTo : Int64)
  | notUniquePredicate (p : ObjectId)
  | idSpaceExhausted (kind : IdKind)
  | invalidArgument (msg : String)
  | store (e : StoreError)
  | custom (msg : String)
  deriving Repr, DecidableEq, Inhabited

namespace Error

/-- Rust's error code (the variant name). -/
def code : Error → String
  | .uniqueViolation .. => "UniqueViolation"
  | .valueTypeMismatch .. => "ValueTypeMismatch"
  | .subjectTypeMismatch .. => "SubjectTypeMismatch"
  | .cascadeLimitExceeded .. => "CascadeLimitExceeded"
  | .notLive _ => "NotLive"
  | .invalidPatch _ => "InvalidPatch"
  | .selfReference _ => "SelfReference"
  | .reservedNamespace _ => "ReservedNamespace"
  | .invalidGraphName _ => "InvalidGraphName"
  | .schemaConflict _ => "SchemaConflict"
  | .unsupported _ => "Unsupported"
  | .invalidTerm .. => "InvalidTerm"
  | .invalidInterval .. => "InvalidInterval"
  | .notUniquePredicate _ => "NotUniquePredicate"
  | .idSpaceExhausted _ => "IdSpaceExhausted"
  | .invalidArgument _ => "InvalidArgument"
  | .store _ => "Sqlite"
  | .custom _ => "Custom"

/-- A codec failure in a position. -/
def ofCodec (pos : Position) : CodecError → Error
  | .unsupported f => .unsupported f
  | .invalidTerm r => .invalidTerm pos r
  | .idSpaceExhausted k => .idSpaceExhausted k

end Error

instance : ToString Error where
  toString e := match e with
    | .uniqueViolation p o x => s!"unique violation on {p.raw}: value {o.raw} is already held by {x.raw}"
    | .valueTypeMismatch p x g => s!"value type mismatch on {p.raw}: expected {x.raw}, got {g.name}"
    | .subjectTypeMismatch p _ g => s!"subject type mismatch on {p.raw}: got {g.name}"
    | .cascadeLimitExceeded r l => s!"cascade from {r.raw} exceeds the limit of {l} statements"
    | .notLive x => s!"statement {x.raw} is not live"
    | .invalidPatch m => s!"invalid patch: {m}"
    | .selfReference x => s!"statement {x.raw} would reference itself"
    | .reservedNamespace i => s!"reserved namespace: {i}"
    | .invalidGraphName t => s!"invalid graph name: {t}"
    | .schemaConflict v => s!"schema change conflicts with live statements {v.map (·.raw)}"
    | .unsupported f => s!"unsupported: {f}"
    | .invalidTerm p r => s!"invalid term in {reprStr p} position: {r}"
    | .invalidInterval a b => s!"invalid valid-time interval [{a}, {b})"
    | .notUniquePredicate p => s!"predicate {p.raw} is not unique"
    | .idSpaceExhausted k => s!"id space exhausted for {k.name}: counters stop at 2^48 - 1"
    | .invalidArgument m => m
    | .store e => s!"sqlite: {e}"
    | .custom m => m

end Tiramemsu.Engine
