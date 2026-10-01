/-
The predicate schema (Rust's `engine/schema.rs`): the flags in force for a predicate at the
current point of the transaction, value-type and subject-type checks, flag validation, and
the checks that reject schema changes live data already violates.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Base

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Predicate Schema]]

namespace EngM

/-- `true` as an ObjectId. -/
def trueId : ObjectId := ObjectId.ofPayload .bool 1

/-- The tags a subject can have, and so the tags `sys:subjectType` may name. -/
def subjectTags : List Tag := [.iri, .node, .bnode, .stmt, .tx]

/-- The inline tags a datatype IRI matches (besides `TYPED` terms with that datatype). -/
def datatypeTags (iri : String) : List Tag :=
  if iri == xsdInteger then [.int]
  else if iri == xsdString then [.shortStr, .str]
  else if iri == rdfLangString then [.langStr]
  else if iri == xsdBoolean then [.bool]
  else if iri == xsdDate then [.date]
  else if iri == xsdDateTime then [.dateTime]
  else if iri == xsdDouble then [.double]
  else if iri == xsdDecimal then [.decimal]
  else []

/-- Rows in ascending eid order. -/
def byEid (xs : Array TripleRow) : List TripleRow := View.byEid xs.toList

/-- Live rows with a subject. -/
def liveOfS (s : ObjectId) : EngM (Array TripleRow) :=
  rd (.scan { family := .liveSpo, pre := #[s.raw] })

/-- Live rows with a subject and a predicate. -/
def liveOfSP (s p : ObjectId) : EngM (Array TripleRow) :=
  rd (.scan { family := .liveSpo, pre := #[s.raw, p.raw] })

/-- Live rows with a predicate. -/
def liveOfP (p : ObjectId) : EngM (Array TripleRow) :=
  rd (.scan { family := .livePos, pre := #[p.raw] })

/-- The schema of `p` at the current point of this transaction. -/
def schema (p : ObjectId) : EngM PredicateSchema := do
  let ids ← [Vocab.sysCardinality, Vocab.sysUnique, Vocab.sysValueType, Vocab.sysIsEdge,
    Vocab.sysSubjectType].mapM sysLookup
  if ids.all Option.isNone then return {}
  let one ← sysLookup Vocab.sysOne
  let rows := byEid (← liveOfS p)
  let is (i : Nat) (r : TripleRow) : Bool := (ids[i]?.join).any (·.raw == r.p)
  let mut sc : PredicateSchema := {}
  for r in rows do
    let o : ObjectId := ⟨r.o⟩
    if is 0 r then sc := { sc with one := some o == one }
    else if is 1 r then sc := { sc with unique := o == trueId }
    else if is 2 r then sc := { sc with valueType := some o }
    else if is 3 r then sc := { sc with isEdge := some (o == trueId) }
    else if is 4 r then sc := { sc with subjectTypes := sc.subjectTypes ++ [o] }
  pure sc

/-- Whether `o` matches the value type `vt` (a tag IRI or a datatype IRI). -/
def matchesValueType (vt o : ObjectId) : EngM Bool := do
  match ← iriOf vt with
  | none => pure false
  | some iri =>
    let otag ← tagOf o
    match Vocab.tagOfIri iri with
    | some t => pure (otag == t)
    | none =>
      if (datatypeTags iri).contains otag then return true
      if otag == .typed then
        return (← rd (.rowById o.upayload.toNat)).any (·.dt == some vt.raw)
      pure false

/-- Checks `o` against the value type of `p`. -/
def checkValueType (p o : ObjectId) : EngM Unit := do
  if let some vt := (← schema p).valueType then
    if !(← matchesValueType vt o) then fail (.valueTypeMismatch p vt (← tagOf o))

/-- The tags named by `sys:subjectType` objects. -/
def tagsOf (types : List ObjectId) : EngM (List Tag) := do
  let mut out := []
  for t in types do
    if let some tag := (← iriOf t).bind Vocab.tagOfIri then out := out ++ [tag]
  pure out

/-- Checks the subject kind against the subject types of `p`. -/
def checkSubjectType (p s : ObjectId) : EngM Unit := do
  let types := (← schema p).subjectTypes
  if types.isEmpty then return
  let got ← tagOf s
  if (← tagsOf types).contains got then return
  fail (.subjectTypeMismatch p types got)

/-- Live `sys:subjectType` flag statements of predicate `x`, as `(eid, object)`, eid order. -/
def subjectTypeRows (x : ObjectId) : EngM (List (ObjectId × ObjectId)) := do
  match ← sysLookup Vocab.sysSubjectType with
  | none => pure []
  | some st => return (byEid (← liveOfSP x st)).map fun r => (⟨r.eid⟩, ⟨r.o⟩)

/-- Live statements of predicate `x` whose subject kind is outside `tags`, eid order. -/
def subjectTypeViolations (x : ObjectId) (tags : List Tag) : EngM (List ObjectId) := do
  let mut out := []
  for r in byEid (← liveOfP x) do
    if !tags.contains (← tagOf ⟨r.s⟩) then out := out ++ [⟨r.eid⟩]
  pure out

/-- Rejects retracting a `sys:subjectType` value when live data violates the remaining ones;
retracting the last value lifts the constraint. -/
def validateFlagRetraction (e : ObjectId) : EngM Unit := do
  let some st ← sysLookup Vocab.sysSubjectType | return
  let some row ← rd (.triple e.raw) | return
  if row.p != st.raw || row.tRet.isSome then return
  let x : ObjectId := ⟨row.s⟩
  let rest := ((← subjectTypeRows x).filter (·.1 != e)).map (·.2)
  if rest.isEmpty then return
  let violating ← subjectTypeViolations x (← tagsOf rest)
  if !violating.isEmpty then fail (.schemaConflict violating)

/-- Built-in validation of a flag statement `(s flag o)`. -/
def validateFlag (f : Flag) (fp s o : ObjectId) : EngM Unit := do
  if (← tagOf s) != .iri then fail (.invalidTerm .subject "schema flags need an IRI subject")
  let sIri := (← iriOf s).getD ""
  if sIri.startsWith Vocab.sys then fail (.reservedNamespace sIri)
  let otag ← tagOf o
  let (ok, expected) ← match f with
    | .cardinality => do
      let iri ← iriOf o
      pure (iri == some Vocab.sysOne || iri == some Vocab.sysMany, Tag.iri)
    | .unique | .isEdge => pure (otag == .bool, Tag.bool)
    | .valueType => do
      let ok := match ← iriOf o with
        | some i => if i.startsWith Vocab.sys then (Vocab.tagOfIri i).isSome else true
        | none => false
      pure (ok, Tag.iri)
    | .subjectType => do
      let tag := (← iriOf o).bind Vocab.tagOfIri
      pure (tag.any subjectTags.contains, Tag.iri)
  if !ok then
    let exp ← sys (Vocab.tagIri expected)
    fail (.valueTypeMismatch fp exp otag)

/-- Ascending raw order without duplicates. -/
def sortIds (xs : List ObjectId) : List ObjectId :=
  (sortDedup (xs.map (·.raw))).map (⟨·⟩)

/-- Rejects a flag value that live data (including this transaction's writes) violates.
`replacing` is the flag statement a supersede retracts. -/
def validateSchemaChange (f : Flag) (x o : ObjectId) (replacing : Option ObjectId) : EngM Unit := do
  let violating : List ObjectId ← match f with
    | .cardinality => do
      if (← iriOf o) != some Vocab.sysOne then pure [] else
      let rows := (← liveOfP x).toList
      let mut out := []
      for a in rows do
        for b in rows do
          if b.s == a.s && b.o != a.o && Valid.overlaps ⟨a.vFrom, a.vTo⟩ ⟨b.vFrom, b.vTo⟩ then
            out := ⟨a.eid⟩ :: ⟨b.eid⟩ :: out
      pure out
    | .unique => do
      if o != trueId then pure [] else
      let rows := (← liveOfP x).toList
      pure <| (rows.filter fun a =>
        (rows.filter fun b => b.o == a.o).any fun b => b.s != a.s).map fun a => (⟨a.eid⟩ : ObjectId)
    | .valueType => do
      let mut out := []
      for r in (← liveOfP x).toList do
        if !(← matchesValueType o ⟨r.o⟩) then out := ⟨r.eid⟩ :: out
      pure out
    | .subjectType => do
      let types := ((← subjectTypeRows x).filter fun (e, _) => some e != replacing).map (·.2) ++ [o]
      subjectTypeViolations x (← tagsOf types)
    | .isEdge => pure []
  if !violating.isEmpty then fail (.schemaConflict (sortIds violating))

end EngM

end Tiramemsu.Engine
