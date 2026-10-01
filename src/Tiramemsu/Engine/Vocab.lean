/-
Engine IRIs (`sys:`, `tm:`, `rdf:`), the schema flags, the reserved-namespace rule for user
writes and tag IRIs, as in Rust's `vocab.rs` and `engine/reserved.rs`.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Engine.Types

namespace Tiramemsu.Engine

open Tiramemsu.Codec

--# @lat: [[engine#Reserved Namespaces]]

namespace Vocab

def sys : String := "urn:tiramemsu:sys:"
def tm : String := "urn:tiramemsu:tm:"
def v : String := "urn:tiramemsu:v:"

def sysCardinality : String := sys ++ "cardinality"
def sysUnique : String := sys ++ "unique"
def sysValueType : String := sys ++ "valueType"
def sysIsEdge : String := sys ++ "isEdge"
def sysSubjectType : String := sys ++ "subjectType"
def sysSensitive : String := sys ++ "sensitive"
def sensitiveFeature : String := "sys:sensitive (M6)"
def sysOne : String := sys ++ "one"
def sysMany : String := sys ++ "many"
def sysConfirmedBy : String := sys ++ "confirmedBy"
def sysSupersedes : String := sys ++ "supersedes"
def sysInGraph : String := sys ++ "inGraph"
def sysGraph : String := sys ++ "Graph"
def rdfType : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- `sys:` local names users may write as predicates with any subject. -/
def sysAllowed : List String :=
  ["cardinality", "unique", "valueType", "subjectType", "isEdge", "vocab", "prefix", "prefixName",
   "prefixIri"]

/-- `sys:` local names users may write only with a transaction subject. -/
def sysTxMetadata : List String := ["author", "source", "reason"]

/-- The tag IRI `sys:<TAG>`. -/
def tagIri (t : Tag) : String := sys ++ t.name

/-- The tag named by a tag IRI. -/
def tagOfIri (iri : String) : Option Tag :=
  if iri.startsWith sys then Tag.ofName? (iri.drop sys.length).toString else none

/-- An IRI in the default user vocabulary. -/
def vIri (local_ : String) : String := v ++ local_

end Vocab

/-- The schema flags. -/
inductive Flag where
  | cardinality
  | unique
  | valueType
  | subjectType
  | isEdge
  deriving Repr, DecidableEq, Inhabited

namespace Flag

def ofIri (iri : String) : Option Flag :=
  if iri == Vocab.sysCardinality then some .cardinality
  else if iri == Vocab.sysUnique then some .unique
  else if iri == Vocab.sysValueType then some .valueType
  else if iri == Vocab.sysSubjectType then some .subjectType
  else if iri == Vocab.sysIsEdge then some .isEdge
  else none

/-- One live value per predicate (implicit cardinality one); `sys:subjectType` accumulates. -/
def singleValued (f : Flag) : Bool := f != .subjectType

end Flag

/-- The tags a subject can have. -/
def _root_.Tiramemsu.Codec.Tag.isSubject : Tag → Bool
  | .iri | .node | .bnode | .stmt | .tx => true
  | _ => false

/-- Checks that a user write may use predicate `iri` with a subject of tag `s`
(`sys:sensitive` is `Unsupported` first, `sys:inGraph` and `tm:` are reserved). -/
def checkReserved (iri : String) (s : Tag) : Except Error Unit :=
  if iri == Vocab.sysSensitive then .error (.unsupported Vocab.sensitiveFeature)
  else if iri == Vocab.sysInGraph then .error (.reservedNamespace iri)
  else if iri.startsWith Vocab.tm then .error (.reservedNamespace iri)
  else if iri.startsWith Vocab.sys then
    let local_ := (iri.drop Vocab.sys.length).toString
    if Vocab.sysAllowed.contains local_ then .ok ()
    else if Vocab.sysTxMetadata.contains local_ && s == .tx then .ok ()
    else .error (.reservedNamespace iri)
  else .ok ()

end Tiramemsu.Engine
