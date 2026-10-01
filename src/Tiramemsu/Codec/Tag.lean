/-
ObjectId tags: the fifteen kinds of format 1. Tag 15 (`SEALED`) has no constructor, so no
well-typed value carries it; reading it is the error `Unsupported "SEALED (M6)"`.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Error

namespace Tiramemsu.Codec

--# @lat: [[codec#ObjectId Layout]]

/-- The kind of value an ObjectId holds (low 4 bits). -/
inductive Tag where
  | iri
  | node
  | bnode
  | stmt
  | tx
  | int
  | bool
  | dateTime
  | date
  | shortStr
  | str
  | langStr
  | typed
  | double
  | decimal
  deriving Repr, DecidableEq, Inhabited

namespace Tag

/-- The tag number (0–14). -/
def toNat : Tag → Nat
  | .iri => 0 | .node => 1 | .bnode => 2 | .stmt => 3 | .tx => 4 | .int => 5 | .bool => 6
  | .dateTime => 7 | .date => 8 | .shortStr => 9 | .str => 10 | .langStr => 11
  | .typed => 12 | .double => 13 | .decimal => 14

/-- The tag number as the low bits of a raw id. -/
def toUInt64 (t : Tag) : UInt64 := t.toNat.toUInt64

/-- The tag number as a signed 64-bit value. -/
def toInt64 (t : Tag) : Int64 := t.toNat.toInt64

/-- The tag with a number, if it is one of 0–14. -/
def ofNat? : Nat → Option Tag
  | 0 => some .iri | 1 => some .node | 2 => some .bnode | 3 => some .stmt | 4 => some .tx
  | 5 => some .int | 6 => some .bool | 7 => some .dateTime | 8 => some .date
  | 9 => some .shortStr | 10 => some .str | 11 => some .langStr | 12 => some .typed
  | 13 => some .double | 14 => some .decimal | _ => none

/-- Every tag, in numeric order. -/
def all : List Tag :=
  [.iri, .node, .bnode, .stmt, .tx, .int, .bool, .dateTime, .date, .shortStr, .str, .langStr,
   .typed, .double, .decimal]

/-- The tag of the low bits of a raw id. 15 is `SEALED`, reserved for a later format. -/
def ofBits (b : UInt64) : Except CodecError Tag :=
  match ofNat? b.toNat with
  | some t => .ok t
  | none =>
    if b.toNat = 15 then .error (.unsupported sealedFeature)
    else .error (.invalidTerm s!"tag {b.toNat} out of range")

/-- The upper-case name used wherever a tag is named (tag IRIs, errors). -/
def name : Tag → String
  | .iri => "IRI" | .node => "NODE" | .bnode => "BNODE" | .stmt => "STMT" | .tx => "TX"
  | .int => "INT" | .bool => "BOOL" | .dateTime => "DATETIME" | .date => "DATE"
  | .shortStr => "SHORT_STR" | .str => "STR" | .langStr => "LANG_STR" | .typed => "TYPED"
  | .double => "DOUBLE" | .decimal => "DECIMAL"

/-- Inverse of `name`. -/
def ofName? (s : String) : Option Tag := all.find? (·.name == s)

/-- The payload is a term-dictionary id. -/
def isDictionary : Tag → Bool
  | .iri | .str | .langStr | .typed | .double | .decimal => true
  | _ => false

/-- The payload is read with an arithmetic shift (`INT`, `DATE`, `DATETIME`). -/
def isSigned : Tag → Bool
  | .int | .date | .dateTime => true
  | _ => false

/-- The payload is `origin << 48 | counter` (`NODE`, `BNODE`, `STMT`, `TX`). -/
def isAllocated : Tag → Bool
  | .node | .bnode | .stmt | .tx => true
  | _ => false

end Tag

end Tiramemsu.Codec
