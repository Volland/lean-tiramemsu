/-
Codec errors: the failures of encoding, decoding and allocation, with Rust's feature strings.
Verified module: imports only `Init`.
-/

namespace Tiramemsu.Codec

--# @lat: [[codec#Errors]]

/-- The kinds of id a counter allocates. -/
inductive IdKind where
  | node
  | bnode
  | stmt
  | tx
  | term
  deriving Repr, DecidableEq, Inhabited

/-- The upper-case name of an id kind, as in `IdSpaceExhausted { kind: STMT }`. -/
def IdKind.name : IdKind → String
  | .node => "NODE"
  | .bnode => "BNODE"
  | .stmt => "STMT"
  | .tx => "TX"
  | .term => "TERM"

/-- Every codec failure. -/
inductive CodecError where
  /-- A reserved feature of a later format: tag 15 (`SEALED (M6)`) or a non-zero origin. -/
  | unsupported (feature : String)
  /-- An id or term that no canonical value encodes to. -/
  | invalidTerm (reason : String)
  /-- A counter that has reached its bound. -/
  | idSpaceExhausted (kind : IdKind)
  deriving Repr, DecidableEq, Inhabited

instance : ToString CodecError where
  toString
    | .unsupported f => s!"unsupported: {f}"
    | .invalidTerm r => s!"invalid term: {r}"
    | .idSpaceExhausted k => s!"id space exhausted: {k.name}"

/-- The feature reported for the reserved tag 15. -/
def sealedFeature : String := "SEALED (M6)"

/-- The feature reported for an allocated id with a non-zero origin. -/
def originFeature (origin : Nat) : String := "origin " ++ toString origin

end Tiramemsu.Codec
