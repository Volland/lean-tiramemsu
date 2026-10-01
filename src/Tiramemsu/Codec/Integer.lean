/-
`xsd:integer` lexical forms: an optional sign and one or more ASCII digits. The canonical form
is the decimal of the value (no `+`, no leading zeros, `0` for every zero), so two forms
canonicalize to the same text exactly when they denote the same integer.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Text

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Numbers]]

/-- `[+-]digits` as an integer. -/
def parseIntChars (l : List Char) : Option Int :=
  let (neg, ds) := splitSign l
  (digitsVal? ds).map fun n => if neg then -(n : Int) else n

/-- The integer of an `xsd:integer` lexical form, or `none` if it is ill-typed. -/
def parseIntLex (s : String) : Option Int := parseIntChars s.toList

/-- The canonical decimal of an `xsd:integer` lexical form, or `none` if it is ill-typed. -/
def canonInteger (s : String) : Option String := (parseIntLex s).map intText

/-- An integer of the inline `INT` range `[−2^59, 2^59 − 1]`. -/
def inIntRange (i : Int) : Bool := intMin ≤ i && i ≤ intMax

end Tiramemsu.Codec
