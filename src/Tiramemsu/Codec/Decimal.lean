/-
`xsd:decimal` lexical forms: an optional sign, integer digits, optionally `.` and fraction
digits, at least one digit, no exponent. The canonical form is computed from the value: no `+`,
no leading zeros in the integer part (`0` when empty), no trailing zeros in the fraction (`0`
when empty), always a `.`, and `0.0` for every zero.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Text

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Numbers]]

/-- A decimal lexical form as (negative, mantissa, scale): the value is `±m / 10^k`. -/
def scanDecimal (l : List Char) : Option (Bool × Nat × Nat) :=
  let (neg, body) := splitSign l
  let int := body.takeWhile (· != '.')
  let frac := match body.drop int.length with
    | '.' :: f => f
    | _ => []
  if int.isEmpty && frac.isEmpty then none
  else if !(int.all isDigitChar && frac.all isDigitChar) then none
  else some (neg, Nat.ofDigitChars 10 (int ++ frac) 0, frac.length)

/-- Strips trailing zeros of the fraction: divides `m` by 10 while `k > 0` and `m % 10 = 0`. -/
def stripZeros : Nat → Nat → Nat → Nat × Nat
  | 0, m, k => (m, k)
  | fuel + 1, m, k => if k > 0 && m % 10 == 0 then stripZeros fuel (m / 10) (k - 1) else (m, k)

/-- The normal form of a decimal: no trailing fraction zeros, no sign on zero. -/
def normDec (neg : Bool) (m k : Nat) : Bool × Nat × Nat :=
  let (m', k') := stripZeros k m k
  (neg && m' != 0, m', k')

/-- The text of a normal-form decimal. -/
def renderDec (neg : Bool) (m k : Nat) : String :=
  (if neg then "-" else "") ++ natText (m / 10 ^ k) ++ "." ++
    (if k = 0 then "0" else String.ofList (padLeft k '0' (natChars (m % 10 ^ k))))

/-- The canonical form of an `xsd:decimal` lexical form, or `none` if it is ill-typed. -/
def canonDecimal (s : String) : Option String :=
  (scanDecimal s.toList).map fun (n, m, k) =>
    let (n', m', k') := normDec n m k
    renderDec n' m' k'

end Tiramemsu.Codec
