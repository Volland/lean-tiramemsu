/-
The `xsd:double` parser: Rust's syntax gate, then the exact decimal value `±m · 10^q` rounded
to binary64 with round-to-nearest, ties-to-even, in `Nat` arithmetic. The exponent is clamped
before any power is formed, so memory grows with the input length only.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Double.Bits
import Tiramemsu.Codec.Text

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-- The syntax of an accepted `xsd:double` form. -/
inductive DoubleSyntax where
  /-- `INF`, `+INF`, `-INF` or `NaN`. -/
  | special (x : Double64)
  /-- `[±] int [. frac] [(e|E) [±] exp]`. -/
  | numeric (neg : Bool) (intDigits fracDigits : List Char) (expNeg : Bool) (expDigits : List Char)
  deriving Repr, DecidableEq, Inhabited

/-- The numeric gate of Rust's `parse_double`. -/
def scanNumeric (l : List Char) : Option DoubleSyntax :=
  let (neg, body) := splitSign l
  let mant := body.takeWhile fun c => c != 'e' && c != 'E'
  let expPart : Option (List Char) := match body.drop mant.length with
    | [] => none
    | _ :: e => some e
  let int := mant.takeWhile (· != '.')
  let frac := match mant.drop int.length with
    | '.' :: f => f
    | _ => []
  if int.isEmpty && frac.isEmpty then none
  else if !(int.all isDigitChar && frac.all isDigitChar) then none
  else match expPart with
    | none => some (.numeric neg int frac false [])
    | some e =>
      let (eneg, ed) := splitSign e
      if ed.isEmpty || !ed.all isDigitChar then none
      else some (.numeric neg int frac eneg ed)

/-- The syntax of an `xsd:double` form, or `none` if it is ill-typed. -/
def scanDouble (s : String) : Option DoubleSyntax :=
  if s == "INF" || s == "+INF" then some (.special Double64.posInf)
  else if s == "-INF" then some (.special Double64.negInf)
  else if s == "NaN" then some (.special Double64.canonNaN)
  else scanNumeric s.toList

/-- The decimal exponent of a numeric form: `±exp − |frac|`. -/
def DoubleSyntax.decExp (fracDigits : List Char) (expNeg : Bool) (expDigits : List Char) : Int :=
  let e : Int := Nat.ofDigitChars 10 expDigits 0
  (if expNeg then -e else e) - fracDigits.length

/-- `a / b` (both positive) rounded to binary64, ties to even. -/
def roundRatio (neg : Bool) (a b : Nat) : Double64 :=
  let t := floorLog2Ratio a b
  let E := max t (-1022) - 52
  let (num, den) := if 0 ≤ E then (a, b <<< E.toNat) else (a <<< (-E).toNat, b)
  let q := num / den
  let r := num % den
  let M := if 2 * r > den || (2 * r == den && q % 2 == 1) then q + 1 else q
  Double64.ofMantExp neg M E

/-- `±m · 10^q` rounded to binary64, ties to even. Values with `digits(m) + q > 310` are at
least `10^310` and overflow; values with `digits(m) + q < −324` are below `10^−324` and
underflow; neither forms a power. -/
def roundDec (neg : Bool) (m : Nat) (q : Int) : Double64 :=
  if m = 0 then Double64.zero neg
  else
    let n : Int := numDigits m
    if n + q > 310 then Double64.inf neg
    else if n + q < -324 then Double64.zero neg
    else if 0 ≤ q then roundRatio neg (m * 10 ^ q.toNat) 1
    else roundRatio neg m (10 ^ (-q).toNat)

/-- The binary64 value of a syntax. -/
def DoubleSyntax.value : DoubleSyntax → Double64
  | .special x => x
  | .numeric neg int frac eneg ed =>
    roundDec neg (Nat.ofDigitChars 10 (int ++ frac) 0) (DoubleSyntax.decExp frac eneg ed)

/-- Parses an `xsd:double` lexical form exactly as Rust's `parse_double` accepts and rounds it. -/
def parseDouble (s : String) : Option Double64 := (scanDouble s).map DoubleSyntax.value

end Tiramemsu.Codec
