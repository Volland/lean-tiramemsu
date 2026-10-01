/-
Character-level helpers shared by the literal parsers and printers: ASCII digits, signs,
decimal rendering and zero padding. Verified module: imports only `Init`.
-/

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals]]

/-- Smallest and largest `INT` / `DATE` payload values: `−2^59` and `2^59 − 1`. -/
abbrev intMin : Int := -(2 ^ 59)
abbrev intMax : Int := 2 ^ 59 - 1

/-- An ASCII digit `0`–`9`. -/
abbrev isDigitChar (c : Char) : Bool := c.isDigit

/-- The value of a non-empty list of ASCII digits. -/
def digitsVal? (l : List Char) : Option Nat :=
  if !l.isEmpty && l.all isDigitChar then some (Nat.ofDigitChars 10 l 0) else none

/-- Splits one leading `-` or `+`: `(negative, rest)`. -/
def splitSign : List Char → Bool × List Char
  | '-' :: r => (true, r)
  | '+' :: r => (false, r)
  | l => (false, l)

/-- The decimal digits of a natural number (no leading zeros; `0` is `"0"`). -/
def natChars (n : Nat) : List Char := Nat.toDigits 10 n

/-- The decimal text of a natural number. -/
def natText (n : Nat) : String := String.ofList (natChars n)

/-- The decimal text of an integer, with `-` for negatives. -/
def intText (i : Int) : String :=
  if i < 0 then "-" ++ natText i.natAbs else natText i.toNat

/-- Left-pads a character list with `c` to at least `n` characters. -/
def padLeft (n : Nat) (c : Char) (l : List Char) : List Char :=
  List.replicate (n - l.length) c ++ l

/-- `{:0w}` formatting of a natural number. -/
def natPadded (w : Nat) (n : Nat) : String := String.ofList (padLeft w '0' (natChars n))

end Tiramemsu.Codec
