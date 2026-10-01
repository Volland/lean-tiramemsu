/-
`xsd:double` as its IEEE 754 binary64 bit pattern (D11). The numeric meaning of the bits lives
only in the proofs; runtime code never uses hardware `Float` here.
Verified module: imports only `Init`.
-/

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-- A binary64 value as its bit pattern. -/
structure Double64 where
  bits : UInt64
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace Double64

/-- The sign bit. -/
def neg (x : Double64) : Bool := x.bits >>> 63 == 1

/-- The biased exponent field (0–2047). -/
def biasedExp (x : Double64) : Nat := ((x.bits >>> 52) &&& 0x7FF).toNat

/-- The fraction field (below `2^52`). -/
def frac (x : Double64) : Nat := (x.bits &&& 0xFFFFFFFFFFFFF).toNat

def isNaN (x : Double64) : Bool := x.biasedExp == 2047 && x.frac != 0
def isInf (x : Double64) : Bool := x.biasedExp == 2047 && x.frac == 0
def isFinite (x : Double64) : Bool := x.biasedExp != 2047
def isZero (x : Double64) : Bool := x.biasedExp == 0 && x.frac == 0

/-- The quiet NaN every NaN canonicalizes to. -/
def canonNaN : Double64 := ⟨0x7FF8000000000000⟩

/-- Every NaN to `canonNaN`, every other value unchanged. -/
def canon (x : Double64) : Double64 := if x.isNaN then canonNaN else x

def posInf : Double64 := ⟨0x7FF0000000000000⟩
def negInf : Double64 := ⟨0xFFF0000000000000⟩

/-- `±∞`. -/
def inf (neg : Bool) : Double64 := if neg then negInf else posInf

/-- `±0`. -/
def zero (neg : Bool) : Double64 := ⟨if neg then 0x8000000000000000 else 0⟩

/-- The value with a sign, a biased exponent (below 2048) and a fraction (below `2^52`). -/
def ofFields (neg : Bool) (e f : Nat) : Double64 :=
  ⟨((if neg then (1 : UInt64) else 0) <<< 63) ||| (e.toUInt64 <<< 52) ||| f.toUInt64⟩

/-- The significand `M` and exponent `E` of a finite value: its magnitude is `M · 2^E`. -/
def mantExp (x : Double64) : Nat × Int :=
  if x.biasedExp = 0 then (x.frac, -1074) else (x.frac + 2 ^ 52, (x.biasedExp : Int) - 1075)

/-- The value of magnitude `M · 2^E` for a significand `M ≤ 2^53` and an exponent
`E ≥ −1074` as rounding produces them (`M < 2^52` only with `E = −1074`); `±∞` when the
exponent overflows. -/
def ofMantExp (neg : Bool) (M : Nat) (E : Int) : Double64 :=
  let (M, E) := if M = 2 ^ 53 then (2 ^ 52, E + 1) else (M, E)
  if M < 2 ^ 52 then ofFields neg 0 M
  else if E + 1075 ≥ 2047 then inf neg
  else ofFields neg (E + 1075).toNat (M - 2 ^ 52)

end Double64

/-- `⌊log_b n⌋` for `n ≥ 1`, `b ≥ 2` (0 for `n = 0`). -/
def natLogAux (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if b ≤ n && 1 < b then natLogAux b fuel (n / b) + 1 else 0

def natLog (b n : Nat) : Nat := natLogAux b n n

/-- The number of decimal digits of `n ≥ 1`. -/
def numDigits (n : Nat) : Nat := natLog 10 n + 1

/-- `b · 2^t ≤ a` for an integer `t`. -/
def pow2Le (t : Int) (a b : Nat) : Bool :=
  if 0 ≤ t then b <<< t.toNat ≤ a else b ≤ a <<< (-t).toNat

/-- `⌊log₂ (a / b)⌋` for `a, b > 0`. -/
def floorLog2Ratio (a b : Nat) : Int :=
  let t : Int := (Nat.log2 a : Int) - Nat.log2 b
  if pow2Le t a b then t else t - 1

/-- `b · 10^t ≤ a` for an integer `t`. -/
def pow10Le (t : Int) (a b : Nat) : Bool :=
  if 0 ≤ t then b * 10 ^ t.toNat ≤ a else b ≤ a * 10 ^ (-t).toNat

/-- `⌊log₁₀ (a / b)⌋` for `a, b > 0`. -/
def floorLog10Ratio (a b : Nat) : Int :=
  let t : Int := (natLog 10 a : Int) - natLog 10 b
  if pow10Le t a b then t else t - 1

end Tiramemsu.Codec
