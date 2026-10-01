/-
The shortest round-trip printer for `xsd:double`: for a finite nonzero value, the decimal with
the fewest significant digits (1 … 17) inside the value's rounding interval, the nearest one
among those (the upper one on an exact tie), written as Rust's `{:e}` with the xsd rewrite (`.0` when there is no fraction,
`E` for `e`). All arithmetic is exact (`Nat`).
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Double.Parse

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Doubles]]

/-- Compares `a · 10^pa` with `b · 2^eb`. -/
def cmpDecBin (a : Nat) (pa : Int) (b : Nat) (eb : Int) : Ordering :=
  compare (a * 10 ^ (max pa 0).toNat * 2 ^ (max (-eb) 0).toNat)
    (b * 2 ^ (max eb 0).toNat * 10 ^ (max (-pa) 0).toNat)

/-- The rounding interval of a finite nonzero value `M · 2^E`, in units of `2^(E−2)`:
`(lo, hi, inclusive)`. The upper half-gap is `2^(E−1)`; the lower one is `2^(E−2)` at a
power of two above the smallest normal exponent, else `2^(E−1)`; the ends belong to the
interval exactly when `M` is even (ties round to even). -/
def roundingInterval (x : Double64) : Nat × Nat × Bool :=
  let (M, _) := x.mantExp
  let lo := if x.frac = 0 && x.biasedExp > 1 then 4 * M - 1 else 4 * M - 2
  (lo, 4 * M + 2, M % 2 == 0)

/-- Whether `c · 10^P` lies in the rounding interval of `x` (`M · 2^E`). -/
def inInterval (x : Double64) (c : Nat) (P : Int) : Bool :=
  let (_, E) := x.mantExp
  let (lo, hi, incl) := roundingInterval x
  let okLo := match cmpDecBin c P lo (E - 2) with
    | .gt => true
    | .eq => incl
    | .lt => false
  let okHi := match cmpDecBin c P hi (E - 2) with
    | .lt => true
    | .eq => incl
    | .gt => false
  okLo && okHi

/-- `M · 2^E` as a ratio `num / den` of naturals. -/
def binRatio (M : Nat) (E : Int) : Nat × Nat :=
  if 0 ≤ E then (M * 2 ^ E.toNat, 1) else (M, 2 ^ (-E).toNat)

/-- `⌊log₁₀ x⌋` of a finite nonzero value. -/
def decLog (x : Double64) : Int :=
  let (M, E) := x.mantExp
  let (a, b) := binRatio M E
  floorLog10Ratio a b

/-- The `k`-digit candidates below and above `x` (with `L = ⌊log₁₀ x⌋`): the two multiples of
`10^P` around its value, `P = L − k + 1`. Returns `(f, P)` with candidates `f · 10^P` and
`(f+1) · 10^P`. -/
def candidates (x : Double64) (L : Int) (k : Nat) : Nat × Int :=
  let (M, E) := x.mantExp
  let (a, b) := binRatio M E
  let P := L - k + 1
  let num := a * 10 ^ (max (-P) 0).toNat
  let den := b * 10 ^ (max P 0).toNat
  (num / den, P)

/-- The nearest `k`-digit decimal in the rounding interval, if any. -/
def pickK (x : Double64) (L : Int) (k : Nat) : Option (Nat × Int) :=
  let (M, E) := x.mantExp
  let (f, P) := candidates x L k
  let inF := inInterval x f P
  let inG := inInterval x (f + 1) P
  -- f · 10^P is strictly nearer than (f+1) · 10^P iff 2 · M · 2^E < (2f + 1) · 10^P;
  -- an exact tie takes the upper candidate, as Rust's `{:e}` does
  let fNearer := cmpDecBin (2 * f + 1) P (2 * M) E == .gt
  if inF && inG then some (if fNearer then (f, P) else (f + 1, P))
  else if inF then some (f, P)
  else if inG then some (f + 1, P)
  else none

/-- The first `k` of `start, start+1, …` (at most `fuel` of them) with a candidate. -/
def searchShortest (x : Double64) (L : Int) : Nat → Nat → Option (Nat × Int)
  | 0, _ => none
  | fuel + 1, k => match pickK x L k with
    | some r => some r
    | none => searchShortest x L fuel (k + 1)

/-- Drops trailing zero digits: `(c, P)` with `c · 10^P` unchanged. -/
def stripTrailing : Nat → Nat → Int → Nat × Int
  | 0, c, P => (c, P)
  | fuel + 1, c, P => if c ≠ 0 && c % 10 == 0 then stripTrailing fuel (c / 10) (P + 1) else (c, P)

/-- The shortest decimal `c · 10^P` of a finite nonzero value (`c` without trailing zeros).
Seventeen digits always suffice. -/
def shortestDec (x : Double64) : Nat × Int :=
  let L := decLog x
  let (c, P) := (searchShortest x L 17 1).getD (candidates x L 17)
  stripTrailing (numDigits c) c P

/-- `[-]d.ddd E[-]n`: Rust's `{:e}` of `c · 10^P` with `.0` when there is no fraction and `E`. -/
def sciChars (neg : Bool) (c : Nat) (P : Int) : List Char :=
  let ds := natChars c
  let x : Int := P + ds.length - 1
  let (d0, rest) := match ds with
    | d :: r => (d, r)
    | [] => ('0', [])
  (if neg then ['-'] else []) ++ d0 :: '.' :: (if rest.isEmpty then ['0'] else rest) ++
    'E' :: (intText x).toList

/-- The canonical lexical form of a double. -/
def printDouble (x : Double64) : String :=
  if x.isNaN then "NaN"
  else if x.isInf then (if x.neg then "-INF" else "INF")
  else if x.isZero then (if x.neg then "-0.0E0" else "0.0E0")
  else
    let (c, P) := shortestDec x
    String.ofList (sciChars x.neg c P)

end Tiramemsu.Codec
