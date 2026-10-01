/-
The codec mode of the differential oracle (M1): the Lean codec runs in process and the pinned
Rust `tm-core` runs behind its driver (`codec*` operations); results are compared value by
value. Corpora are the spec edge cases plus seeded random inputs (splitmix64).

  oracle codec smoke                      Rust unit-test values
  oracle codec fuzz [--seed S] [--doubles N] [--parse N] [--values N] [--dates N]
                    [--decode N] [--numbers N]

A mismatch is reported with the suite, the input and both results; the two decoding
deviations (non-zero `SHORT_STR` padding and non-zero origins, rejected by Lean only) are
accepted only when the id really has that shape, and counted. Tooling only.
-/
import Oracle.Driver
import Tiramemsu.Shell.ValueJson

namespace Oracle.Codec

open Tiramemsu.Json Tiramemsu.Codec
open Tiramemsu.Shell (valueJ)

def optJ {α : Type} (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

--# @lat: [[codec#Differential Codec Oracle]]

/-! ## JSON forms (shared with the drivers: `Tiramemsu.Shell.ValueJson`) -/

def errJ (e : CodecError) : Json := .obj #[("err", .str (Tiramemsu.Shell.errCode e))]
def encJ (r : Except CodecError Encoded) : Json := match r with
  | .error e => errJ e
  | r => Tiramemsu.Shell.encodedJ r

/-- Drops error messages and maps every NaN double to the canonical NaN, so that results
compare by code and by canonical value. -/
partial def norm : Json → Json
  | .obj #[("double", .int b)] =>
    let x : Double64 := ⟨UInt64.ofNat b.toNat⟩
    .obj #[("double", .int x.canon.bits.toNat)]
  | .obj kvs => .obj ((kvs.filter (·.1 != "message")).map fun (k, v) => (k, norm v))
  | .arr xs => .arr (xs.map norm)
  | j => j

/-! ## Random inputs -/

/-- splitmix64. -/
structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A number in `[0, n)` (`n > 0`). -/
def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (x.toNat % max n 1, r)

def Rng.pick {α : Type} [Inhabited α] (r : Rng) (xs : Array α) : α × Rng :=
  let (i, r) := r.below xs.size
  (xs[i]!, r)

abbrev RngM := StateM Rng

def rnd (n : Nat) : RngM Nat := modifyGet fun r => r.below n
def rnd64 : RngM UInt64 := modifyGet fun r => r.next
def pick {α : Type} [Inhabited α] (xs : Array α) : RngM α := modifyGet fun r => r.pick xs
def chance (num den : Nat) : RngM Bool := do return (← rnd den) < num

def digitsOf (n : Nat) : RngM String := do
  let mut s := ""
  for _ in [0:n] do s := s.push (Char.ofNat (48 + (← rnd 10)))
  return s

/-- A digit count from a skewed distribution with a maximum. -/
def digitCount (max : Nat) : RngM Nat := do
  let k ← rnd 100
  if k < 50 then rnd (min 21 (max + 1))
  else if k < 80 then rnd (min 101 (max + 1))
  else if k < 95 then rnd (min 401 (max + 1))
  else rnd (max + 1)

/-- A random `xsd:double`-like string: mostly well-formed, sometimes with junk. -/
def randDecimalString (maxDigits : Nat) (withExp : Bool) : RngM String := do
  let sign ← pick #["", "", "", "+", "-"]
  let int ← digitsOf (← digitCount maxDigits)
  let hasFrac ← chance 1 2
  let fracLen ← digitCount maxDigits
  let fracDs ← digitsOf fracLen
  let frac := if hasFrac then "." ++ fracDs else ""
  let skipExp ← chance 2 5
  let e ← pick #["e", "E"]
  let es ← pick #["", "+", "-"]
  let k ← rnd 100
  let a ← rnd 2
  let b ← rnd 400
  let c ← rnd 2000000
  let d ← rnd 1000
  let ed ← if k < 40 then digitsOf (1 + a)
    else if k < 80 then pure (toString b)
    else if k < 95 then pure (toString c)
    else digitsOf (1 + d)
  let exp := if !withExp || skipExp then "" else e ++ es ++ ed
  let s := sign ++ int ++ frac ++ exp
  if ← chance 1 20 then
    let junk ← pick #["x", " ", ".", "e", "+", "-", "_", "é", "0x", "inf"]
    let pos ← rnd (s.length + 1)
    return String.ofList (s.toList.take pos ++ junk.toList ++ s.toList.drop pos)
  return s

/-- The exact decimal text of `n · 2^k`. -/
def dyadicText (n : Nat) (k : Int) : String :=
  if 0 ≤ k then natText (n * 2 ^ k.toNat)
  else
    let d := (-k).toNat
    let ds := natChars (n * 5 ^ d)
    let ds := List.replicate (d + 1 - min ds.length (d + 1)) '0' ++ ds
    String.ofList (ds.take (ds.length - d) ++ '.' :: ds.drop (ds.length - d))

/-! ## Batched comparison -/

structure Suite where
  name : String
  compared : Nat := 0
  accepted : Nat := 0
  failures : Array String := #[]

def Suite.fail (s : Suite) (msg : String) : Suite :=
  if s.failures.size < 20 then { s with failures := s.failures.push msg } else
    { s with failures := s.failures.set! 19 s!"{msg} (and more)" }

/-- Sends inputs in batches to one Rust operation, returning its results in order. -/
def rustBatch (rust : Driver) (op key : String) (items : Array Json) (batch : Nat := 5000) :
    IO (Array Json) := do
  let mut out := #[]
  let mut i := 0
  while i < items.size do
    let chunk := items.extract i (i + batch)
    match ← rust.call op (.obj #[(key, .arr chunk)]) with
    | .ok (.arr rs) => out := out ++ rs
    | .ok r => throw (IO.userError s!"{op}: unexpected result {r.compress.take 200}")
    | .err c m => throw (IO.userError s!"{op}: {c}: {m}")
    i := i + batch
  return out

/-- Compares Lean and Rust results pairwise (after `norm`). `accept` may classify a mismatch
as an accepted deviation. -/
def compareAll (s : Suite) (inputs : Array Json) (lean rust : Array Json)
    (accept : Json → Json → Json → Bool := fun _ _ _ => false) : Suite := Id.run do
  let mut s := s
  if lean.size != rust.size then
    return s.fail s!"result count differs: lean {lean.size}, rust {rust.size}"
  for h : i in [0:lean.size] do
    let l := norm lean[i]
    let r := norm rust[i]!
    s := { s with compared := s.compared + 1 }
    if l.compress != r.compress then
      if accept inputs[i]! l r then s := { s with accepted := s.accepted + 1 }
      else s := s.fail s!"input {inputs[i]!.compress.take 300}: lean {l.compress.take 300}, rust {r.compress.take 300}"
  return s

/-! ## Suites -/

def edgeBits : Array UInt64 := Id.run do
  let mut out : Array UInt64 := #[0, 0x8000000000000000, 0x7FF0000000000000, 0xFFF0000000000000,
    0x7FF8000000000000, 0x7FF0000000000001, 0xFFF8000000000000, 0x7FFFFFFFFFFFFFFF,
    1, 2, 3, 0xFFFFFFFFFFFFF, 0x10000000000000, 0x10000000000001, 0x7FEFFFFFFFFFFFFF,
    0x3FF0000000000000, 0x4062C00000000000]
  for e in [1:2047] do
    let b : UInt64 := e.toUInt64 <<< 52
    out := out ++ #[b, b + 1, b - 1, b ||| 0xFFFFFFFFFFFFF, b ||| 0x8000000000000000]
  return out

def edgeDoubleStrings : Array String := Id.run do
  let mut out : Array String := #["1.0", "1E0", "+1e+0", "9007199254740993", "1e400", "-1e400",
    "1e-400", "-1e-400", "1e" ++ String.ofList (List.replicate 1000 '9'),
    "1e-" ++ String.ofList (List.replicate 1000 '9'), "0", "-0", "-0.0", "+0.0e10", "0e-999999",
    "1.7976931348623157e308", "1.7976931348623158e308", "1.7976931348623159e308",
    "2.2250738585072014e-308", "2.2250738585072011e-308", "2.2250738585072009e-308",
    "4.9406564584124654e-324", "2.4703282292062327e-324", "2.4703282292062328e-324",
    "INF", "+INF", "-INF", "NaN", "", "+", "-", ".", "e5", "1e", "1e+", "1.2.3", "0x1p3",
    "inf", "nan", "-NaN", "+NaN", "NaN ", " 1", "1 ", "1_000", "1e5.5", "--1", "+-1", "1.",
    ".5", "+.5e-3", "1.e5", "00000000000000000000000000001.5", "123456789012345678901234567890"]
  for i in [0:633] do
    let e : Int := (i : Int) - 324
    out := out.push ("1e" ++ toString e)
  return out

/-- Halfway decimals between consecutive doubles, and their neighbours one unit away in the
last digit (below and above). -/
def halfwayStrings (n : Nat) : RngM (Array String) := do
  let mut out := #[]
  for _ in [0:n] do
    let b ← rnd64
    let x : Double64 := ⟨b &&& 0x7FEFFFFFFFFFFFFF⟩
    let (M, E) := x.mantExp
    let t := dyadicText (2 * M + 1) (E - 1)
    out := out ++ #[t, t ++ "0000000000000000000001", (if t.contains '.' then t else t ++ ".") ++ "9e0"]
  return out

def suitePrint (rust : Driver) (n seed : Nat) : IO Suite := do
  let (randBits, _) := (do
    let mut xs := #[]
    for _ in [0:n] do xs := xs.push (← rnd64)
    return xs : RngM (Array UInt64)).run ⟨seed.toUInt64⟩
  let parsed := edgeDoubleStrings.filterMap parseDouble
  let near := parsed.flatMap fun x => #[x.bits, x.bits + 1, x.bits - 1]
  let all := edgeBits ++ near ++ randBits
  let inputs := all.map fun b => Json.int b.toNat
  let lean := all.map fun b => Json.str (printDouble ⟨b⟩)
  let rust ← rustBatch rust "codecPrintDoubles" "bits" inputs 20000
  return compareAll { name := "print doubles" } inputs lean rust

def suiteParse (rust : Driver) (n seed : Nat) : IO Suite := do
  let (rand, _) := (do
    let mut xs := #[]
    for _ in [0:n] do xs := xs.push (← randDecimalString 800 true)
    let hw ← halfwayStrings (n / 20 + 100)
    return xs ++ hw : RngM (Array String)).run ⟨seed.toUInt64 + 1⟩
  let all := edgeDoubleStrings ++ rand
  let inputs := all.map Json.str
  let lean := all.map fun s => optJ (fun (x : Double64) => Json.int x.bits.toNat) (parseDouble s)
  let rust ← rustBatch rust "codecParseDoubles" "lex" inputs 2000
  return compareAll { name := "parse doubles" } inputs lean rust

/-! ### Dates and date-times -/

def randYear : RngM String := do
  let k ← rnd 100
  let neg ← chance 1 4
  let a ← rnd 10000
  let b ← rnd 1000001
  let c ← rnd 27
  let d ← rnd 4
  let body ← if k < 60 then pure (natPadded 4 a)
    else if k < 85 then pure (toString b)
    else if k < 95 then digitsOf (4 + c)
    else digitsOf (1 + d)
  return (if neg then "-" else "") ++ body

def randTz : RngM String := do
  let k ← rnd 10
  if k < 3 then return ""
  if k < 5 then return "Z"
  let sign ← pick #["+", "-"]
  let h ← rnd 16
  let m ← pick #[0, 0, 30, 45, 1, 59, 60]
  let h := if ← chance 1 10 then 14 else h
  return sign ++ natPadded 2 h ++ ":" ++ natPadded 2 m

def randDateLex : RngM String := do
  let y ← randYear
  let m ← pick #[1, 2, 3, 4, 6, 9, 11, 12, 0, 13]
  let d ← pick #[1, 15, 28, 29, 30, 31, 0, 32]
  let tz ← randTz
  let sep ← pick #["-", "-", "-", "/"]
  return y ++ sep ++ natPadded 2 m ++ "-" ++ natPadded 2 d ++ tz

def randDateTimeLex : RngM String := do
  let y ← randYear
  let m ← pick #[1, 2, 3, 4, 6, 9, 11, 12, 0, 13]
  let d ← pick #[1, 15, 28, 29, 30, 31, 0, 32]
  let h ← pick #[0, 1, 12, 23, 24, 24, 25]
  let mi ← pick #[0, 0, 1, 30, 59, 60]
  let s ← pick #[0, 0, 1, 59, 60]
  let hasFrac ← chance 1 2
  let n ← rnd 8
  let fd ← digitsOf n
  let frac := if hasFrac then "." ++ fd else ""
  let tz ← randTz
  return y ++ "-" ++ natPadded 2 m ++ "-" ++ natPadded 2 d ++ "T" ++ natPadded 2 h ++ ":" ++
    natPadded 2 mi ++ ":" ++ natPadded 2 s ++ frac ++ tz

def suiteDates (rust : Driver) (n seed : Nat) : IO (Array Suite) := do
  let ((dates, dts, days, dtv), _) := (do
    let mut a := #[]; let mut b := #[]; let mut c := #[]; let mut d := #[]
    for _ in [0:n] do
      a := a.push (← randDateLex)
      b := b.push (← randDateTimeLex)
      let span ← pick #[1000000, 1000000000, 1000000000000000]
      c := c.push ((← rnd (2 * span)) - (span : Int))
      let ms : Int := (← rnd (2 ^ 49)) - (2 ^ 48 : Int)
      let none? ← chance 1 5
      let off ← rnd 1681
      let tz : Option Int := if none? then none else some ((off : Int) - 840)
      d := d.push (ms, tz)
    return (a, b, c, d) : RngM _).run ⟨seed.toUInt64 + 2⟩
  let fixed := #["2026-02-30", "1900-02-29", "2000-02-29", "1970-01-01", "1969-12-31", "1969-12-31Z",
    "0000-03-01", "-0001-12-31", "12000-01-01", "01234-01-01"]
  let fixedDT := #["2026-03-01T10:00:00+14:01", "2026-03-01T24:00:00Z", "2026-03-01T24:00:01Z",
    "2026-03-01T10:00:00.123999Z", "2026-03-01T12:00:00+02:00", "12000-01-01T00:00:00Z",
    "1969-12-31T23:59:59.999Z", "2026-03-01T10:00:00Z", "2026-03-01T10:00:00+00:00",
    "2026-03-01T10:00:00-00:00", "2026-03-01T10:00:00.", "2026-03-01T10:00"]
  let dl := (fixed ++ dates).map Json.str
  let s1 := compareAll { name := "parse dates" } dl
    ((fixed ++ dates).map fun s => optJ Json.int (parseDate s)) (← rustBatch rust "codecDates" "lex" dl)
  let tl := (fixedDT ++ dts).map Json.str
  let s2 := compareAll { name := "parse date-times" } tl
    ((fixedDT ++ dts).map fun s => optJ (fun (ms, tz) => Json.arr #[.int ms, optJ .int tz]) (parseDateTime s))
    (← rustBatch rust "codecDateTimes" "lex" tl)
  let dj := days.map Json.int
  let s3 := compareAll { name := "format dates" } dj (days.map fun d => .str (formatDate d))
    (← rustBatch rust "codecFormatDates" "days" dj)
  let tj := dtv.map fun (ms, tz) => Json.arr #[.int ms, optJ .int tz]
  let s4 := compareAll { name := "format date-times" } tj (dtv.map fun (ms, tz) => .str (formatDateTime ms tz))
    (← rustBatch rust "codecFormatDateTimes" "items" tj)
  -- property: the canonical text of an in-range (instant, timezone) parses back to it
  let mut s5 : Suite := { name := "date-time text round trip (property)" }
  for (ms, tz) in dtv do
    s5 := { s5 with compared := s5.compared + 1 }
    if parseDateTime (formatDateTime ms tz) != some (ms, tz) then
      s5 := s5.fail s!"({ms}, {tz}) prints {formatDateTime ms tz}, parses {repr (parseDateTime (formatDateTime ms tz))}"
  return #[s1, s2, s3, s4, s5]

/-! ### Integers, booleans and decimals -/

def randIntLex : RngM String := do
  let sign ← pick #["", "", "+", "-"]
  let lead ← pick #["", "", "0", "000"]
  let ds ← digitsOf (← digitCount 60)
  let s := sign ++ lead ++ ds
  if ← chance 1 15 then return s ++ (← pick #[".0", " ", "e3", "x"]) else return s

def suiteNumbers (rust : Driver) (n seed : Nat) : IO (Array Suite) := do
  let ((ints, decs), _) := (do
    let mut a := #[]; let mut b := #[]
    for _ in [0:n] do
      a := a.push (← randIntLex)
      b := b.push (← randDecimalString 60 false)
    return (a, b) : RngM _).run ⟨seed.toUInt64 + 3⟩
  let fi := #["+0001", "01", "1", "-000", "1.0", " 1", "abc", "", "+", "-", "576460752303423487",
    "576460752303423488", "-576460752303423488", "-576460752303423489"]
  let fd := #["01.50", "1.5", "+1.5000", "3", ".5", "-0.0", ".", "1e3", "", "-.05", "0.000", "-1."]
  let il := (fi ++ ints).map Json.str
  let s1 := compareAll { name := "canonical integers" } il ((fi ++ ints).map fun s => optJ .str (canonInteger s))
    (← rustBatch rust "codecCanonIntegers" "lex" il)
  let dl := (fd ++ decs).map Json.str
  let s2 := compareAll { name := "canonical decimals" } dl ((fd ++ decs).map fun s => optJ .str (canonDecimal s))
    (← rustBatch rust "codecCanonDecimals" "lex" dl)
  return #[s1, s2]

/-! ### Literal classification and value encoding -/

def dts : Array String := #[xsdInteger, xsdBoolean, xsdString, xsdDate, xsdDateTime, xsdDouble,
  xsdDecimal, "http://www.w3.org/2001/XMLSchema#int", "http://www.opengis.net/ont/geosparql#wktLiteral",
  rdfLangString, "urn:x:custom"]

def randString : RngM String := do
  let parts := #["a", "b", "é", "€", "\x00", " ", "𝄞", "abcdefg", "urn:x:", "NaN"]
  let n ← rnd 6
  let mut s := ""
  for _ in [0:n] do s := s ++ (← pick parts)
  return s

def randLexFor (dt : String) : RngM String := do
  if dt == xsdInteger then randIntLex
  else if dt == xsdBoolean then pick #["true", "false", "1", "0", "TRUE", " 1", ""]
  else if dt == xsdDate then randDateLex
  else if dt == xsdDateTime then randDateTimeLex
  else if dt == xsdDouble then randDecimalString 30 true
  else if dt == xsdDecimal then randDecimalString 30 false
  else randString

def randLiteral : RngM (String × Option String × Option String) := do
  let k ← rnd 10
  if k == 0 then return (← randString, none, some (← pick #["en", "en-GB", "EN-gb", "de", "", "Zh-Hant"]))
  if k == 1 then return (← randString, none, none)
  let dt ← pick dts
  return (← randLexFor dt, some dt, none)

def skolemIris : Array String := #["urn:tiramemsu:node:12", "urn:tiramemsu:bnode:3",
  "urn:tiramemsu:stmt:281474976710661", "urn:tiramemsu:tx:281474976710655",
  "urn:tiramemsu:node:007", "urn:tiramemsu:node:0", "urn:tiramemsu:node:-1",
  "urn:tiramemsu:node:1152921504606846976", "urn:tiramemsu:node:1152921504606846975",
  "urn:tiramemsu:node:", "urn:tiramemsu:nodes:1", "https://example.org/alice", "urn:x:abcdefghij"]

def randValue : RngM Value := do
  let k ← rnd 14
  match k with
  | 0 => return .iri (← pick (skolemIris ++ #["http://ex/" ++ (← randString)]))
  | 1 => return .node (← rnd (2 ^ 49))
  | 2 => return .bnode (← rnd (2 ^ 48))
  | 3 => return .stmt (← rnd (2 ^ 50))
  | 4 => return .tx (← rnd (2 ^ 48))
  | 5 => do
    let span ← pick #[1000, 2 ^ 59 + 10, 2 ^ 63]
    let v : Int := (← rnd (2 * span)) - (span : Int)
    return .int (max (-(2 ^ 63)) (min v (2 ^ 63 - 1)))
  | 6 => return .bool (← chance 1 2)
  | 7 => do
    let span ← pick #[2 ^ 40, 2 ^ 48 + 1000, 2 ^ 62]
    let ms : Int := (← rnd (2 * span)) - (span : Int)
    let none? ← chance 1 4
    let off ← rnd 2001
    let tz : Option Int := if none? then none else some ((off : Int) - 1000)
    return .dateTime ms tz
  | 8 => do
    let span ← pick #[100000, 2 ^ 59 + 10, 2 ^ 62]
    return .date ((← rnd (2 * span)) - (span : Int))
  | 9 => return .str (← randString)
  | 10 => return .langStr (← randString) (← pick #["en", "EN-gb", "x-Y"])
  | 11 => do
    let dt ← pick dts
    return .typed (← randLexFor dt) dt
  | 12 => return .double ⟨← rnd64⟩
  | _ => return .decimal (← randDecimalString 30 false)

def literalJ (lex : String) (dt lang : Option String) : Json :=
  .arr #[.str lex, optJ .str dt, optJ .str lang]

def suiteValues (rust : Driver) (n seed : Nat) : IO (Array Suite) := do
  let ((lits, vals), _) := (do
    let mut a := #[]; let mut b := #[]
    for _ in [0:n] do
      a := a.push (← randLiteral)
      b := b.push (← randValue)
    return (a, b) : RngM _).run ⟨seed.toUInt64 + 4⟩
  let fixedLits : Array (String × Option String × Option String) := #[
    ("colour", none, some "en-GB"), ("colour", none, some "en-gb"), ("hello", none, none),
    ("hello", some xsdString, none), ("5", some "http://www.w3.org/2001/XMLSchema#int", none),
    ("POINT(1 2)", some "http://www.opengis.net/ont/geosparql#wktLiteral", none),
    ("abc", some xsdInteger, none), (" 1", some xsdInteger, none), ("+0001", some xsdInteger, none),
    ("01", some xsdInteger, none), ("-000", some xsdInteger, none),
    ("576460752303423488", some xsdInteger, none), ("-576460752303423489", some xsdInteger, none),
    ("1", some xsdBoolean, none), ("true", some xsdBoolean, none), ("TRUE", some xsdBoolean, none),
    ("abcdefg", none, none), ("abcdefgh", none, none), ("héllo", none, none), ("€€€", none, none),
    ("hi", none, some "en"), ("2026-02-30", some xsdDate, none), ("1900-02-29", some xsdDate, none),
    ("2000-02-29", some xsdDate, none), ("2026-03-01T10:00:00+14:01", some xsdDateTime, none),
    ("2026-03-01T24:00:00Z", some xsdDateTime, none), ("2026-03-01T24:00:01Z", some xsdDateTime, none),
    ("2026-03-01T10:00:00.123999Z", some xsdDateTime, none),
    ("12000-01-01T00:00:00Z", some xsdDateTime, none), ("1970-01-01", some xsdDate, none),
    ("1969-12-31Z", some xsdDate, none), ("01.50", some xsdDecimal, none), ("3", some xsdDecimal, none),
    (".5", some xsdDecimal, none), ("-0.0", some xsdDecimal, none), (".", some xsdDecimal, none),
    ("1e3", some xsdDecimal, none), ("1.0", some xsdDouble, none), ("1E0", some xsdDouble, none),
    ("9007199254740993", some xsdDouble, none), ("NaN", some xsdDouble, none),
    ("-NaN", some xsdDouble, none), ("0.10", some xsdDecimal, none), ("", none, none),
    ("a\x00b", none, none)]
  let allLits := fixedLits ++ lits
  let li := allLits.map fun (l, d, g) => literalJ l d g
  let lean := allLits.map fun (l, d, g) =>
    let v := literal l d g
    Json.obj #[("enc", encJ (encode v)), ("value", valueJ v)]
  let s1 := compareAll { name := "literal classification and encoding" } li lean
    (← rustBatch rust "codecLiterals" "items" li 2000)
  let fixedVals : Array Value := #[.int 5, .stmt 42, .tx 7, .node 1, .bnode 2, .stmt 3, .tx 4, .int (-7),
    .bool true, .date (-1), .str "héllo", .str "", .str "a\x00b", .str "a", .node ((3 * 2 ^ 48) + 1),
    .stmt (2 ^ 48 - 1), .stmt (2 ^ 48), .int (2 ^ 59 - 1), .int (-(2 ^ 59)), .int (2 ^ 59),
    .int (-(2 ^ 59) - 1), .iri "urn:tiramemsu:node:12", .double ⟨0x7FF0000000000001⟩,
    .typed "01" xsdInteger, .decimal "01.50", .langStr "x" "EN-GB"]
  let allVals := fixedVals ++ vals
  let vi := allVals.map valueJ
  let leanV := allVals.map fun v =>
    let c := v.canonical
    Json.obj #[("canonical", valueJ c), ("datatype", optJ .str c.datatype), ("enc", encJ (encode v)),
      ("lexical", .str c.lexical)]
  let s2 := compareAll { name := "API values: canonical, encoding, lexical form" } vi leanV
    (← rustBatch rust "codecValues" "values" vi 2000)
  -- properties: canonicalization is idempotent and lexical forms are stable
  let mut s3 : Suite := { name := "canonical idempotence and lexical stability (property)" }
  for v in allVals ++ allLits.map (fun (l, d, g) => literal l d g) do
    let c := v.canonical
    s3 := { s3 with compared := s3.compared + 1 }
    if c.canonical != c then s3 := s3.fail s!"canonical not idempotent on {repr v}"
    let back := match c with
      | .iri _ | .node _ | .bnode _ | .stmt _ | .tx _ => (Value.iri c.lexical).canonical
      | .langStr lex lang => literal lex none (some lang)
      | _ => literal c.lexical c.datatype none
    if back != c then s3 := s3.fail s!"lexical form of {repr c} classifies as {repr back}"
  return #[s1, s2, s3]

/-! ### Decoding raw ids -/

/-- Whether Lean's strict decoding may reject an id that Rust accepts: a non-zero origin on an
allocated tag, or non-zero `SHORT_STR` padding (listed deviations). -/
def strictDeviation (raw : Int) : Bool :=
  let x : ObjectId := ⟨Int64.ofInt raw⟩
  match x.tag with
  | .ok t =>
    if t.isAllocated then x.origin != 0
    else if t == .shortStr then
      let len := (x.upayload &&& 15).toNat
      len ≤ 7 && !((shortBytes x.upayload).drop len).all (· == 0)
    else false
  | .error _ => false

def suiteDecode (rust : Driver) (n seed : Nat) : IO Suite := do
  let (ids, _) := (do
    let mut xs : Array Int := #[]
    for _ in [0:n] do
      let b ← rnd64
      let tag ← rnd 16
      let k ← rnd 4
      -- small payloads, random payloads, and the shapes of the deviations
      let p : UInt64 := if k == 0 then (b &&& (0xFFFF : UInt64)) else if k == 1 then b >>> (4 : UInt64)
        else if k == 2 then (b &&& (0xFFFFFFFFFFFF : UInt64))
        else ((b &&& (0xFFFFFFFFFFFFF0 : UInt64)) ||| ((b >>> (60 : UInt64)) &&& (7 : UInt64)))
      xs := xs.push ((p <<< 4) ||| tag.toUInt64).toInt64.toInt
    return xs : RngM (Array Int)).run ⟨seed.toUInt64 + 5⟩
  let rawOf (p tag : UInt64) : Int := ((p <<< (4 : UInt64)) ||| tag).toInt64.toInt
  let fixed : Array Int := #[85, (42 * 16) + 3, (7 * 16) + 4, (3 * 16) + 15,
    rawOf (((1 : UInt64) <<< 48) ||| 5) 3, rawOf 2 6, rawOf (1682 : UInt64) 7, rawOf 8 9,
    rawOf (((0x61 : UInt64) <<< 52) ||| ((1 : UInt64) <<< 44) ||| 1) 9,
    rawOf (((1 : UInt64) <<< 60) - 1) 9]
  let all := fixed ++ ids
  let inputs := all.map Json.int
  let lean := all.map fun raw => match decodeInline ⟨Int64.ofInt raw⟩ with
    | .ok (some v) => valueJ v
    | .ok none => Json.null
    | .error e => errJ e
  let rust ← rustBatch rust "codecDecode" "ids" inputs 20000
  return compareAll { name := "decode inline ids" } inputs lean rust fun inp l _ =>
    match inp, l with
    | .int raw, .obj #[("err", _)] => strictDeviation raw
    | _, _ => false

/-! ## Benchmark (report-only, D14) -/

def bench (rust : Driver) (n seed : Nat) (out : System.FilePath) : IO UInt32 := do
  let ((bits, lex), _) := (do
    let mut bs := #[]; let mut ls := #[]
    for _ in [0:n] do
      bs := bs.push (← rnd64)
      ls := ls.push (← randDecimalString 20 true)
    return (bs, ls) : RngM _).run ⟨seed.toUInt64 + 99⟩
  let r ← rust.call! "codecBench" (.obj #[("bits", .arr (bits.map fun b => .int b.toNat)),
    ("lex", .arr (lex.map Json.str))])
  let rp := (r.getInt? "printNs").getD 0
  let rq := (r.getInt? "parseNs").getD 0
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for b in bits do acc := acc + (printDouble ⟨b⟩).length
  let t1 ← IO.monoNanosNow
  for s in lex do acc := acc + (match parseDouble s with | some x => (x.bits &&& 1).toNat | none => 0)
  let t2 ← IO.monoNanosNow
  let lp := t1 - t0
  let lq := t2 - t1
  let per (ns : Int) : String := s!"{(ns / (max n 1)).toNat} ns/op"
  let ratio (a b : Int) : String := if b ≤ 0 then "n/a" else s!"{(a * 100 / b).toNat / 100}.{(a * 100 / b).toNat % 100}x"
  let md := s!"# Codec benchmark (report-only, D14)\n\n{n} random bit patterns printed, {n} random decimal strings (≤ 20 digits, optional exponent) parsed; seed {seed}; check {acc}.\n\n| Operation | Rust | Lean | Lean / Rust |\n|---|---|---|---|\n| print (`canonical_double`) | {per rp} | {per lp} | {ratio lp rp} |\n| parse (`parse_double`) | {per rq} | {per lq} | {ratio lq rq} |\n"
  IO.FS.createDirAll (out.parent.getD ".")
  IO.FS.writeFile out md
  IO.println md
  return 0

/-! ## Entry points -/

def report (suites : Array Suite) : IO UInt32 := do
  let mut failures := 0
  for s in suites do
    for f in s.failures do IO.eprintln s!"FAIL [{s.name}] {f}"
    let acc := if s.accepted > 0 then s!", {s.accepted} accepted deviation(s)" else ""
    IO.println s!"codec {s.name}: {s.compared} compared, {s.failures.size} mismatch(es){acc}"
    failures := failures + s.failures.size
  return if failures == 0 then 0 else 1

/-- The Rust unit-test values (task 1.3 smoke test). -/
def smoke (rust : Driver) : IO UInt32 := do
  let s1 ← suitePrint rust 0 1
  let s2 ← suiteParse rust 0 1
  let vs ← suiteValues rust 0 1
  report (#[s1, s2] ++ vs)

def fuzz (rust : Driver) (seed doubles parse values dates decode numbers : Nat) : IO UInt32 := do
  let mut suites := #[]
  suites := suites.push (← suitePrint rust doubles seed)
  suites := suites.push (← suiteParse rust parse seed)
  suites := suites ++ (← suiteValues rust values seed)
  suites := suites ++ (← suiteDates rust dates seed)
  suites := suites.push (← suiteDecode rust decode seed)
  suites := suites ++ (← suiteNumbers rust numbers seed)
  report suites

end Oracle.Codec
