/-
Unit tests of the codec scenarios of the object-encoding and literal-canonicalization specs:
one check per scenario value (the proven laws are in `TiramemsuProofs.Codec`).
-/
import Test.Util

namespace Test.Codec

open Test Tiramemsu.Codec

--# @lat: [[codec#Tests]]

def enc (v : Value) : Except CodecError Encoded := encode v
def inl (v : Value) : Option Int := match encode v with
  | .ok (.inline x) => some x.raw.toInt
  | _ => none
def isTerm (v : Value) (t : Tag) : Bool := match encode v with
  | .ok (.term s) => s.tag == t
  | _ => false
def raw (p : UInt64) (tag : UInt64) : ObjectId := ⟨((p <<< 4) ||| tag).toInt64⟩
def errFeature {α : Type} : Except CodecError α → Option String
  | .error (.unsupported f) => some f
  | _ => none
def isInvalid {α : Type} : Except CodecError α → Bool
  | .error (.invalidTerm _) => true
  | _ => false
def lit (lex : String) (dt : String) : Value := literal lex (some dt) none

def run : TestM Unit := do
  -- ObjectId layout and tags
  checkEq "integer five is 85" (inl (.int 5)) (some 85)
  check "85 & 15 identifies INT" ((ObjectId.mk 85).tag == .ok .int)
  checkEq "statement 42 is (42 << 4) | 3" (inl (.stmt 42)) (some (42 * 16 + 3))
  checkEq "transaction 7 is (7 << 4) | 4" (inl (.tx 7)) (some (7 * 16 + 4))
  let big := ObjectId.ofPayload .shortStr (((1 : UInt64) <<< 60) - 1)
  check "large SHORT_STR payload makes a negative id" (decide (big.raw < 0))
  check "tag and payload still read back" (big.tag == .ok .shortStr && big.upayload == ((1 : UInt64) <<< 60) - 1)
  -- SEALED
  checkEq "decoding tag 15" (errFeature (decodeInline (raw 3 15))) (some "SEALED (M6)")
  -- origins
  checkEq "foreign origin rejected on decode" (errFeature (decodeInline (raw (((1 : UInt64) <<< 48) ||| 5) 3))) (some "origin 1")
  checkEq "foreign origin rejected on input" (errFeature (enc (.node (3 * 2 ^ 48 + 1)))) (some "origin 3")
  let a := mkAlloc .stmt 0 42
  check "local ids have origin 0" (a.origin == 0 && a.counter == 42 && a.raw.toInt == 42 * 16 + 3)
  -- allocation bound
  check "last counter value" (match alloc .stmt (2 ^ 48 - 1) with
    | .ok (x, n) => x.origin == 0 && x.counter.toNat == 2 ^ 48 - 1 && n == 2 ^ 48
    | _ => false)
  check "past the bound" (alloc .stmt (2 ^ 48) == .error (.idSpaceExhausted .stmt))
  -- inline round trips
  let dt := (parseDateTime "2026-03-01T12:00:00+02:00").getD (0, none)
  for v in [Value.node 1, .bnode 2, .stmt 3, .tx 4, .int (-7), .bool true, .dateTime dt.1 dt.2,
      .date (-1), .str "héllo"] do
    match encode v with
    | .ok (.inline x) =>
      check s!"round trip {repr v}" (decodeInline x == .ok (some v) && encode v == .ok (.inline x))
    | _ => check s!"inline {repr v}" false
  -- malformed inline ids
  check "BOOL payload 2" (isInvalid (decodeInline (raw 2 6)))
  check "DATETIME timezone code 1682" (isInvalid (decodeInline (raw 1682 7)))
  check "SHORT_STR length 8" (isInvalid (decodeInline (raw 8 9)))
  check "SHORT_STR padding" (isInvalid (decodeInline (raw (((0x61 : UInt64) <<< 52) ||| ((1 : UInt64) <<< 44) ||| 1) 9)))
  -- one ObjectId per value
  let one := inl (.int 1)
  check "lexical variants share an id" (inl (lit "01" xsdInteger) == one && inl (lit "+1" xsdInteger) == one &&
    inl (lit "1" xsdInteger) == one)
  check "inlineable values never reach the dictionary" ([Value.int (2 ^ 59 - 1), .bool false, .date 0,
    .dateTime 0 none, .str "abcdefg"].all fun v => (inl v).isSome)
  -- order
  let ints : List Int := [-1000, -1, 0, 1, 2 ^ 59 - 1]
  let ids := ints.filterMap fun i => inl (.int i)
  check "integers across zero" (ids.length == 5 && (ids.zip ids.tail).all fun (a, b) => a < b)
  let t := (parseDateTime "2026-03-01T10:00:00Z").getD (0, none)
  check "earlier instant sorts first whatever the offset"
    (decide ((encDT t.1 (some 840)).raw < (encDT (t.1 + 1) none).raw))
  -- date-time packing
  let d1 := (parseDateTime "2026-03-01T12:00:00+02:00").getD (0, none)
  let d2 := (parseDateTime "2026-03-01T10:00:00Z").getD (0, none)
  let i1 := encDT d1.1 d1.2
  let i2 := encDT d2.1 d2.2
  check "offsets make two terms with one instant" (i1 != i2 && i1.instant == i2.instant)
  let e := (parseDateTime "1969-12-31T23:59:59.999Z").getD (0, none)
  checkEq "instant before the epoch" (encDT e.1 e.2).instant.toInt (-1)
  -- short strings with NUL bytes
  let ss := ["", "a\x00b", "a"].filterMap fun s => inl (.str s)
  check "strings with NUL bytes" (ss.length == 3 && ss.eraseDups.length == 3)
  for s in ["", "a\x00b", "a"] do
    match encode (.str s) with
    | .ok (.inline x) => check s!"decode {repr s}" (decodeInline x == .ok (some (.str s)))
    | _ => check "short" false
  -- range bounds
  checkEq "integer range bounds" ((rangeLower .int (-5)).toInt, (rangeUpper .int 10).toInt)
    (-5 * 16 + 5, 10 * 16 + 5)
  let inRange := (List.range 40).filter fun (k : Nat) =>
    let x := (encSigned .int ((k : Int) - 20))
    decide (rangeLower .int (-5) ≤ x.raw) && decide (x.raw ≤ rangeUpper .int 10)
  checkEq "ids between the bounds are exactly -5 … 10" inRange.length 16
  let allTz := (List.range 1682).all fun c =>
    let x := encDT t.1 (match tzOfCode c with | .ok tz => tz | _ => none)
    decide (instantLower t.1 ≤ x.raw) && decide (x.raw ≤ instantUpper t.1)
  check "instant range covers every offset" allTz
  check "no other instant inside" (!(decide (instantLower t.1 ≤ (encDT (t.1 + 1) none).raw) &&
    decide ((encDT (t.1 + 1) none).raw ≤ instantUpper t.1)))
  -- skolem IRIs
  check "node round trip" (renderSkolem .node 12 == "urn:tiramemsu:node:12" &&
    inl (.iri "urn:tiramemsu:node:12") == inl (.node 12))
  check "non-canonical forms stay IRIs" (["urn:tiramemsu:node:007", "urn:tiramemsu:node:0",
    "urn:tiramemsu:node:-1"].all fun s => isTerm (.iri s) .iri)
  checkEq "foreign-origin skolem" (errFeature (enc (.iri "urn:tiramemsu:stmt:281474976710661"))) (some "origin 1")
  -- literal classification
  check "language tag lower-cased" (literal "colour" none (some "en-GB") == .langStr "colour" "en-gb")
  check "plain and xsd:string agree" (literal "hello" none none == lit "hello" xsdString)
  check "derived types stay typed" (lit "5" "http://www.w3.org/2001/XMLSchema#int" ==
    .typed "5" "http://www.w3.org/2001/XMLSchema#int")
  check "ill-typed and padded forms stay typed" (lit "abc" xsdInteger == .typed "abc" xsdInteger &&
    lit " 1" xsdInteger == .typed " 1" xsdInteger)
  check "integer variants" (lit "+0001" xsdInteger == .int 1 && lit "-000" xsdInteger == .int 0)
  check "integer range boundaries" ((Value.int (2 ^ 59)).canonical == .typed "576460752303423488" xsdInteger &&
    (Value.int (-(2 ^ 59) - 1)).canonical == .typed "-576460752303423489" xsdInteger &&
    (Value.int (2 ^ 59 - 1)).canonical == .int (2 ^ 59 - 1))
  check "booleans" (lit "1" xsdBoolean == .bool true && lit "true" xsdBoolean == .bool true &&
    lit "TRUE" xsdBoolean == .typed "TRUE" xsdBoolean)
  check "seven-byte boundary" ((inl (.str "abcdefg")).isSome && isTerm (.str "abcdefgh") .str &&
    (inl (.str "héllo")).isSome && isTerm (.str "€€€") .str)
  check "short language string" (isTerm (literal "hi" none (some "en")) .langStr)
  check "invalid calendar dates" (lit "2026-02-30" xsdDate == .typed "2026-02-30" xsdDate &&
    lit "1900-02-29" xsdDate == .typed "1900-02-29" xsdDate &&
    lit "2026-03-01T10:00:00+14:01" xsdDateTime == .typed "2026-03-01T10:00:00+14:01" xsdDateTime &&
    lit "2000-02-29" xsdDate != .typed "2000-02-29" xsdDate)
  check "end-of-day hour" (lit "2026-03-01T24:00:00Z" xsdDateTime == lit "2026-03-02T00:00:00.000Z" xsdDateTime &&
    lit "2026-03-01T24:00:01Z" xsdDateTime == .typed "2026-03-01T24:00:01Z" xsdDateTime)
  check "zero offsets are one code" (lit "2026-03-01T10:00:00Z" xsdDateTime == lit "2026-03-01T10:00:00+00:00" xsdDateTime)
  check "extreme offsets" (tzCode (some (-840)) == 1 && tzCode (some 840) == 1681)
  check "sub-millisecond truncation" (formatDateTime t.1 (some 0) == "2026-03-01T10:00:00.000Z" &&
    lit "2026-03-01T10:00:00.123999Z" xsdDateTime == .dateTime (t.1 + 123) (some 0))
  check "offset kept" ((lit "2026-03-01T12:00:00+02:00" xsdDateTime).lexical == "2026-03-01T12:00:00.000+02:00")
  check "out-of-range instant" (lit "12000-01-01T00:00:00Z" xsdDateTime == .typed "12000-01-01T00:00:00Z" xsdDateTime)
  check "dates around the epoch" (lit "1970-01-01" xsdDate == .date 0 && lit "1969-12-31" xsdDate == .date (-1) &&
    lit "1969-12-31Z" xsdDate == .date (-1))
  check "known day numbers" (daysFromCivil 1970 1 1 == 0 && daysFromCivil 1969 12 31 == -1 &&
    daysFromCivil 2000 3 1 == 11017 && daysFromCivil 0 3 1 == -719468 &&
    civilFromDays 11017 == (2000, 3, 1) && civilFromDays (-719468) == (0, 3, 1))
  check "decimal variants" (lit "01.50" xsdDecimal == .decimal "1.5" && lit "+1.5000" xsdDecimal == .decimal "1.5" &&
    lit "3" xsdDecimal == .decimal "3.0" && lit ".5" xsdDecimal == .decimal "0.5" &&
    lit "-0.0" xsdDecimal == .decimal "0.0" && lit "." xsdDecimal == .typed "." xsdDecimal &&
    lit "1e3" xsdDecimal == .typed "1e3" xsdDecimal)
  let bits (s : String) : Option UInt64 := (parseDouble s).map (·.bits)
  check "equivalent double spellings" (bits "1.0" == some 0x3FF0000000000000 && bits "1E0" == bits "1.0" &&
    bits "+1e+0" == bits "1.0")
  checkEq "ties to even" (bits "9007199254740993") (some 0x4340000000000000)
  check "overflow and underflow" (bits "1e400" == some 0x7FF0000000000000 && bits "-1e400" == some 0xFFF0000000000000 &&
    bits "1e-400" == some 0 && bits "-1e-400" == some 0x8000000000000000 &&
    bits ("1e" ++ String.ofList (List.replicate 1000 '9')) == some 0x7FF0000000000000)
  check "rejected double forms" (["inf", "-NaN", "1e", "0x1p3"].all fun s => (parseDouble s).isNone)
  let forms := [("1.0", "1.0E0"), ("150.0", "1.5E2"), ("-0.00003", "-3.0E-5"), ("0.1", "1.0E-1"),
    ("-0.0", "-0.0E0"), ("5e-324", "5.0E-324"), ("2.2250738585072014e-308", "2.2250738585072014E-308"),
    ("1.7976931348623157e308", "1.7976931348623157E308")]
  for (i, f) in forms do checkEq s!"canonical form {f}" ((parseDouble i).map printDouble) (some f)
  check "NaN payloads collapse" (printDouble ⟨0x7FF0000000000001⟩ == "NaN" && printDouble ⟨0xFFF8000000000123⟩ == "NaN" &&
    (Double64.canon ⟨0x7FF0000000000001⟩).bits == 0x7FF8000000000000)
  check "API typed literal of a special datatype" ((Value.typed "01" xsdInteger).canonical == .int 1)

def main : IO UInt32 := do
  let ((), r) ← run.run {}
  finish "codec" r

end Test.Codec
