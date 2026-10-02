/-
Values in the semantics: the Rust class ranks and memcmp-ordered sort keys (`tm-exec/udf.rs`
`value_key`), an injective total key used to break ties canonically, numeric views with exact
integer/decimal arithmetic and hardware binary64 for doubles (trusted base), value comparison,
effective boolean value and the SPARQL scalar functions.
Verified module: imports only `Init`, `Std` and verified modules. Double arithmetic uses the
core `Float` type, whose operations are part of the trusted base.
-/
import Tiramemsu.IR.Types

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[query#Reference Semantics#Values And Order]]

/-! ## Class ranks and sort keys -/

/-- The class rank (Rust `kind_of_value`): the fixed cross-kind order. -/
def kindRank : Value → Nat
  | .node _ | .bnode _ => 1
  | .iri _ => 2
  | .stmt _ => 3
  | .tx _ => 4
  | .int _ | .double _ | .decimal _ => 5
  | .bool _ => 6
  | .dateTime .. => 7
  | .date _ => 8
  | .str _ => 9
  | .langStr .. => 10
  | .typed .. => 11

/-- Big-endian bytes of a 64-bit word. -/
def beBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun i => ((w >>> (8 * (7 - i)).toUInt64) &&& 0xFF).toUInt8

/-- Order-preserving bytes of a signed 64-bit integer (sign bit flipped). -/
def i64Key (n : Int) : List UInt8 := beBytes ((Int64.ofInt n).toUInt64 ^^^ 0x8000000000000000)

/-- Order-preserving bytes of a binary64 value (NaN after +inf, −0 as +0). -/
def f64Key (x : Double64) : List UInt8 :=
  if x.isNaN then List.replicate 8 0xFF
  else
    let b := if x.isZero then (0 : UInt64) else x.bits
    beBytes (if b >>> 63 == 1 then ~~~b else b ||| 0x8000000000000000)

/-- The exact value of a finite binary64 as `num / den`, with its sign. -/
def _root_.Tiramemsu.Codec.Double64.ratio (x : Double64) : Bool × Nat × Nat :=
  let (M, E) := x.mantExp
  if 0 ≤ E then (x.neg, M * 2 ^ E.toNat, 1) else (x.neg, M, 2 ^ (-E).toNat)

/-- `⌊x⌋` clamped to the signed 64-bit range (Rust `floor_i64`). -/
def floorI64 (x : Double64) : Int :=
  let lo : Int := -(2 ^ 63)
  let hi : Int := 2 ^ 63 - 1
  if x.isNaN then lo
  else if x.isInf then (if x.neg then lo else hi)
  else
    let (neg, n, d) := x.ratio
    let f : Int := if neg then -((n + d - 1) / d : Nat) else (n / d : Nat)
    max lo (min hi f)

/-- The binary64 nearest to an integer. -/
def intToDouble (i : Int) : Double64 := roundRatio (i < 0) i.natAbs 1

/-- A decimal's value as `±m / 10^k`. -/
def decParts (s : String) : Option (Bool × Nat × Nat) := scanDecimal s.toList

/-- The binary64 nearest to a decimal lexical form (NaN when ill-formed). -/
def decToDouble (s : String) : Double64 := (parseDouble s).getD Double64.canonNaN

def numKey (x : Double64) (tie : Int) : List UInt8 := 5 :: (f64Key x ++ i64Key tie)

def strKey (rank : Nat) (s : String) : List UInt8 := rank.toUInt8 :: s.toUTF8.toList

/-- The sort key of a value, byte-identical to Rust `value_key`. -/
def sortKey (v : Value) : List UInt8 :=
  match v.canonical with
  | .iri s => strKey 2 s
  | .node n => [1, 1] ++ beBytes n.toUInt64
  | .bnode n => [1, 2] ++ beBytes n.toUInt64
  | .stmt n => 3 :: beBytes n.toUInt64
  | .tx n => 4 :: beBytes n.toUInt64
  | .int i => numKey (intToDouble i) i
  | .double x => numKey x (floorI64 x)
  | .decimal s =>
    let x := decToDouble s
    if x.isNaN then 5 :: List.replicate 16 0xFF else numKey x (floorI64 x)
  | .bool b => [6, if b then 1 else 0]
  | .dateTime ms _ => 7 :: i64Key ms
  | .date d => 8 :: i64Key d
  | .str s => strKey 9 s
  | .langStr lex lang => strKey 10 lex ++ [0] ++ lang.toUTF8.toList
  | .typed lex _ => strKey 11 lex

/-- Lexicographic comparison of byte lists. -/
def cmpBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else cmpBytes as bs

/-- Lexicographic comparison of natural-number lists. -/
def cmpNats : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else cmpNats as bs

/-! ## An injective total key -/

/-- Integers as naturals, injectively (zig-zag). -/
def zig (i : Int) : Nat := if 0 ≤ i then 2 * i.toNat else 2 * (-i).toNat - 1

def charsKey (s : String) : List Nat := s.toList.map Char.toNat

/-- A self-delimiting key of a string: its length, then its characters. -/
def strTKey (s : String) : List Nat := s.length :: charsKey s

/-- An injective key of a value; ties of the sort key are broken by it. -/
def totalKey : Value → List Nat
  | .iri s => 0 :: strTKey s
  | .node n => [1, n]
  | .bnode n => [2, n]
  | .stmt n => [3, n]
  | .tx n => [4, n]
  | .int i => [5, zig i]
  | .bool b => [6, if b then 1 else 0]
  | .dateTime ms tz => [7, zig ms, match tz with | none => 0 | some z => zig z + 1]
  | .date d => [8, zig d]
  | .str s => 9 :: strTKey s
  | .langStr l g => 10 :: strTKey l ++ strTKey g
  | .typed l d => 11 :: strTKey l ++ strTKey d
  | .double x => [12, x.bits.toNat]
  | .decimal s => 13 :: strTKey s

/-- Prefix-free encoding of a natural list (every element shifted, `0` terminates). -/
def encNats (l : List Nat) : List Nat := l.map (· + 1) ++ [0]

/-- The canonical key of a cell: missing first, then the sort key, then the total key. -/
def cellKey : Option Value → List Nat
  | none => [0]
  | some v => 1 :: (encNats ((sortKey v).map UInt8.toNat) ++ encNats (totalKey v))

/-- The canonical value order: sort key, ties by the total key. -/
def cmpValue (a b : Value) : Ordering := cmpNats (cellKey (some a)) (cellKey (some b))

/-! ## Comparison -/

/-- Value comparison of `<`-style operators: same class rank, by sort key; otherwise an
error (`none`). -/
def cmpOrder (a b : Value) : Option Ordering :=
  if kindRank a != kindRank b then none else some (cmpBytes (sortKey a) (sortKey b))

/-- Value equality: numbers by value, date-times by instant, other typed literals by term
identity; values of different classes are unequal. -/
def valueEq (a b : Value) : Bool :=
  match a, b with
  | .typed .., .typed .. => a == b
  | _, _ => kindRank a == kindRank b && cmpBytes (sortKey a) (sortKey b) == .eq

/-! ## Numbers -/

/-- A numeric view. -/
inductive Num where
  | int (i : Int)
  /-- `q / 10^k`. -/
  | dec (q : Int) (k : Nat)
  | dbl (x : Double64)
  deriving Repr, DecidableEq, Inhabited

def _root_.Tiramemsu.Codec.Value.num? : Value → Option Num
  | .int i => some (.int i)
  | .decimal s => (decParts s).map fun (neg, m, k) => .dec (if neg then -(m : Int) else m) k
  | .double x => some (.dbl x)
  | _ => none

def Num.toDouble : Num → Double64
  | .int i => intToDouble i
  | .dec q k => roundRatio (q < 0) q.natAbs (10 ^ k)
  | .dbl x => x

def toFloat (x : Double64) : Float := Float.ofBits x.bits
def ofFloat (f : Float) : Double64 := (⟨f.toBits⟩ : Double64).canon

/-- A numeric result as a canonical value. -/
def Num.toValue : Num → Value
  | .int i => (Value.int i).canonical
  | .dec q k =>
    let (n, m, k') := normDec (q < 0) q.natAbs k
    .decimal (renderDec n m k')
  | .dbl x => .double x.canon

/-- Aligns two decimals to a common scale. -/
def alignDec (q1 : Int) (k1 : Nat) (q2 : Int) (k2 : Nat) : Int × Int × Nat :=
  if k1 ≤ k2 then (q1 * 10 ^ (k2 - k1), q2, k2) else (q1, q2 * 10 ^ (k1 - k2), k1)

def Num.asDec : Num → Option (Int × Nat)
  | .int i => some (i, 0)
  | .dec q k => some (q, k)
  | .dbl _ => none

/-- `+ - *` exact on integers and decimals, binary64 when a double is involved; `/` is a
binary64 division (as the Rust build). -/
def arith (op : ArithOp) (a b : Num) : Num :=
  match op with
  | .div => .dbl (ofFloat (toFloat a.toDouble / toFloat b.toDouble))
  | _ =>
    match a, b with
    | .int x, .int y => .int (match op with | .add => x + y | .sub => x - y | _ => x * y)
    | _, _ =>
      match a.asDec, b.asDec with
      | some (q1, k1), some (q2, k2) =>
        match op with
        | .mul => .dec (q1 * q2) (k1 + k2)
        | _ =>
          let (x, y, k) := alignDec q1 k1 q2 k2
          .dec (if op == .add then x + y else x - y) k
      | _, _ =>
        let (x, y) := (toFloat a.toDouble, toFloat b.toDouble)
        .dbl (ofFloat (match op with | .add => x + y | .sub => x - y | _ => x * y))

def Num.neg : Num → Num
  | .int i => .int (-i)
  | .dec q k => .dec (-q) k
  | .dbl x => .dbl (ofFloat (-(toFloat x)))

def Num.isZeroOrNaN : Num → Bool
  | .int i => i == 0
  | .dec q _ => q == 0
  | .dbl x => x.isZero || x.isNaN

/-! ## Effective boolean value and scalar functions -/

/-- The effective boolean value; `none` is a type error. -/
def ebv : Value → Option Bool
  | .bool b => some b
  | .str s => some (s != "")
  | .langStr s _ => some (s != "")
  | v => match v.num? with
    | some n => some (!n.isZeroOrNaN)
    | none => none

/-- The lexical form used by string functions (`STR`): IRI text, skolem IRIs, literal forms. -/
def strOf (v : Value) : String := v.lexical

def isStringLike : Value → Bool
  | .str _ | .langStr .. => true
  | _ => false

/-- RFC 4647 basic filtering. -/
def langMatches (tag range : String) : Bool :=
  if range == "*" then tag != ""
  else
    let t := asciiLower tag
    let r := asciiLower range
    t == r || (t.startsWith r && (t.drop r.length).toString.startsWith "-")

def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList.getD n '0'

/-- `ENCODE_FOR_URI`. -/
def encodeForUri (s : String) : String :=
  s.toUTF8.toList.foldl (fun acc b =>
    let c := Char.ofNat b.toNat
    if b < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~') then acc.push c
    else (acc.push '%').push (hexDigit (b.toNat / 16)) |>.push (hexDigit (b.toNat % 16))) ""

/-- XPath rounding of a binary64 to an integer (`⌊x + 0.5⌋`), `none` for NaN. -/
def xround (x : Double64) : Option Int :=
  if x.isNaN then none
  else if x.isInf then some (if x.neg then -(2 ^ 62) else 2 ^ 62)
  else
    let (neg, n, d) := x.ratio
    -- ⌊±n/d + 1/2⌋ = ⌊(±2n + d) / 2d⌋
    let num : Int := (if neg then -(2 * (n : Int)) else 2 * n) + d
    some (num / (2 * (d : Int)))

/-- `SUBSTR` with XPath rounding and 1-based positions. -/
def substr (s : String) (start : Double64) (len : Option Double64) : String :=
  match xround start with
  | none => ""
  | some first =>
    let last : Option Int := match len with
      | none => none
      | some l => (xround l).map (first + ·)
    if len.isSome && last.isNone then ""
    else
      String.ofList ((s.toList.zipIdx).filterMap fun (c, i) =>
        let pos : Int := i + 1
        if first ≤ pos && (match last with | none => true | some l => pos < l) then some c else none)

/-- Index of the first occurrence of `b` in `a`, in characters. -/
def findSub (a b : List Char) : Option Nat :=
  let n := a.length
  (List.range (n + 1)).find? fun i => (a.drop i).take b.length == b && i + b.length ≤ n

def strBefore (a b : String) : String :=
  match findSub a.toList b.toList with
  | some i => String.ofList (a.toList.take i)
  | none => ""

def strAfter (a b : String) : String :=
  match findSub a.toList b.toList with
  | some i => String.ofList (a.toList.drop (i + b.length))
  | none => ""

/-- Local date-time fields `(year, month, day, hour, minute, ms of the minute)`. -/
def dtFields (ms : Int) (tz : Option Int) : Int × Nat × Nat × Nat × Nat × Nat :=
  let local_ := ms + tz.getD 0 * 60000
  let days := local_ / msPerDay
  let rem := (local_ % msPerDay).toNat
  let (y, m, d) := civilFromDays days
  (y, m, d, rem / 3600000, (rem / 60000) % 60, rem % 60000)

def pad2 (n : Nat) : String := natPadded 2 n

/-- `TZ`: `Z`, `±hh:mm`, or empty. -/
def tzText : Option Int → String
  | none => ""
  | some 0 => "Z"
  | some m => (if m < 0 then "-" else "+") ++ pad2 (m.natAbs / 60) ++ ":" ++ pad2 (m.natAbs % 60)

/-- `TIMEZONE` as an `xsd:dayTimeDuration` lexical form. -/
def timezoneText (m : Int) : String :=
  let a := m.natAbs
  let (h, mi) := (a / 60, a % 60)
  (if m < 0 then "-" else "") ++ "PT" ++ (if h != 0 then s!"{h}H" else "") ++
    (if mi != 0 then s!"{mi}M" else "") ++ (if h == 0 && mi == 0 then "0S" else "")

abbrev xsdDayTimeDuration : String := "http://www.w3.org/2001/XMLSchema#dayTimeDuration"

/-- A seconds value `s.mmm` as a decimal. -/
def secondsDec (msOfMinute : Nat) : Value := (Num.dec msOfMinute 3).toValue

/-- The numeric reading of a lexical form for casts. -/
def numberOfLex (lex : String) : Option Double64 :=
  if lex == "true" then some (intToDouble 1)
  else if lex == "false" then some (intToDouble 0)
  else match parseDouble lex with
    | some x => some x
    | none => (canonDecimal lex).map decToDouble

/-- Truncation of a binary64 to an integer (finite values only). -/
def truncD (x : Double64) : Option Int :=
  if x.isNaN || x.isInf then none
  else
    let (neg, n, d) := x.ratio
    some (if neg then -((n / d : Nat) : Int) else (n / d : Nat))

/-- XSD casts. -/
def cast (f : Func) (v : Value) : Option Value :=
  let lex := (strOf v).trimAscii.toString
  match f with
  | .castString => some (.str (strOf v))
  | .castInteger =>
    match v with
    | .int i => some (.int i)
    | .bool b => some (.int (if b then 1 else 0))
    | _ =>
      match parseIntLex lex with
      | some i => if inIntRange i then some (.int i) else none
      | none =>
        match (v.num?.map Num.toDouble).orElse (fun _ => numberOfLex lex) with
        | some x => match truncD x with
          | some i => if i.natAbs < 2 ^ 59 then some (.int i) else none
          | none => none
        | none => none
  | .castDecimal =>
    match v.num? with
    | some (.int i) => some ((Num.dec i 0).toValue)
    | some (.dec q k) => some ((Num.dec q k).toValue)
    | _ =>
      match canonDecimal lex with
      | some c => some (.decimal c)
      | none => match numberOfLex lex with
        | some x => if x.isNaN || x.isInf then none else some (.double x)
        | none => none
  | .castDouble =>
    match v.num? with
    | some n => some (.double n.toDouble)
    | none => (numberOfLex lex).map .double
  | .castBoolean =>
    match v with
    | .bool b => some (.bool b)
    | _ =>
      if lex == "true" || lex == "1" then some (.bool true)
      else if lex == "false" || lex == "0" then some (.bool false)
      else (numberOfLex lex).map fun x => .bool (!(x.isZero || x.isNaN))
  | .castDate =>
    match v with
    | .date d => some (.date d)
    | .dateTime ms tz => some (.date ((ms + tz.getD 0 * 60000) / msPerDay))
    | _ =>
      if lex.contains 'T' then
        (parseDateTime lex).map fun (ms, tz) => .date ((ms + tz.getD 0 * 60000) / msPerDay)
      else (parseDate lex).map .date
  | .castDateTime =>
    match v with
    | .dateTime .. => some v
    | .date d => some (.dateTime (d * msPerDay) none)
    | _ =>
      let r := if lex.contains 'T' then parseDateTime lex else (parseDate lex).map (· * msPerDay, none)
      match r with
      | some (ms, tz) => if dtInRange ms then some (.dateTime ms tz) else none
      | none => none
  | _ => none

/-- The value of a numeric function on a number. -/
def numFn (f : Func) (n : Num) : Option Num :=
  match f, n with
  | .abs, .int i => some (.int i.natAbs)
  | .abs, .dec q k => some (.dec q.natAbs k)
  | .abs, .dbl x => some (.dbl (ofFloat (Float.abs (toFloat x))))
  | .ceil, .int i => some (.int i)
  | .ceil, .dec q k => some (.dec (-((-q) / (10 ^ k : Nat))) 0)
  | .ceil, .dbl x => some (.dbl (ofFloat (Float.ceil (toFloat x))))
  | .floor, .int i => some (.int i)
  | .floor, .dec q k => some (.dec (q / (10 ^ k : Nat)) 0)
  | .floor, .dbl x => some (.dbl (ofFloat (Float.floor (toFloat x))))
  | .round, .int i => some (.int i)
  | .round, .dec q k => some (.dec ((2 * q + (10 ^ k : Nat)) / (2 * (10 ^ k : Nat))) 0)
  | .round, .dbl x => some (.dbl (ofFloat (Float.floor (toFloat x + 0.5))))
  | _, _ => none

/-- A scalar function on evaluated arguments (`none` = error). `REGEX` and `REPLACE` are
handled by the evaluator (unsupported until the SPARQL front end). -/
def applyFunc (f : Func) (args : List Value) : Option Value :=
  match f, args with
  | .str, [v] => some (.str (strOf v))
  | .lang, [v] => match v with
    | .langStr _ l => some (.str l)
    | .iri _ | .node _ | .bnode _ | .stmt _ | .tx _ => none
    | _ => some (.str "")
  | .datatype, [v] => v.datatype.map .iri
  | .isIri, [v] => some (.bool (match v with | .iri _ | .node _ | .stmt _ | .tx _ => true | _ => false))
  | .isBlank, [v] => some (.bool (match v with | .bnode _ => true | _ => false))
  | .isLiteral, [v] => some (.bool (match v with
      | .iri _ | .node _ | .bnode _ | .stmt _ | .tx _ => false | _ => true))
  | .isNumeric, [v] => some (.bool v.num?.isSome)
  | .strLen, [v] => some (.int (strOf v).length)
  | .ucase, [v] => some (.str ((strOf v).map Char.toUpper))
  | .lcase, [v] => some (.str ((strOf v).map Char.toLower))
  | .contains, [a, b] => some (.bool ((findSub (strOf a).toList (strOf b).toList).isSome))
  | .strStarts, [a, b] => some (.bool ((strOf a).startsWith (strOf b)))
  | .strEnds, [a, b] => some (.bool ((strOf a).endsWith (strOf b)))
  | .langMatches, [a, b] => some (.bool (langMatches (strOf a) (strOf b)))
  | .iri, [v] => some (Value.iri (strOf v)).canonical
  | .strDt, [a, b] => some (literal (strOf a) (some (strOf b)) none)
  | .strLang, [a, b] => some (literal (strOf a) none (some (strOf b)))
  | .substr, a :: s :: rest =>
    match s.num?, rest with
    | some n, [] => some (.str (substr (strOf a) n.toDouble none))
    | some n, [l] => (l.num?).map fun m => .str (substr (strOf a) n.toDouble (some m.toDouble))
    | _, _ => none
  | .strBefore, [a, b] => some (.str (strBefore (strOf a) (strOf b)))
  | .strAfter, [a, b] => some (.str (strAfter (strOf a) (strOf b)))
  | .concat, xs => some (.str (String.join (xs.map strOf)))
  | .encodeForUri, [v] => some (.str (encodeForUri (strOf v)))
  | .abs, [v] | .ceil, [v] | .floor, [v] | .round, [v] =>
    v.num?.bind (numFn f) |>.map Num.toValue
  | .year, [.dateTime ms tz] => some (.int (dtFields ms tz).1)
  | .month, [.dateTime ms tz] => some (.int (dtFields ms tz).2.1)
  | .day, [.dateTime ms tz] => some (.int (dtFields ms tz).2.2.1)
  | .hours, [.dateTime ms tz] => some (.int (dtFields ms tz).2.2.2.1)
  | .minutes, [.dateTime ms tz] => some (.int (dtFields ms tz).2.2.2.2.1)
  | .seconds, [.dateTime ms tz] => some (secondsDec (dtFields ms tz).2.2.2.2.2)
  | .timezone, [.dateTime _ (some m)] => some (literal (timezoneText m) (some xsdDayTimeDuration) none)
  | .tz, [.dateTime _ tz] => some (.str (tzText tz))
  | .castString, [v] | .castInteger, [v] | .castDecimal, [v] | .castDouble, [v]
  | .castBoolean, [v] | .castDate, [v] | .castDateTime, [v] => (cast f v).map Value.canonical
  | _, _ => none

end Tiramemsu.Sem
