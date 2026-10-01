/-
Dates and date-times: timezone codes, the inline `DATETIME` payload `(epoch_ms << 11) | code`,
and the `xsd:date` / `xsd:dateTime` lexical forms as Rust parses and prints them. The packing is
proven; the text functions are tested against the Rust oracle.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Civil
import Tiramemsu.Codec.Text
import Tiramemsu.Codec.ObjectId

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Dates And Times]]

/-- The largest timezone offset in minutes (14:00). -/
abbrev maxOffsetMin : Int := 840

/-- Inline date-times have `−2^48 ≤ ms < 2^48`. -/
abbrev dtMinMs : Int := -(2 ^ 48)
abbrev dtLimitMs : Int := 2 ^ 48

def dtInRange (ms : Int) : Bool := dtMinMs ≤ ms && ms < dtLimitMs

/-- An offset within ±14:00 (or no timezone). -/
def tzValid : Option Int → Bool
  | none => true
  | some m => -maxOffsetMin ≤ m && m ≤ maxOffsetMin

/-- The timezone code: 0 for none, else minutes + 841. -/
def tzCode : Option Int → Nat
  | none => 0
  | some m => (m + 841).toNat

/-- The offset of a timezone code; `InvalidTerm` above 1681. -/
def tzOfCode (c : Nat) : Except CodecError (Option Int) :=
  if c = 0 then .ok none
  else if c ≤ 1681 then .ok (some ((c : Int) - 841))
  else .error (.invalidTerm s!"timezone code {c} out of range")

/-- The `DATETIME` payload of an instant and a timezone code. -/
def packDT (ms : Int) (code : Nat) : Int64 := (Int64.ofInt ms <<< 11) ||| Int64.ofNat code

/-- The `DATETIME` id of an instant and an offset. -/
def encDT (ms : Int) (tz : Option Int) : ObjectId := ObjectId.ofSigned .dateTime (packDT ms (tzCode tz))

/-- The instant and offset of a `DATETIME` payload. -/
def unpackDT (p : Int64) : Except CodecError (Int × Option Int) := do
  let tz ← tzOfCode (p &&& 0x7FF).toNatClampNeg
  pure ((p >>> 11).toInt, tz)

/-! ## Lexical forms -/

/-- Exactly two ASCII digits. -/
def digits2 (l : List Char) : Option Nat :=
  if l.length = 2 then digitsVal? l else none

/-- `[-]YYYY-MM-DD`: the date and the rest of the text. -/
def parseYMD (l : List Char) : Option ((Int × Nat × Nat) × List Char) := do
  let (neg, body) := match l with
    | '-' :: r => (true, r)
    | _ => (false, l)
  let ys := body.takeWhile (· != '-')
  if ys.length = body.length then none
  let rest := body.drop (ys.length + 1)
  if ys.length < 4 || ys.length > 30 || !ys.all isDigitChar then none
  if ys.length > 4 && ys.head? == some '0' then none
  let yn := Nat.ofDigitChars 10 ys 0
  let y : Int := if neg then -(yn : Int) else yn
  if rest.length < 5 || rest[2]? != some '-' then none
  let m ← digits2 (rest.take 2)
  let d ← digits2 ((rest.drop 3).take 2)
  if !(1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ daysInMonth y m) then none
  pure ((y, m, d), rest.drop 5)

/-- An optional timezone: `some none` for none, `some (some minutes)`, or `none` when
ill-formed or beyond ±14:00. -/
def parseTz (l : List Char) : Option (Option Int) :=
  match l with
  | [] => some none
  | ['Z'] => some (some 0)
  | sgn :: rest => do
    if sgn != '+' && sgn != '-' then none
    if rest.length != 5 || rest[2]? != some ':' then none
    let h ← digits2 (rest.take 2)
    let m ← digits2 (rest.drop 3)
    if m > 59 then none
    let total := h * 60 + m
    if (total : Int) > maxOffsetMin then none
    pure (some (if sgn == '-' then -(total : Int) else total))

abbrev int64Min : Int := -(2 ^ 63)
abbrev int64Limit : Int := 2 ^ 63

/-- An `xsd:date` as days since 1970-01-01 (timezone validated and ignored); `none` if
ill-typed or outside the `INT` payload range. -/
def parseDate (s : String) : Option Int := do
  let ((y, m, d), rest) ← parseYMD s.toList
  let _ ← parseTz rest
  let days := daysFromCivil y m d
  if intMin ≤ days && days ≤ intMax then some days else none

abbrev msPerDay : Int := 86400000

/-- An `xsd:dateTime` as (epoch ms, offset minutes); fraction digits beyond the third are
truncated; `none` if ill-typed or if the instant does not fit 64 bits. -/
def parseDateTime (s : String) : Option (Int × Option Int) := do
  let ((y, mo, d), rest) ← parseYMD s.toList
  let r ← match rest with
    | 'T' :: r => some r
    | _ => none
  if r.length < 8 || r[2]? != some ':' || r[5]? != some ':' then none
  let h ← digits2 (r.take 2)
  let mi ← digits2 ((r.drop 3).take 2)
  let sec ← digits2 ((r.drop 6).take 2)
  let r := r.drop 8
  let (fracMs, fracZero, r) ← match r with
    | '.' :: f =>
      let ds := f.takeWhile isDigitChar
      if ds.isEmpty then none
      else
        let ms3 := (ds.take 3) ++ List.replicate (3 - (ds.take 3).length) '0'
        some (Nat.ofDigitChars 10 ms3 0, ds.all (· == '0'), f.drop ds.length)
    | _ => some (0, true, r)
  let tz ← parseTz r
  if mi > 59 || sec > 59 then none
  if h > 24 || (h == 24 && (mi != 0 || sec != 0 || !fracZero)) then none
  let days := daysFromCivil y mo d
  let lcl := days * msPerDay + (h : Int) * 3600000 + (mi : Int) * 60000 + (sec : Int) * 1000 + fracMs
  let utc := lcl - tz.getD 0 * 60000
  if int64Min ≤ utc && utc < int64Limit then some (utc, tz) else none

/-- The year, zero-padded to at least 4 digits, `-` for negative years. -/
def formatYear (y : Int) : String :=
  if y < 0 then "-" ++ natPadded 4 y.natAbs else natPadded 4 y.toNat

/-- `YYYY-MM-DD` of a day number. -/
def formatDate (days : Int) : String :=
  let (y, m, d) := civilFromDays days
  formatYear y ++ "-" ++ natPadded 2 m ++ "-" ++ natPadded 2 d

/-- `YYYY-MM-DDThh:mm:ss.mmm[Z|±hh:mm]` in the value's own offset. -/
def formatDateTime (ms : Int) (tz : Option Int) : String :=
  let lcl := ms + tz.getD 0 * 60000
  let days := lcl / msPerDay
  let tod := lcl % msPerDay
  let (y, m, d) := civilFromDays days
  let h := (tod / 3600000).toNat
  let mi := ((tod / 60000) % 60).toNat
  let sec := ((tod / 1000) % 60).toNat
  let milli := (tod % 1000).toNat
  let zone := match tz with
    | none => ""
    | some 0 => "Z"
    | some off =>
      let a := off.natAbs
      (if off < 0 then "-" else "+") ++ natPadded 2 (a / 60) ++ ":" ++ natPadded 2 (a % 60)
  formatYear y ++ "-" ++ natPadded 2 m ++ "-" ++ natPadded 2 d ++ "T" ++ natPadded 2 h ++ ":" ++
    natPadded 2 mi ++ ":" ++ natPadded 2 sec ++ "." ++ natPadded 3 milli ++ zone

end Tiramemsu.Codec
