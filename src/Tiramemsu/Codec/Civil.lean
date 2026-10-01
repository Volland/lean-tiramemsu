/-
The proleptic Gregorian calendar with astronomical years: day numbers relative to 1970-01-01
and back (Howard Hinnant's era algorithm, as Rust's `days_from_civil` / `civil_from_days`).
Verified module: imports only `Init`.
-/

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals#Dates And Times]]

/-- The Gregorian leap rule, for every year (negative years included). -/
def isLeap (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- The length of month `m` (1–12) of year `y`; 0 for any other `m`. -/
def daysInMonth (y : Int) (m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeap y then 29 else 28
  | _ => 0

/-- A valid proleptic Gregorian date. -/
def validYMD (y : Int) (m d : Nat) : Bool :=
  1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ daysInMonth y m

/-- Days from 1970-01-01 to `y-m-d`. -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The date `(year, month, day)` of a day number. -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m.toNat, d.toNat)

end Tiramemsu.Codec
