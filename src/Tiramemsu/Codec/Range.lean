/-
Range-scan bounds: a value range on a signed tag (`INT`, `DATE`) is one contiguous id range
filtered by `id & 15 = T`, and an instant range on `DATETIME` is `[(a << 15) | 7,
(b << 15) | 0x7FF7]`. Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.DateTime

namespace Tiramemsu.Codec

--# @lat: [[codec#Order And Ranges]]

/-- The id of a signed-tag value (`INT`, `DATE`): `(v << 4) | tag`. -/
def encSigned (t : Tag) (v : Int) : ObjectId := ObjectId.ofSigned t (Int64.ofInt v)

/-- The inclusive lower bound of the ids of tag `t` with value at least `v`. -/
def rangeLower (t : Tag) (v : Int) : Int64 := (Int64.ofInt v <<< 4) ||| t.toInt64

/-- The inclusive upper bound of the ids of tag `t` with value at most `v`. -/
def rangeUpper (t : Tag) (v : Int) : Int64 := (Int64.ofInt v <<< 4) ||| t.toInt64

/-- The inclusive lower bound of the `DATETIME` ids with instant at least `ms`. -/
def instantLower (ms : Int) : Int64 := (Int64.ofInt ms <<< 15) ||| 7

/-- The inclusive upper bound of the `DATETIME` ids with instant at most `ms`. -/
def instantUpper (ms : Int) : Int64 := (Int64.ofInt ms <<< 15) ||| 0x7FF7

end Tiramemsu.Codec
