/-
ObjectIds: one signed 64-bit integer `(payload << 4) | tag` per value in a statement position,
stored as is in SQLite's `INTEGER` columns. `INT`, `DATE` and `DATETIME` read the 60-bit
payload with an arithmetic shift, every other tag with a logical shift.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Tag

namespace Tiramemsu.Codec

--# @lat: [[codec#ObjectId Layout]]

/-- A value identifier: the raw integer of the `triple` columns. Order is that of the raw
signed integer. -/
structure ObjectId where
  raw : Int64
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace ObjectId

instance : LT ObjectId := ⟨fun a b => a.raw < b.raw⟩
instance : LE ObjectId := ⟨fun a b => a.raw ≤ b.raw⟩
instance (a b : ObjectId) : Decidable (a < b) := inferInstanceAs (Decidable (a.raw < b.raw))
instance (a b : ObjectId) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.raw ≤ b.raw))
instance : Ord ObjectId := ⟨fun a b => compare a.raw b.raw⟩

/-- Payloads are below `2^60`. -/
def payloadLimit : UInt64 := (1 : UInt64) <<< 60

/-- The id of a tag and an unsigned payload (`payload < 2^60`). -/
def ofPayload (t : Tag) (p : UInt64) : ObjectId := ⟨((p <<< 4) ||| t.toUInt64).toInt64⟩

/-- The id of a tag and a signed payload (`-2^59 ≤ v < 2^59`). -/
def ofSigned (t : Tag) (v : Int64) : ObjectId := ⟨(v <<< 4) ||| t.toInt64⟩

/-- The low 4 bits. -/
def tagBits (x : ObjectId) : UInt64 := x.raw.toUInt64 &&& 15

/-- The tag; `Unsupported "SEALED (M6)"` for tag 15. -/
def tag (x : ObjectId) : Except CodecError Tag := Tag.ofBits x.tagBits

/-- The payload read with a logical shift. -/
def upayload (x : ObjectId) : UInt64 := x.raw.toUInt64 >>> 4

/-- The payload read with an arithmetic shift. -/
def spayload (x : ObjectId) : Int64 := x.raw >>> 4

/-- The instant of a `DATETIME` id in epoch milliseconds: `id >> 15` (arithmetic). -/
def instant (x : ObjectId) : Int64 := x.raw >>> 15

end ObjectId

end Tiramemsu.Codec
