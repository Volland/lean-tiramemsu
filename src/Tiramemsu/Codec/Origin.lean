/-
Allocated ids (`NODE`, `BNODE`, `STMT`, `TX`): the payload is a 12-bit origin above a 48-bit
counter (D15). Format 1 allocates only origin 0 and rejects other origins.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.ObjectId

namespace Tiramemsu.Codec

--# @lat: [[codec#Origins And Allocation]]

/-- The tags whose payload is allocated from a counter. -/
inductive AllocTag where
  | node
  | bnode
  | stmt
  | tx
  deriving Repr, DecidableEq, Inhabited

namespace AllocTag

def tag : AllocTag → Tag
  | .node => .node | .bnode => .bnode | .stmt => .stmt | .tx => .tx

def kind : AllocTag → IdKind
  | .node => .node | .bnode => .bnode | .stmt => .stmt | .tx => .tx

def ofTag? : Tag → Option AllocTag
  | .node => some .node | .bnode => some .bnode | .stmt => some .stmt | .tx => some .tx
  | _ => none

end AllocTag

/-- Width of the counter. -/
def counterBits : Nat := 48

/-- The largest counter format 1 allocates: `2^48 − 1`. -/
def counterMax : Nat := 2 ^ 48 - 1

/-- The counter mask `2^48 − 1`. -/
def counterMask : UInt64 := 0xFFFFFFFFFFFF

namespace ObjectId

/-- The origin: the high 12 bits of the payload. -/
def origin (x : ObjectId) : UInt64 := x.upayload >>> 48

/-- The counter: the low 48 bits of the payload. -/
def counter (x : ObjectId) : UInt64 := x.upayload &&& counterMask

end ObjectId

/-- The id of an allocated tag with an origin (`< 2^12`) and a counter (`< 2^48`). -/
def mkAlloc (k : AllocTag) (o c : UInt64) : ObjectId :=
  ObjectId.ofPayload k.tag ((o <<< 48) ||| c)

/-- Fails with `Unsupported "origin <n>"` for an allocated-tag id with a non-zero origin. -/
def checkOrigin (x : ObjectId) : Except CodecError Unit :=
  match x.tag with
  | .ok t => if t.isAllocated && x.origin != 0 then .error (.unsupported (originFeature x.origin.toNat))
             else .ok ()
  | .error _ => .ok ()

/-- Allocates the origin-0 id of counter `next`, and the next counter; fails with
`IdSpaceExhausted` once the counter is past `2^48 − 1`. -/
def alloc (k : AllocTag) (next : Nat) : Except CodecError (ObjectId × Nat) :=
  if next ≤ counterMax then .ok (mkAlloc k 0 next.toUInt64, next + 1)
  else .error (.idSpaceExhausted k.kind)

end Tiramemsu.Codec
