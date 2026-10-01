/-
`SHORT_STR` packing: the UTF-8 bytes of a string of at most 7 bytes, big-endian in the high 56
payload bits (first byte highest), zero bytes after the string, and the byte length in the low
4 bits. Unpacking is strict: a length above 7, non-zero padding or non-UTF-8 bytes are
rejected, so packing and unpacking are inverse bijections.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Error

namespace Tiramemsu.Codec

--# @lat: [[codec#Inline Values#Short Strings]]

/-- The longest inline string, in UTF-8 bytes. -/
def shortMaxLen : Nat := 7

/-- The payload word of seven bytes and a length. -/
def packWord (b0 b1 b2 b3 b4 b5 b6 len : UInt64) : UInt64 :=
  (b0 <<< 52) ||| (b1 <<< 44) ||| (b2 <<< 36) ||| (b3 <<< 28) ||| (b4 <<< 20) |||
    (b5 <<< 12) ||| (b6 <<< 4) ||| len

/-- Byte `i` of a byte list, 0 past its end. -/
def byteAt (l : List UInt8) (i : Nat) : UInt64 := (l.getD i 0).toUInt64

/-- The payload of a string of at most 7 UTF-8 bytes. -/
def packShort (s : String) : UInt64 :=
  let l := s.toUTF8.data.toList
  packWord (byteAt l 0) (byteAt l 1) (byteAt l 2) (byteAt l 3) (byteAt l 4) (byteAt l 5)
    (byteAt l 6) s.utf8ByteSize.toUInt64

/-- Byte `i` (0–6, first byte highest) of a payload. -/
def shortByte (p : UInt64) (i : Nat) : UInt8 := ((p >>> (52 - 8 * i).toUInt64) &&& 0xFF).toUInt8

/-- The seven data bytes of a payload. -/
def shortBytes (p : UInt64) : List UInt8 :=
  [shortByte p 0, shortByte p 1, shortByte p 2, shortByte p 3, shortByte p 4, shortByte p 5,
   shortByte p 6]

/-- The string of a payload; `InvalidTerm` for a length above 7, non-zero padding or
non-UTF-8 bytes. -/
def unpackShort (p : UInt64) : Except CodecError String :=
  let len := (p &&& 15).toNat
  if len > shortMaxLen then .error (.invalidTerm s!"SHORT_STR length {len}")
  else
    let bytes := shortBytes p
    if (bytes.drop len).all (· == 0) then
      match String.fromUTF8? (ByteArray.mk (bytes.take len).toArray) with
      | some s => .ok s
      | none => .error (.invalidTerm "SHORT_STR is not UTF-8")
    else .error (.invalidTerm "SHORT_STR padding is not zero")

end Tiramemsu.Codec
