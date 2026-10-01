/-
The codec facts the term dictionary relies on (`Term.CodecLaws`), discharged from the codec
proofs, and the dictionary round trip with them. Lives under `Codec` because the layout facts
use `bv_decide` (D12); the dictionary proofs themselves use only the standard axioms.
-/
import TiramemsuProofs.Codec.Encode
import TiramemsuProofs.Term.Dict

namespace Tiramemsu.Codec

open Tiramemsu.Term

--# @lat: [[codec#Term Dictionary]]

theorem decodeInline_dict (x : ObjectId) (t : Tag) (ht : x.tag = .ok t) (hd : t.isDictionary = true) :
    decodeInline x = .ok none := by
  unfold decodeInline
  rw [ht]
  cases t <;> simp [Tag.isDictionary] at hd ⊢

theorem codecLaws : CodecLaws where
  inline v x h := encode_value v (.inline x) h
  term v t h := ⟨encode_value v (.term t) h, encode_term_tag v t h⟩
  layout t i hi := by
    have h60 : ((1 : UInt64) <<< 60).toNat = 2 ^ 60 := by decide
    have hn : i.toUInt64.toNat = i := uint64_toNat_toUInt64 i (by omega)
    have hp : i.toUInt64 < ObjectId.payloadLimit := by
      show i.toUInt64 < (1 : UInt64) <<< 60
      rw [UInt64.lt_iff_toNat_lt, h60, hn]; exact hi
    obtain ⟨a, b, c⟩ := layout t _ hp
    exact ⟨b, by unfold termId; rw [c, hn], a⟩
  decodeDict x t ht hd := decodeInline_dict x t ht hd

/-- Decoding the id returned by interning any value gives the value's canonical form. -/
theorem decode_internValue (d : Dict) (hw : d.WF) (v : Value) (x : ObjectId) (d' : Dict)
    (h : d.internValue v = .ok (x, d')) : d'.decode x = .ok v.canonical :=
  Dict.decode_internValue codecLaws d hw v x d' h

/-- On every reachable dictionary. -/
theorem decode_internValue_reachable (d : Dict) (hr : Dict.Reachable d) (v : Value) (x : ObjectId)
    (d' : Dict) (h : d.internValue v = .ok (x, d')) : d'.decode x = .ok v.canonical :=
  decode_internValue d (Dict.reachable_wf d hr) v x d' h

end Tiramemsu.Codec
