/-
Term keys and rows: a dictionary term is identified by `(tag, lex, dt, lang)`, where an absent
`dt` compares equal to 0 and an absent `lang` to the empty string, exactly as the `term_key`
unique index compares (`ifnull(dt, 0)`, `ifnull(lang, '')`).
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Encode
import Tiramemsu.Store.Types

namespace Tiramemsu.Term

open Tiramemsu.Codec

--# @lat: [[codec#Term Dictionary]]

/-- The identity of a dictionary term. -/
structure TermKey where
  tag : Tag
  lex : String
  /-- The raw ObjectId of the datatype IRI. -/
  dt : Option Int64
  lang : Option String
  deriving Repr, DecidableEq, Inhabited

/-- The key as the `term_key` index compares it. -/
def TermKey.coalesced (k : TermKey) : Tag × String × Int64 × String :=
  (k.tag, k.lex, k.dt.getD 0, k.lang.getD "")

/-- Key equality under coalescing. -/
def TermKey.equiv (a b : TermKey) : Bool := a.coalesced == b.coalesced

/-- A dictionary row: the id is the ObjectId payload; `num` holds IEEE bits. -/
structure Row where
  id : Nat
  tag : Tag
  lex : String
  dt : Option Int64
  lang : Option String
  num : Option UInt64
  deriving Repr, DecidableEq, Inhabited

def Row.key (r : Row) : TermKey := ⟨r.tag, r.lex, r.dt, r.lang⟩

/-- The row as the `term` table stores it (`num` normalized as SQLite stores a REAL: NaN as
NULL, −0.0 as +0.0). -/
def Row.toStore (r : Row) : Tiramemsu.Store.TermRow :=
  { id := r.id.toInt64, tag := r.tag.toInt64, lex := r.lex, dt := r.dt, lang := r.lang,
    num := r.num.bind fun b =>
      if (b >>> 52) &&& 0x7FF == 0x7FF && (b &&& 0xFFFFFFFFFFFFF) != 0 then none
      else if b == 0x8000000000000000 then some 0 else some b }

/-- The ObjectId of a term of a tag and an id. -/
def termId (t : Tag) (i : Nat) : ObjectId := ObjectId.ofPayload t i.toUInt64

end Tiramemsu.Term
