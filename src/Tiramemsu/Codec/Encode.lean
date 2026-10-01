/-
Encoding and decoding: a canonical value is either an inline ObjectId or a term spec that the
dictionary stores. Decoding is strict: it accepts only ids that some canonical value encodes
to, so decode is injective and encode after decode is the identity.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Value
import Tiramemsu.Codec.Range
import Tiramemsu.Codec.ShortStr

namespace Tiramemsu.Codec

--# @lat: [[codec#Encoding]]

/-- A value that needs the term dictionary. -/
structure TermSpec where
  /-- `IRI`, `STR`, `LANG_STR`, `TYPED`, `DOUBLE` or `DECIMAL`. -/
  tag : Tag
  /-- Canonical lexical form. -/
  lex : String
  /-- Datatype IRI (`TYPED`, `DOUBLE`, `DECIMAL`). -/
  datatype : Option String
  /-- Lower-cased language tag (`LANG_STR`). -/
  lang : Option String
  /-- IEEE bits of the numeric value (`DOUBLE` unless NaN, `DECIMAL`). -/
  num : Option UInt64
  deriving Repr, DecidableEq, Inhabited

/-- The encoding of a value: an inline id, or a term to look up or intern. -/
inductive Encoded where
  | inline (x : ObjectId)
  | term (t : TermSpec)
  deriving Repr, DecidableEq, Inhabited

/-- The id of an allocated value: origin 0 below `2^48`, `Unsupported "origin <o>"` up to
`2^60`, `InvalidTerm` beyond. -/
def encodeAlloc (k : AllocTag) (n : Nat) : Except CodecError ObjectId :=
  if n < 2 ^ 48 then .ok (mkAlloc k 0 n.toUInt64)
  else if n < 2 ^ 60 then .error (.unsupported (originFeature (n / 2 ^ 48)))
  else .error (.invalidTerm s!"{k.tag.name} counter {n} out of range")

/-- The encoding of a value already in canonical form. -/
def encodeCanonical : Value → Except CodecError Encoded
  | .iri s => .ok (.term ⟨.iri, s, none, none, none⟩)
  | .node n => .inline <$> encodeAlloc .node n
  | .bnode n => .inline <$> encodeAlloc .bnode n
  | .stmt n => .inline <$> encodeAlloc .stmt n
  | .tx n => .inline <$> encodeAlloc .tx n
  | .int i => .ok (.inline (encSigned .int i))
  | .bool b => .ok (.inline (ObjectId.ofPayload .bool (if b then 1 else 0)))
  | .dateTime ms tz => .ok (.inline (encDT ms tz))
  | .date d => .ok (.inline (encSigned .date d))
  | .str s =>
    if s.utf8ByteSize ≤ shortMaxLen then .ok (.inline (ObjectId.ofPayload .shortStr (packShort s)))
    else .ok (.term ⟨.str, s, none, none, none⟩)
  | .langStr lex lang => .ok (.term ⟨.langStr, lex, none, some lang, none⟩)
  | .typed lex dt => .ok (.term ⟨.typed, lex, some dt, none, none⟩)
  | .double x =>
    .ok (.term ⟨.double, printDouble x, some xsdDouble, none, if x.isNaN then none else some x.bits⟩)
  | .decimal s => .ok (.term ⟨.decimal, s, some xsdDecimal, none, (parseDouble s).map (·.bits)⟩)

/-- Encodes a value, canonicalizing it first. Allocated values with a non-zero origin fail
with `Unsupported`. -/
def encode (v : Value) : Except CodecError Encoded := encodeCanonical v.canonical

/-- Decodes an inline id: `none` for dictionary tags, `Unsupported` for tag 15 and non-zero
origins, `InvalidTerm` for ids no canonical value encodes to. -/
def decodeInline (x : ObjectId) : Except CodecError (Option Value) :=
  match x.tag with
  | .error e => .error e
  | .ok t =>
    match t with
    | .node | .bnode | .stmt | .tx =>
      match checkOrigin x, AllocTag.ofTag? t with
      | .error e, _ => .error e
      | .ok (), some k => .ok (some (.ofAlloc k x.counter.toNat))
      | .ok (), none => .ok none
    | .int => .ok (some (.int x.spayload.toInt))
    | .bool =>
      if x.upayload = 0 then .ok (some (.bool false))
      else if x.upayload = 1 then .ok (some (.bool true))
      else .error (.invalidTerm s!"BOOL payload {x.upayload.toNat}")
    | .dateTime => match unpackDT x.spayload with
      | .ok (ms, tz) => .ok (some (.dateTime ms tz))
      | .error e => .error e
    | .date => .ok (some (.date x.spayload.toInt))
    | .shortStr => match unpackShort x.upayload with
      | .ok s => .ok (some (.str s))
      | .error e => .error e
    | _ => .ok none

/-- The value of a dictionary term: its tag, lexical form, datatype IRI and language. A
`DOUBLE` is rebuilt by parsing its lexical form, never from `num`. -/
def valueFromTerm (tag : Tag) (lex : String) (datatype lang : Option String) : Except CodecError Value :=
  match tag with
  | .iri => .ok (.iri lex)
  | .str => .ok (.str lex)
  | .langStr => .ok (.langStr lex (lang.getD ""))
  | .typed => .ok (.typed lex (datatype.getD ""))
  | .double => .ok (.double ((parseDouble lex).getD Double64.canonNaN))
  | .decimal => .ok (.decimal lex)
  | t => .error (.invalidTerm s!"tag {t.name} is not a dictionary tag")

/-- The value of a term spec. -/
def TermSpec.value (t : TermSpec) : Except CodecError Value :=
  valueFromTerm t.tag t.lex t.datatype t.lang

end Tiramemsu.Codec
