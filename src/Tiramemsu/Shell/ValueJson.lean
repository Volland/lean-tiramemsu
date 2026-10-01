/-
The JSON form of values and encodings shared by the Lean driver and the oracle, identical to
the Rust driver's (`oracle/rust-driver/src/codec.rs`): one key per variant. Shell module.
-/
import Tiramemsu.Shell.Json
import Tiramemsu.Codec.Encode

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.Codec

--# @lat: [[codec#Differential Codec Oracle]]

def optMapJ {α : Type} (f : α → Json) : Option α → Json
  | some a => f a
  | none => .null

def valueJ : Value → Json
  | .iri s => .obj #[("iri", .str s)]
  | .node n => .obj #[("node", .int n)]
  | .bnode n => .obj #[("bnode", .int n)]
  | .stmt n => .obj #[("stmt", .int n)]
  | .tx n => .obj #[("tx", .int n)]
  | .int i => .obj #[("int", .int i)]
  | .bool b => .obj #[("bool", .bool b)]
  | .dateTime ms tz => .obj #[("dateTime", .arr #[.int ms, optMapJ .int tz])]
  | .date d => .obj #[("date", .int d)]
  | .str s => .obj #[("str", .str s)]
  | .langStr l g => .obj #[("langStr", .arr #[.str l, .str g])]
  | .typed l d => .obj #[("typed", .arr #[.str l, .str d])]
  | .double x => .obj #[("double", .int x.bits.toNat)]
  | .decimal s => .obj #[("decimal", .str s)]

def valueOfJ? (j : Json) : Option Value := do
  let .obj #[(k, v)] := j | none
  let str : Json → Option String := fun | .str s => some s | _ => none
  let int : Json → Option Int := fun | .int i => some i | _ => none
  let nat : Json → Option Nat := fun | .int i => if i ≥ 0 then some i.toNat else none | _ => none
  let pair : Json → Option (Json × Json) := fun | .arr #[a, b] => some (a, b) | _ => none
  match k with
  | "iri" => .iri <$> str v
  | "node" => .node <$> nat v
  | "bnode" => .bnode <$> nat v
  | "stmt" => .stmt <$> nat v
  | "tx" => .tx <$> nat v
  | "int" => .int <$> int v
  | "bool" => match v with | .bool b => some (.bool b) | _ => none
  | "dateTime" => do
    let (a, b) ← pair v
    pure (.dateTime (← int a) (match b with | .int t => some t | _ => none))
  | "date" => .date <$> int v
  | "str" => .str <$> str v
  | "langStr" => do let (a, b) ← pair v; pure (.langStr (← str a) (← str b))
  | "typed" => do let (a, b) ← pair v; pure (.typed (← str a) (← str b))
  | "double" => do let n ← nat v; pure (.double ⟨n.toUInt64⟩)
  | "decimal" => .decimal <$> str v
  | _ => none

def errCode : CodecError → String
  | .unsupported _ => "Unsupported"
  | .invalidTerm _ => "InvalidTerm"
  | .idSpaceExhausted _ => "IdSpaceExhausted"

def codecErrJ (e : CodecError) : Json := .obj #[("err", .str (errCode e)), ("message", .str (toString e))]

def encodedJ : Except CodecError Encoded → Json
  | .ok (.inline x) => .obj #[("inline", .int x.raw.toInt)]
  | .ok (.term t) => .obj #[("term", .arr #[.int t.tag.toNat, .str t.lex, optMapJ .str t.datatype,
      optMapJ .str t.lang, optMapJ (fun b => .int b.toNat) t.num])]
  | .error e => codecErrJ e

end Tiramemsu.Shell
