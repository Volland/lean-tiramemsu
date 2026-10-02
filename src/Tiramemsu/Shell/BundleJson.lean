/-
The JSON form `tiramemsu-bundle/1` of a fact bundle, written as Rust's `serde_json` writes it
(compact, object keys in sorted order) and read back strictly (another format string or a
malformed statement is `InvalidTerm`; a read bundle passes the structural check).
Shell module (unverified; tested by round trips and byte comparison with the Rust oracle).
-/
import Tiramemsu.Bundle.Import
import Tiramemsu.Shell.Json

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.Bundle Tiramemsu.Codec Tiramemsu.Engine

--# @lat: [[query#Fact Bundles#Bundle JSON]]

def bundleFormat : String := "tiramemsu-bundle/1"

/-- A JSON string as `serde_json` escapes it. -/
def serdeQuote (s : String) : String :=
  let hex (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  "\"" ++ s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | '\x08' => acc ++ "\\b"
    | '\x0C' => acc ++ "\\f"
    | c => if c.toNat < 0x20 then acc ++ "\\u00" ++ String.ofList [hex (c.toNat / 16), hex (c.toNat % 16)] else acc.push c) "" ++ "\""

/-- Compact JSON with sorted object keys (`serde_json` without `preserve_order`). -/
partial def sortedText : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int i => toString i
  | .num l => l
  | .str s => serdeQuote s
  | .arr xs => "[" ++ ",".intercalate (xs.map sortedText).toList ++ "]"
  | .obj kvs =>
    let sorted := kvs.toList.mergeSort fun a b => decide (a.1 ≤ b.1)
    "{" ++ ",".intercalate (sorted.map fun (k, v) => serdeQuote k ++ ":" ++ sortedText v) ++ "}"

def bundleTermJ : BTerm → Json
  | .stmt r => .obj #[("ref", .int r)]
  | .node n => .obj #[("blank", .int n)]
  | .value (.langStr lex lang) => .obj #[("lex", .str lex), ("lang", .str lang)]
  | .value v => match v.datatype with
    | some dt => .obj #[("lex", .str v.lexical), ("datatype", .str dt)]
    | none => .obj #[("iri", .str v.lexical)]

def bundleStmtJ (st : BStmt) : Json :=
  .obj (#[("id", .int st.local_), ("s", bundleTermJ st.s),
          ("p", .str (match st.p with | .iri p => p | other => other.lexical)), ("o", bundleTermJ st.o)] ++
        (match st.vFrom with | some f => #[("validFrom", .int f.toInt)] | none => #[]) ++
        (match st.vTo with | some t => #[("validTo", .int t.toInt)] | none => #[]))

/-- The JSON value of a bundle. -/
def _root_.Tiramemsu.Bundle.Bundle.toJsonValue (b : Bundle) : Json :=
  .obj #[("format", .str bundleFormat), ("root", .int b.root), ("statements", .arr (b.statements.map bundleStmtJ).toArray)]

/-- The JSON text of a bundle (byte-identical to the Rust build). -/
def _root_.Tiramemsu.Bundle.Bundle.toJson (b : Bundle) : String := sortedText b.toJsonValue

def bundleBad {α : Type} (reason : String) : Except Error α := .error (.invalidTerm .value s!"bundle JSON: {reason}")

def bundleU32? (j : Json) : Option Nat := match j with
  | .int i => if 0 ≤ i ∧ i < 2 ^ 32 then some i.toNat else none
  | _ => none

def bundleTermOfJ (j : Json) (what : String) : Except Error BTerm := do
  let .obj _ := j | bundleBad s!"{what} is not a term object"
  if let some r := j.get? "ref" then
    match bundleU32? r with
    | some n => return .stmt n
    | none => bundleBad s!"{what}.ref is not a 32-bit id"
  if let some n := j.get? "blank" then
    match bundleU32? n with
    | some k => return .node k
    | none => bundleBad s!"{what}.blank is not a 32-bit id"
  if let some iri := j.getStr? "iri" then return .value (Value.iri iri).canonical
  if let some lex := j.getStr? "lex" then
    match j.getStr? "lang", j.getStr? "datatype" with
    | some lang, none => return .value (literal lex none (some lang))
    | none, some dt => return .value (literal lex (some dt) none)
    | _, _ => bundleBad s!"{what} needs exactly one of datatype and lang"
  bundleBad s!"{what} is not a term"

def bundleStmtOfJ (j : Json) (k : Nat) : Except Error BStmt := do
  let what := s!"statements[{k}]"
  let .obj _ := j | bundleBad s!"{what} is not an object"
  let some l := (j.get? "id").bind bundleU32? | bundleBad s!"{what}.id is not a 32-bit id"
  let some p := j.getStr? "p" | bundleBad s!"{what}.p is not an IRI string"
  let some s := j.get? "s" | bundleBad s!"{what}.s is missing"
  let some o := j.get? "o" | bundleBad s!"{what}.o is missing"
  let time (f : String) : Except Error (Option Int64) :=
    match j.get? f with
    | none | some .null => .ok none
    | some (.int i) => .ok (some (Int64.ofInt i))
    | some _ => bundleBad s!"{what}.{f} is not epoch milliseconds"
  return { local_ := l, s := ← bundleTermOfJ s s!"{what}.s", p := (Value.iri p).canonical,
           o := ← bundleTermOfJ o s!"{what}.o", vFrom := ← time "validFrom", vTo := ← time "validTo" }

/-- Reads the JSON form of a bundle. -/
def _root_.Tiramemsu.Bundle.Bundle.fromJsonValue (j : Json) : Except Error Bundle := do
  match j.getStr? "format" with
  | some f => if f != bundleFormat then bundleBad s!"unknown format \"{f}\""
  | none => bundleBad "`format` is missing"
  let some root := (j.get? "root").bind bundleU32? | bundleBad "`root` is not a 32-bit id"
  let some sts := j.getArr? "statements" | bundleBad "`statements` is not a list"
  let statements ← sts.toList.zipIdx.mapM fun (s, k) => bundleStmtOfJ s k
  let b : Bundle := { root, statements }
  b.check
  return b

def _root_.Tiramemsu.Bundle.Bundle.fromJson (text : String) : Except Error Bundle :=
  match Json.parse text with
  | .ok j => Bundle.fromJsonValue j
  | .error e => bundleBad s!"not JSON: {e}"

end Tiramemsu.Shell
