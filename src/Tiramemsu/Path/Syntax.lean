/-
Path text: SPARQL 1.1 property-path syntax (precedence `|` < `/` < `^` < postfix) plus `{m,n}`,
`{m,}` and `{n}`, as Rust `tm-exec/path/syntax.rs`. Atoms are `<iri>`, CURIEs (`sys:`, `tm:`,
`rdf:`, `xsd:` built in; `v:`, `rdfs:` and declared prefixes through the database vocabulary) and
bare names resolved through `@vocab`. The parser first produces raw atoms with their byte
offsets; resolution reads the vocabulary only when the text needs it. Errors are `Parse` of
dialect `Path` with a byte offset; a negated property set is `Unsupported`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.IR.Types

namespace Tiramemsu.Path

open Tiramemsu.IR Tiramemsu.Engine

--# @lat: [[query#Paths#Path Text]]

/-- The database vocabulary: the `@vocab` base and declared prefixes. -/
structure Vocab where
  vocab : String := Vocab.v
  prefixes : List (String × String) := []
  deriving Repr, Inhabited

def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def rdfsNs : String := "http://www.w3.org/2000/01/rdf-schema#"
def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"

/-- The base IRI of a prefix name. -/
def Vocab.prefixIri (vc : Path.Vocab) (name : String) : Option String :=
  if name == "sys" then some Engine.Vocab.sys
  else if name == "tm" then some Engine.Vocab.tm
  else if name == "rdf" then some rdfNs
  else if name == "rdfs" then some rdfsNs
  else if name == "xsd" then some xsdNs
  else if name == "v" then some vc.vocab
  else (vc.prefixes.find? (·.1 == name)).map (·.2)

def hexByte (b : Nat) : String :=
  let d := "0123456789ABCDEF".toList
  String.ofList ['%', d.getD (b / 16) '0', d.getD (b % 16) '0']

/-- Percent-encodes the characters an IRI cannot hold (Rust `pct_encode`). -/
def pctEncode (s : String) : String :=
  s.foldl (fun acc ch =>
    let bad := ch.toNat < 128 && (ch.toNat < 32 || ch.toNat == 127 ||
      " \"<>\\^`{|}%".toList.contains ch)
    if bad then (String.singleton ch).toUTF8.toList.foldl (fun a b => a ++ hexByte b.toNat) acc
    else acc.push ch) ""

/-- A parsed atom before vocabulary resolution, with its byte offset. -/
inductive RawAtom where
  | iri (s : String)
  | curie (pre local_ : String) (at_ : Nat)
  | bare (word : String) (at_ : Nat)
  deriving Repr, Inhabited

/-- A parsed expression over raw atoms. -/
inductive RawPath where
  | atom (a : RawAtom)
  | inv (e : RawPath)
  | seq (es : List RawPath)
  | alt (es : List RawPath)
  | star (e : RawPath)
  | plus (e : RawPath)
  | opt (e : RawPath)
  | rep (e : RawPath) (lo : Nat) (hi : Option Nat)
  deriving Inhabited

def parseErr {α : Type} (at_ : Nat) (msg : String) : Except QError α :=
  .error (.parse "Path" at_ at_ msg)

/-- Parser state: the remaining characters and the byte offset of the first one. -/
structure PState where
  rest : List Char
  pos : Nat

def PState.adv (s : PState) : PState :=
  match s.rest with
  | [] => s
  | c :: cs => { rest := cs, pos := s.pos + c.utf8Size }

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

def PState.ws : PState → PState
  | { rest := c :: cs, pos } => if isWs c then PState.ws { rest := cs, pos := pos + c.utf8Size } else { rest := c :: cs, pos }
  | s => s
termination_by s => s.rest.length

def PState.peek (s : PState) : Option Char := (s.ws).rest.head?

def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '%' || c.toNat ≥ 0x80

/-- Takes characters while `p` holds. -/
def takeWhileP (p : Char → Bool) (s : PState) : String × PState :=
  let taken := s.rest.takeWhile p
  (String.ofList taken, { rest := s.rest.drop taken.length, pos := s.pos + (taken.map Char.utf8Size).sum })

def parseNum (s : PState) : Except QError (Nat × PState) :=
  let s := s.ws
  let (d, s') := takeWhileP Char.isDigit s
  match d.toNat? with
  | some n => .ok (n, s')
  | none => parseErr s.pos "expected a number"

/-- The parser, with fuel bounded by the text length (every step consumes a character). -/
def parseAlt : Nat → PState → Except QError (RawPath × PState)
  | 0, s => parseErr s.pos "expression nested too deeply"
  | fuel + 1, s => do
    let (x, s) ← parseSeq fuel s
    let rec more : Nat → List RawPath → PState → Except QError (List RawPath × PState)
      | 0, acc, s => .ok (acc, s)
      | f + 1, acc, s =>
        if s.peek == some '|' then do
          let (y, s') ← parseSeq fuel s.ws.adv
          more f (acc ++ [y]) s'
        else .ok (acc, s)
    let (xs, s) ← more (s.rest.length + 1) [x] s
    return (if xs.length == 1 then x else .alt xs, s)
where
  parseSeq : Nat → PState → Except QError (RawPath × PState)
    | 0, s => parseErr s.pos "expression nested too deeply"
    | fuel + 1, s => do
      let (x, s) ← parseUnary fuel s
      let rec more : Nat → List RawPath → PState → Except QError (List RawPath × PState)
        | 0, acc, s => .ok (acc, s)
        | f + 1, acc, s =>
          if s.peek == some '/' then do
            let (y, s') ← parseUnary fuel s.ws.adv
            more f (acc ++ [y]) s'
          else .ok (acc, s)
      let (xs, s) ← more (s.rest.length + 1) [x] s
      return (if xs.length == 1 then x else .seq xs, s)
  parseUnary : Nat → PState → Except QError (RawPath × PState)
    | 0, s => parseErr s.pos "expression nested too deeply"
    | fuel + 1, s =>
      if s.peek == some '^' then do
        let (x, s') ← parseUnary fuel s.ws.adv
        return (.inv x, s')
      else parseElt fuel s
  parseElt : Nat → PState → Except QError (RawPath × PState)
    | 0, s => parseErr s.pos "expression nested too deeply"
    | fuel + 1, s => do
      let (p, s) ← parsePrimary fuel s
      let rec post : Nat → RawPath → PState → Except QError (RawPath × PState)
        | 0, p, s => .ok (p, s)
        | f + 1, p, s =>
          match s.peek with
          | some '*' => post f (.star p) s.ws.adv
          | some '+' => post f (.plus p) s.ws.adv
          | some '?' => post f (.opt p) s.ws.adv
          | some '{' => do
            let at_ := s.ws.pos
            let (lo, s1) ← parseNum s.ws.adv
            let (hi, s2) ← if s1.peek == some ',' then do
                let s1' := s1.ws.adv
                if s1'.peek == some '}' then pure (none, s1')
                else do
                  let (h, s3) ← parseNum s1'
                  pure (some h, s3)
              else pure (some lo, s1)
            if s2.peek != some '}' then parseErr s2.ws.pos "expected `}`"
            else if hi.any (· < lo) then parseErr at_ s!"repetition maximum below minimum {lo}"
            else post f (.rep p lo hi) s2.ws.adv
          | _ => .ok (p, s)
      post (s.rest.length + 1) p s
  parsePrimary : Nat → PState → Except QError (RawPath × PState)
    | 0, s => parseErr s.pos "expression nested too deeply"
    | fuel + 1, s =>
      let s := s.ws
      match s.rest with
      | '(' :: _ => do
        let (e, s') ← parseAlt fuel s.adv
        if s'.peek == some ')' then .ok (e, s'.ws.adv) else parseErr s'.ws.pos "expected `)`"
      | '<' :: cs =>
        let body := cs.takeWhile (· != '>')
        if body.length == cs.length then parseErr s.pos "unterminated `<iri>`"
        else
          let s' := { rest := cs.drop (body.length + 1),
                      pos := s.pos + 1 + (body.map Char.utf8Size).sum + 1 }
          .ok (.atom (.iri (String.ofList body)), s')
      | '!' :: _ => .error (.unsupported "negated property sets in paths")
      | c :: _ =>
        if c.isAlpha || c == '_' || c.toNat ≥ 0x80 then
          let (word, s') := takeWhileP (fun c => isNameChar c || c == ':') s
          match word.splitOn ":" with
          | [w] => .ok (.atom (.bare w s.pos), s')
          | pre :: rest => .ok (.atom (.curie pre (":".intercalate rest) s.pos), s')
          | [] => .ok (.atom (.bare word s.pos), s')
        else parseErr s.pos s!"expected a predicate, found `{c}`"
      | [] => parseErr s.pos "unexpected end of path"

/-- Parses path text into raw atoms. -/
def parseRaw (text : String) : Except QError RawPath := do
  let s0 : PState := { rest := text.toList, pos := 0 }
  let (e, s) ← parseAlt (4 * text.length + 4) s0
  let s := s.ws
  match s.rest with
  | [] => .ok e
  | c :: _ => parseErr s.pos s!"unexpected `{c}`"

/-- Whether resolving the atoms needs the database vocabulary. -/
def RawAtom.needsVocab : RawAtom → Bool
  | .iri _ => false
  | .curie pre _ _ => !(pre == "sys" || pre == "tm" || pre == "rdf" || pre == "xsd")
  | .bare .. => true

def RawPath.needsVocab : RawPath → Bool
  | .atom a => a.needsVocab
  | .inv e | .star e | .plus e | .opt e | .rep e _ _ => e.needsVocab
  | .seq es | .alt es => es.attach.any fun ⟨e, _⟩ => e.needsVocab

def RawAtom.resolve (vc : Path.Vocab) : RawAtom → Except QError String
  | .iri s => .ok s
  | .curie pre l at_ => match vc.prefixIri pre with
    | some base => .ok (base ++ l)
    | none => parseErr at_ s!"unknown prefix `{pre}`"
  | .bare w _ => .ok (vc.vocab ++ pctEncode w)

def RawPath.resolve (vc : Path.Vocab) : RawPath → Except QError PathExpr
  | .atom a => do return .atom (← a.resolve vc)
  | .inv e => do return .inv (← e.resolve vc)
  | .star e => do return .star (← e.resolve vc)
  | .plus e => do return .plus (← e.resolve vc)
  | .opt e => do return .opt (← e.resolve vc)
  | .rep e lo hi => do return .rep (← e.resolve vc) lo hi
  | .seq es => do return .seq (← es.attach.mapM fun ⟨e, _⟩ => e.resolve vc)
  | .alt es => do return .alt (← es.attach.mapM fun ⟨e, _⟩ => e.resolve vc)

/-- Parses path text with a vocabulary. -/
def parse (text : String) (vc : Path.Vocab := {}) : Except QError PathExpr := do
  (← parseRaw text).resolve vc

/-! ## Printing -/

/-- Text of an expression, atoms as `<iri>`; parses back to an equal expression. -/
def PathExpr.print : PathExpr → String
  | .atom i => s!"<{i}>"
  | .inv e => "^" ++ printUnary e
  | .seq es => "/".intercalate (es.attach.map fun ⟨e, _⟩ => printSeqItem e)
  | .alt es => "|".intercalate (es.attach.map fun ⟨e, _⟩ => printAltItem e)
  | .star e => printUnary e ++ "*"
  | .plus e => printUnary e ++ "+"
  | .opt e => printUnary e ++ "?"
  | .rep e lo hi => printUnary e ++ "{" ++ toString lo ++
      (match hi with
       | some h => if h == lo then "" else "," ++ toString h
       | none => ",") ++ "}"
where
  printUnary : PathExpr → String
    | .atom i => s!"<{i}>"
    | e => "(" ++ PathExpr.print e ++ ")"
  printAltItem : PathExpr → String
    | .alt es => "(" ++ PathExpr.print (.alt es) ++ ")"
    | e => PathExpr.print e
  printSeqItem : PathExpr → String
    | .alt es => "(" ++ PathExpr.print (.alt es) ++ ")"
    | .seq es => "(" ++ PathExpr.print (.seq es) ++ ")"
    | e => PathExpr.print e

end Tiramemsu.Path
