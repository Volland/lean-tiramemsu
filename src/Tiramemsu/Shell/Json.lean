/-
A small JSON value type with a parser and printers. The runtime carries its own JSON so that it
needs no Lean compiler module (`Lean.Data.Json`). Integers are exact (`Int`); other numbers keep
their lexical form, so doubles compare by lexical form (D11). Shell module (unverified).
-/

namespace Tiramemsu.Json

/-- A JSON value. -/
inductive Json where
  | null
  | bool (b : Bool)
  | int (i : Int)
  /-- A number that is not an integer literal, kept as written. -/
  | num (lex : String)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving Repr, Inhabited, BEq

namespace Json

/-- The value of a key in an object. -/
def get? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def getStr? (j : Json) (k : String) : Option String :=
  match j.get? k with
  | some (.str s) => some s
  | _ => none

def getInt? (j : Json) (k : String) : Option Int :=
  match j.get? k with
  | some (.int i) => some i
  | _ => none

def getArr? (j : Json) (k : String) : Option (Array Json) :=
  match j.get? k with
  | some (.arr xs) => some xs
  | _ => none

def getBool? (j : Json) (k : String) : Option Bool :=
  match j.get? k with
  | some (.bool b) => some b
  | _ => none

/-! ## Printing -/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- A JSON string literal. -/
def quote (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | '\r' => out ++ "\\r"
      | '\t' => out ++ "\\t"
      | c =>
        if c.toNat < 0x20 then
          out ++ "\\u00" ++ (hexDigit (c.toNat / 16)).toString ++ (hexDigit (c.toNat % 16)).toString
        else out.push c
  out.push '"'

/-- Compact serialization, keys in stored order. -/
partial def compress : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int i => toString i
  | .num l => l
  | .str s => quote s
  | .arr xs => "[" ++ ",".intercalate (xs.map compress).toList ++ "]"
  | .obj kvs => "{" ++ ",".intercalate (kvs.map fun (k, v) => quote k ++ ":" ++ compress v).toList ++ "}"

instance : ToString Json := ⟨compress⟩

/-! ## Parsing -/

private structure P where
  s : String
  i : String.Pos.Raw

private abbrev PM := StateT P (Except String)

private def peek : PM (Option Char) := do
  let p ← get
  pure (if p.i.byteIdx < p.s.utf8ByteSize then some (p.i.get p.s) else none)

private def adv : PM Unit := modify fun p => { p with i := p.i.next p.s }

private partial def ws : PM Unit := do
  match ← peek with
  | some ' ' | some '\n' | some '\r' | some '\t' => adv; ws
  | _ => pure ()

private def expect (c : Char) : PM Unit := do
  if (← peek) == some c then adv else throw s!"expected '{c}'"

private def lit (w : String) (v : Json) : PM Json := do
  for c in w.toList do expect c
  pure v

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

private def hex4 : PM Nat := do
  let mut n := 0
  for _ in [0:4] do
    match (← peek).bind hexVal with
    | some d => adv; n := n * 16 + d
    | none => throw "bad \\u escape"
  pure n

private partial def strBody (acc : String) : PM String := do
  match ← peek with
  | none => throw "unterminated string"
  | some '"' => adv; pure acc
  | some '\\' =>
    adv
    match ← peek with
    | some '"' => adv; strBody (acc.push '"')
    | some '\\' => adv; strBody (acc.push '\\')
    | some '/' => adv; strBody (acc.push '/')
    | some 'b' => adv; strBody (acc.push '\x08')
    | some 'f' => adv; strBody (acc.push '\x0c')
    | some 'n' => adv; strBody (acc.push '\n')
    | some 'r' => adv; strBody (acc.push '\r')
    | some 't' => adv; strBody (acc.push '\t')
    | some 'u' =>
      adv
      let hi ← hex4
      if 0xD800 ≤ hi && hi < 0xDC00 then
        expect '\\'; expect 'u'
        let lo ← hex4
        let cp := 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)
        strBody (acc.push (Char.ofNat cp))
      else strBody (acc.push (Char.ofNat hi))
    | _ => throw "bad escape"
  | some c => adv; strBody (acc.push c)

private partial def numBody (acc : String) : PM String := do
  match ← peek with
  | some c =>
    if c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' then
      adv; numBody (acc.push c)
    else pure acc
  | none => pure acc

private partial def value : PM Json := do
  ws
  match ← peek with
  | some 'n' => lit "null" .null
  | some 't' => lit "true" (.bool true)
  | some 'f' => lit "false" (.bool false)
  | some '"' => adv; return .str (← strBody "")
  | some '[' =>
    adv; ws
    if (← peek) == some ']' then adv; return .arr #[]
    let mut xs := #[]
    repeat
      xs := xs.push (← value)
      ws
      match ← peek with
      | some ',' => adv
      | some ']' => adv; break
      | _ => throw "expected ',' or ']'"
    return .arr xs
  | some '{' =>
    adv; ws
    if (← peek) == some '}' then adv; return .obj #[]
    let mut kvs := #[]
    repeat
      ws
      expect '"'
      let k ← strBody ""
      ws; expect ':'
      let v ← value
      kvs := kvs.push (k, v)
      ws
      match ← peek with
      | some ',' => adv
      | some '}' => adv; break
      | _ => throw "expected ',' or '}'"
    return .obj kvs
  | some c =>
    if c.isDigit || c == '-' then
      let lexeme ← numBody ""
      if lexeme.any (fun c => c == '.' || c == 'e' || c == 'E') then return .num lexeme
      match lexeme.toInt? with
      | some i => return .int i
      | none => throw s!"bad number {lexeme}"
    else throw s!"unexpected character '{c}'"
  | none => throw "unexpected end of input"

/-- Parses one JSON document. -/
def parse (s : String) : Except String Json := do
  let (j, p) ← (do let v ← value; ws; pure v).run { s, i := 0 }
  if p.i.byteIdx < s.utf8ByteSize then throw "trailing characters" else pure j

end Json

end Tiramemsu.Json
