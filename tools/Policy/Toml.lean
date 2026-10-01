/-
A parser for the TOML subset used by the committed policy and oracle files: comments,
`[table]` and `[[array-of-tables]]` headers, `key = value` lines with dotted keys kept
literally, and values that are strings, integers, booleans or (possibly multi-line) arrays
of those. Tooling only.
-/

namespace Policy.Toml

inductive Value where
  | str (s : String)
  | int (i : Int)
  | bool (b : Bool)
  | arr (xs : Array Value)
  deriving Repr, Inhabited, BEq

/-- A table: keys in file order. -/
abbrev Table := Array (String × Value)

/-- A document: the top-level table and, per header name, the tables under it in order
(`[[x]]` adds one table per header, `[x]` a single one). -/
structure Doc where
  top : Table := #[]
  tables : Array (String × Table) := #[]
  deriving Repr, Inhabited

def Table.get? (t : Table) (k : String) : Option Value := (t.find? (·.1 == k)).map (·.2)

def Table.str? (t : Table) (k : String) : Option String :=
  match t.get? k with
  | some (.str s) => some s
  | _ => none

def Table.strs (t : Table) (k : String) : Array String :=
  match t.get? k with
  | some (.arr xs) => xs.filterMap fun | .str s => some s | _ => none
  | some (.str s) => #[s]
  | _ => #[]

/-- The tables under a header name. -/
def Doc.all (d : Doc) (name : String) : Array Table :=
  (d.tables.filter (·.1 == name)).map (·.2)

private structure St where
  cs : Array Char
  i : Nat := 0
  line : Nat := 1

private abbrev M := StateT St (Except String)

private def peek : M (Option Char) := do
  let s ← get
  pure s.cs[s.i]?

private def adv : M Unit := modify fun s =>
  { s with i := s.i + 1, line := if s.cs[s.i]? == some '\n' then s.line + 1 else s.line }

private def fail {α : Type} (msg : String) : M α := do
  throw s!"line {(← get).line}: {msg}"

/-- Skips spaces and tabs (and newlines and comments when `nl`). -/
private partial def skip (nl : Bool) : M Unit := do
  match ← peek with
  | some ' ' | some '\t' | some '\r' => adv; skip nl
  | some '\n' => if nl then adv; skip nl else pure ()
  | some '#' =>
    let rec toEol : M Unit := do
      match ← peek with
      | some '\n' | none => pure ()
      | _ => adv; toEol
    toEol; skip nl
  | _ => pure ()

private partial def bareKey (acc : String) : M String := do
  match ← peek with
  | some c =>
    if c.isAlphanum || c == '_' || c == '-' || c == '.' then adv; bareKey (acc.push c)
    else pure acc
  | none => pure acc

private partial def strBody (acc : String) : M String := do
  match ← peek with
  | none | some '\n' => fail "unterminated string"
  | some '"' => adv; pure acc
  | some '\\' =>
    adv
    match ← peek with
    | some 'n' => adv; strBody (acc.push '\n')
    | some 't' => adv; strBody (acc.push '\t')
    | some '"' => adv; strBody (acc.push '"')
    | some '\\' => adv; strBody (acc.push '\\')
    | _ => fail "unsupported escape"
  | some c => adv; strBody (acc.push c)

private partial def value : M Value := do
  match ← peek with
  | some '"' => adv; return .str (← strBody "")
  | some '[' =>
    adv
    let mut xs := #[]
    repeat
      skip true
      if (← peek) == some ']' then adv; break
      xs := xs.push (← value)
      skip true
      match ← peek with
      | some ',' => adv
      | some ']' => adv; break
      | _ => fail "expected ',' or ']'"
    return .arr xs
  | some _ =>
    let w ← bareKey ""
    if w == "true" then return .bool true
    if w == "false" then return .bool false
    match w.toInt? with
    | some i => return .int i
    | none => fail s!"unsupported value '{w}'"
  | none => fail "missing value"

/-- Parses a document. -/
partial def parse (text : String) : Except String Doc := do
  let rec go (d : Doc) (cur : Option (String × Table)) : M Doc := do
    skip true
    let flush (d : Doc) : Doc := match cur with
      | some t => { d with tables := d.tables.push t }
      | none => d
    match ← peek with
    | none => pure (flush d)
    | some '[' =>
      adv
      let arrayHeader := (← peek) == some '['
      if arrayHeader then adv
      skip false
      let name ← bareKey ""
      skip false
      if (← peek) != some ']' then fail "expected ']'"
      adv
      if arrayHeader then
        if (← peek) != some ']' then fail "expected ']]'"
        adv
      go (flush d) (some (name, #[]))
    | some _ =>
      let k ← if (← peek) == some '"' then (do adv; strBody "") else bareKey ""
      if k.isEmpty then fail "expected a key"
      skip false
      if (← peek) != some '=' then fail "expected '='"
      adv; skip false
      let v ← value
      match cur with
      | some (n, t) => go d (some (n, t.push (k, v)))
      | none => go { d with top := d.top.push (k, v) } none
  let (d, _) ← (go {} none).run { cs := text.toList.toArray }
  pure d

end Policy.Toml
