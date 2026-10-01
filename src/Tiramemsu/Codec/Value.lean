/-
Values as they cross the API, literal classification and canonicalization, following the Rust
`Value` (`literal`, `canonical`, `lexical`, `datatype`). Every value has one canonical form, so
it has one ObjectId. Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Codec.Integer
import Tiramemsu.Codec.Decimal
import Tiramemsu.Codec.DateTime
import Tiramemsu.Codec.Double.Print
import Tiramemsu.Codec.Skolem

namespace Tiramemsu.Codec

--# @lat: [[codec#Literals]]

/-! ## Vocabulary -/

abbrev xsdNs : String := "http://www.w3.org/2001/XMLSchema#"
abbrev xsdInteger : String := "http://www.w3.org/2001/XMLSchema#integer"
abbrev xsdBoolean : String := "http://www.w3.org/2001/XMLSchema#boolean"
abbrev xsdString : String := "http://www.w3.org/2001/XMLSchema#string"
abbrev xsdDate : String := "http://www.w3.org/2001/XMLSchema#date"
abbrev xsdDateTime : String := "http://www.w3.org/2001/XMLSchema#dateTime"
abbrev xsdDouble : String := "http://www.w3.org/2001/XMLSchema#double"
abbrev xsdDecimal : String := "http://www.w3.org/2001/XMLSchema#decimal"
abbrev rdfLangString : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"

/-! ## Values -/

/-- A value in any statement position. -/
inductive Value where
  | iri (s : String)
  | node (n : Nat)
  | bnode (n : Nat)
  | stmt (n : Nat)
  | tx (n : Nat)
  /-- Unbounded: outside the `INT` range it canonicalizes to `TYPED xsd:integer`. -/
  | int (i : Int)
  | bool (b : Bool)
  /-- Epoch milliseconds and an optional offset in minutes. -/
  | dateTime (ms : Int) (tz : Option Int)
  /-- Days since 1970-01-01. -/
  | date (d : Int)
  | str (s : String)
  | langStr (lex lang : String)
  | typed (lex dt : String)
  | double (x : Double64)
  /-- A decimal, as its lexical form. -/
  | decimal (s : String)
  deriving Repr, DecidableEq, Inhabited

/-- The value of an allocated tag and counter. -/
def Value.ofAlloc : AllocTag → Nat → Value
  | .node, n => .node n
  | .bnode, n => .bnode n
  | .stmt, n => .stmt n
  | .tx, n => .tx n

/-- ASCII lower-casing (Rust's `to_ascii_lowercase`). -/
def asciiLower (s : String) : String := s.map Char.toLower

/-- An integer given as decimal text: `INT` in range, else `TYPED xsd:integer` with the
canonical decimal; ill-typed text stays verbatim. -/
def bigInteger (lex : String) : Value :=
  match parseIntLex lex with
  | some i => if inIntRange i then .int i else .typed (intText i) xsdInteger
  | none => .typed lex xsdInteger

/-- The canonical value of an RDF literal `(lex, datatype, lang)`. -/
def literal (lex : String) (dt : Option String) (lang : Option String) : Value :=
  match lang with
  | some l => .langStr lex (asciiLower l)
  | none =>
    match dt with
    | none => .str lex
    | some d =>
      if d == xsdString then .str lex
      else if d == xsdInteger then bigInteger lex
      else if d == xsdBoolean then
        if lex == "true" || lex == "1" then .bool true
        else if lex == "false" || lex == "0" then .bool false
        else .typed lex d
      else if d == xsdDateTime then
        match parseDateTime lex with
        | some (ms, tz) => if dtInRange ms && tzValid tz then .dateTime ms tz else .typed lex d
        | none => .typed lex d
      else if d == xsdDate then
        match parseDate lex with
        | some days => if inIntRange days then .date days else .typed lex d
        | none => .typed lex d
      else if d == xsdDouble then
        match parseDouble lex with
        | some x => .double x
        | none => .typed lex d
      else if d == xsdDecimal then
        match canonDecimal lex with
        | some c => .decimal c
        | none => .typed lex d
      else .typed lex d

namespace Value

/-- The canonical form of a value (the value its ObjectId decodes to). -/
def canonical : Value → Value
  | .iri s => match skolemValue? s with
    | some (k, n) => .ofAlloc k n
    | none => .iri s
  | .int i => if inIntRange i then .int i else .typed (intText i) xsdInteger
  | .dateTime ms tz =>
    if dtInRange ms && tzValid tz then .dateTime ms tz
    else .typed (formatDateTime ms tz) xsdDateTime
  | .date d => if inIntRange d then .date d else .typed (formatDate d) xsdDate
  | .langStr lex lang => .langStr lex (asciiLower lang)
  | .typed lex dt => literal lex (some dt) none
  | .decimal s => match canonDecimal s with
    | some c => .decimal c
    | none => .typed s xsdDecimal
  | .double x => .double x.canon
  | v => v

/-- The lexical form of a literal value (or the IRI text). -/
def lexical : Value → String
  | .iri s => s
  | .node n => renderSkolem .node n
  | .bnode n => renderSkolem .bnode n
  | .stmt n => renderSkolem .stmt n
  | .tx n => renderSkolem .tx n
  | .int i => intText i
  | .bool b => if b then "true" else "false"
  | .dateTime ms tz => formatDateTime ms tz
  | .date d => formatDate d
  | .str s => s
  | .langStr lex _ => lex
  | .typed lex _ => lex
  | .double x => printDouble x
  | .decimal s => s

/-- The datatype IRI of a literal (`none` for IRIs, nodes, statements and transactions). -/
def datatype : Value → Option String
  | .int _ => some xsdInteger
  | .bool _ => some xsdBoolean
  | .dateTime .. => some xsdDateTime
  | .date _ => some xsdDate
  | .str _ => some xsdString
  | .langStr .. => some rdfLangString
  | .typed _ dt => some dt
  | .double _ => some xsdDouble
  | .decimal _ => some xsdDecimal
  | _ => none

/-- The language tag of a language string. -/
def lang : Value → Option String
  | .langStr _ l => some l
  | _ => none

end Value

end Tiramemsu.Codec
