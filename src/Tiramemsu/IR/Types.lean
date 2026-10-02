/-
The logical IR (Tier 2): view-scoped triple and path patterns, inline values, the eight
relational operators, expressions with `EXISTS`, aggregates and sort keys, graph selectors,
match groups, semantic flags and parameters. Mirrors Rust `tm-ir` without the Cypher-only
operators (`Unnest`, `RowNumber`, `Lookup`, list expressions, null-safe join keys, volatile
pattern opt-in), which arrive with M5.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.View.Read

namespace Tiramemsu.IR

open Tiramemsu.Codec Tiramemsu.Store

--# @lat: [[query#Logical IR]]

/-- A query variable, by name without the leading `?`. -/
abbrev Var := String

/-- A pattern position, a values cell, or skip/limit: a variable, a constant value, an already
encoded ObjectId, or a named parameter. -/
inductive TermOrVar where
  | var (v : Var)
  | const (v : Value)
  | id (o : ObjectId)
  | param (n : String)
  deriving Repr, DecidableEq, Inhabited

/-- Which named graphs a pattern's statement must be a member of. -/
inductive GraphSel where
  | any
  | set (gs : List TermOrVar)
  | var (g : Var)
  deriving Repr, DecidableEq, Inhabited

/-- A comparison operator. -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- An arithmetic operator. -/
inductive ArithOp where
  | add | sub | mul | div
  deriving Repr, DecidableEq, Inhabited

/-- The SPARQL 1.1 scalar functions (Rust `tm_ir::Func`). -/
inductive Func where
  | str | lang | datatype | isIri | isLiteral | isNumeric | strLen | ucase | lcase
  | contains | strStarts | strEnds | regex | isBlank | langMatches | iri | strDt | strLang
  | substr | strBefore | strAfter | concat | encodeForUri | replace
  | abs | ceil | floor | round
  | year | month | day | hours | minutes | seconds | timezone | tz
  | castString | castInteger | castDecimal | castDouble | castBoolean | castDate | castDateTime
  deriving Repr, DecidableEq, Inhabited

namespace Func

/-- The surface name. -/
def name : Func → String
  | .str => "STR" | .lang => "LANG" | .datatype => "DATATYPE" | .isIri => "isIRI"
  | .isLiteral => "isLiteral" | .isNumeric => "isNumeric" | .strLen => "STRLEN"
  | .ucase => "UCASE" | .lcase => "LCASE" | .contains => "CONTAINS" | .strStarts => "STRSTARTS"
  | .strEnds => "STRENDS" | .regex => "REGEX" | .isBlank => "isBlank"
  | .langMatches => "LANGMATCHES" | .iri => "IRI" | .strDt => "STRDT" | .strLang => "STRLANG"
  | .substr => "SUBSTR" | .strBefore => "STRBEFORE" | .strAfter => "STRAFTER"
  | .concat => "CONCAT" | .encodeForUri => "ENCODE_FOR_URI" | .replace => "REPLACE"
  | .abs => "ABS" | .ceil => "CEIL" | .floor => "FLOOR" | .round => "ROUND"
  | .year => "YEAR" | .month => "MONTH" | .day => "DAY" | .hours => "HOURS"
  | .minutes => "MINUTES" | .seconds => "SECONDS" | .timezone => "TIMEZONE" | .tz => "TZ"
  | .castString => "xsd:string" | .castInteger => "xsd:integer" | .castDecimal => "xsd:decimal"
  | .castDouble => "xsd:double" | .castBoolean => "xsd:boolean" | .castDate => "xsd:date"
  | .castDateTime => "xsd:dateTime"

/-- The accepted numbers of arguments: `(min, max)`, `max = none` for variadic. -/
def arity : Func → Nat × Option Nat
  | .contains | .strStarts | .strEnds | .langMatches | .strDt | .strLang | .strBefore
  | .strAfter => (2, some 2)
  | .regex => (2, some 3)
  | .substr => (2, some 3)
  | .replace => (3, some 4)
  | .concat => (0, none)
  | _ => (1, some 1)

/-- Whether `n` arguments fit the arity. -/
def accepts (f : Func) (n : Nat) : Bool :=
  let (lo, hi) := f.arity
  decide (lo ≤ n) && (match hi with | none => true | some h => decide (n ≤ h))

end Func

/-- An aggregate function. -/
inductive AggFunc where
  | count | sum | avg | min | max | sample
  | groupConcat (sep : String)
  deriving Repr, DecidableEq, Inhabited

def AggFunc.name : AggFunc → String
  | .count => "count" | .sum => "sum" | .avg => "avg" | .min => "min" | .max => "max"
  | .sample => "sample" | .groupConcat _ => "group_concat"

/-- A property-path expression. Atoms are IRIs; `sys:subject`, `sys:object`, `sys:predicate`
are the virtual layer hops and `sys:anyRelationship` the wildcard. -/
inductive PathExpr where
  | atom (iri : String)
  | inv (e : PathExpr)
  | seq (es : List PathExpr)
  | alt (es : List PathExpr)
  | star (e : PathExpr)
  | plus (e : PathExpr)
  | opt (e : PathExpr)
  | rep (e : PathExpr) (lo : Nat) (hi : Option Nat)
  deriving Inhabited

/-- How a path pattern enumerates paths. -/
inductive PathMode where
  | reach | trail | anyShortest | allShortest
  deriving Repr, DecidableEq, Inhabited

namespace PathMode

def name : PathMode → String
  | .reach => "REACH" | .trail => "TRAIL" | .anyShortest => "ANY_SHORTEST"
  | .allShortest => "ALL_SHORTEST"

/-- ASCII upper-casing. -/
def upper (s : String) : String := s.map Char.toUpper

/-- Parses a mode name case-insensitively; any other name is `none`. -/
def parse? (s : String) : Option PathMode :=
  match upper s.trimAscii.toString with
  | "REACH" => some .reach
  | "TRAIL" => some .trail
  | "ANY_SHORTEST" => some .anyShortest
  | "ALL_SHORTEST" => some .allShortest
  | _ => none

/-- Whether a mode returns path values. -/
def returnsPath : PathMode → Bool
  | .reach => false
  | _ => true

end PathMode

/-- Overlays a query-level or per-pattern clause on a default view, part by part: a given
selector replaces the selector of the same kind, a missing one keeps it (front ends). -/
def overlayView (base : View.ViewSpec) (tx : Option View.TxSpec) (valid : Option ValidSel) : View.ViewSpec :=
  { tx := tx.getD base.tx, valid := valid.getD base.valid }

/-- A view-scoped triple pattern. -/
structure TriplePattern where
  s : TermOrVar
  p : TermOrVar
  o : TermOrVar
  eid : Option Var := none
  view : View.ViewSpec := {}
  isoGroup : Option Nat := none
  graph : GraphSel := .any
  deriving Repr, DecidableEq, Inhabited

/-- A path between two endpoints. Time-respecting search is reachable only through the API. -/
structure PathPattern where
  start : TermOrVar
  «end» : TermOrVar
  path : PathExpr
  mode : PathMode := .reach
  maxHops : Option Nat := none
  bindPath : Option Var := none
  view : View.ViewSpec := {}
  graph : GraphSel := .any
  deriving Inhabited

mutual

/-- A scalar expression. -/
inductive Expr where
  | var (v : Var)
  | const (v : Value)
  | param (n : String)
  | cmp (op : CmpOp) (a b : Expr)
  | sameTerm (a b : Expr)
  | and (xs : List Expr)
  | or (xs : List Expr)
  | not (a : Expr)
  | bound (v : Var)
  | inList (a : Expr) (xs : List Expr) (negated : Bool)
  | arith (op : ArithOp) (a b : Expr)
  | neg (a : Expr)
  | coalesce (xs : List Expr)
  | ite (c a b : Expr)
  | func (f : Func) (args : List Expr)
  | exists (q : Op) (negated : Bool)

/-- A logical operator. -/
inductive Op where
  | triple (t : TriplePattern)
  | path (p : PathPattern)
  | values (vs : List Var) (rows : List (List (Option TermOrVar)))
  | join (xs : List Op)
  | leftJoin (l r : Op) (c : Option Expr)
  | union (xs : List Op)
  | filter (c : Expr) (x : Op)
  | extend (v : Var) (e : Expr) (x : Op)
  | aggregate (group : List Var) (aggs : List (Var × AggFunc × Option Expr × Bool)) (x : Op)
  | project (vs : List Var) (distinct : Bool) (x : Op)
  | orderLimit (keys : List (Expr × Bool)) (skip limit : Option TermOrVar) (x : Op)

end

instance : Inhabited Expr := ⟨.const (.bool true)⟩
instance : Inhabited Op := ⟨.join []⟩

/-- One aggregate `var := func([distinct] arg)`; `arg = none` only for `COUNT(*)`. -/
structure Agg where
  var : Var
  func : AggFunc
  arg : Option Expr := none
  distinct : Bool := false
  deriving Inhabited

def Agg.toTuple (a : Agg) : Var × AggFunc × Option Expr × Bool := (a.var, a.func, a.arg, a.distinct)

/-- A sort key: an expression and whether it is descending. -/
structure Key where
  expr : Expr
  desc : Bool := false
  deriving Inhabited

/-- `Aggregate` from structured aggregates. -/
def Op.agg (group : List Var) (aggs : List Agg) (x : Op) : Op := .aggregate group (aggs.map Agg.toTuple) x

/-- `OrderLimit` from structured keys. -/
def Op.order (keys : List Key) (skip limit : Option TermOrVar) (x : Op) : Op :=
  .orderLimit (keys.map fun k => (k.expr, k.desc)) skip limit x

/-- How relationship patterns of one match group may bind statements. -/
inductive MatchMode where
  | homomorphism | relIsomorphism
  deriving Repr, DecidableEq, Inhabited

/-- How missing values behave in joins. -/
inductive Missing where
  | unbound | null3VL
  deriving Repr, DecidableEq, Inhabited

/-- Whether parallel statements count once or once per eid. -/
inductive GraphSet where
  | setOfTriples | bagOfEids
  deriving Repr, DecidableEq, Inhabited

/-- The three semantic flags of a query. -/
structure Semantics where
  matchMode : MatchMode := .homomorphism
  missing : Missing := .unbound
  graphSet : GraphSet := .setOfTriples
  deriving Repr, DecidableEq, Inhabited

/-- SPARQL: `(Homomorphism, Unbound, SetOfTriples)`. -/
def Semantics.sparql : Semantics := { matchMode := .homomorphism, missing := .unbound, graphSet := .setOfTriples }

/-- Cypher: `(RelIsomorphism, Null3VL, BagOfEids)`. -/
def Semantics.cypher : Semantics := { matchMode := .relIsomorphism, missing := .null3VL, graphSet := .bagOfEids }

/-- A query: an operator tree and its flags. -/
structure Query where
  root : Op
  sem : Semantics := .sparql
  deriving Inhabited

/-- Named parameter values (`$name ↦ value`). -/
abbrev Params := List (String × Value)

def Params.get? (ps : Params) (n : String) : Option Value := (ps.find? (·.1 == n)).map (·.2)

/-- Every failure of the query core. -/
inductive QError where
  | invalidQuery (msg : String)
  | unsupported (msg : String)
  /-- `dialect` is `Path` (later `SPARQL`/`Cypher`); `lo, hi` a byte span. -/
  | parse (dialect : String) (lo hi : Nat) (msg : String)
  | pathLimitExceeded (limit : Nat)
  | invalidTerm (msg : String)
  | store (e : StoreError)
  deriving Repr, DecidableEq, Inhabited

def QError.code : QError → String
  | .invalidQuery _ => "InvalidQuery"
  | .unsupported _ => "Unsupported"
  | .parse .. => "Parse"
  | .pathLimitExceeded _ => "PathLimitExceeded"
  | .invalidTerm _ => "InvalidTerm"
  | .store _ => "Sqlite"

instance : ToString QError where
  toString
    | .invalidQuery m => s!"invalid query: {m}"
    | .unsupported m => s!"unsupported: {m}"
    | .parse d lo hi m => s!"{d} parse error at {lo}..{hi}: {m}"
    | .pathLimitExceeded l => s!"path search exceeded {l} states"
    | .invalidTerm m => s!"invalid term: {m}"
    | .store e => s!"sqlite: {e}"

/-- The failures a leaf of the semantics can raise (no `InvalidQuery`: structural problems are
caught by validation). -/
inductive LErr where
  | unsupported (msg : String)
  | parse (dialect : String) (lo hi : Nat) (msg : String)
  | pathLimitExceeded (limit : Nat)
  | invalidTerm (msg : String)
  | store (e : StoreError)
  deriving Repr, DecidableEq, Inhabited

def LErr.toQ : LErr → QError
  | .unsupported m => .unsupported m
  | .parse d lo hi m => .parse d lo hi m
  | .pathLimitExceeded l => .pathLimitExceeded l
  | .invalidTerm m => .invalidTerm m
  | .store e => .store e

/-- A leaf result as a query result. -/
def liftL {α : Type} : Except LErr α → Except QError α
  | .ok a => .ok a
  | .error e => .error e.toQ

def QError.isInvalidQuery : QError → Bool
  | .invalidQuery _ => true
  | _ => false

/-! ## Vocabulary of the query core -/

namespace QVocab

open Tiramemsu.Engine in
def sysSubject : String := Vocab.sys ++ "subject"
open Tiramemsu.Engine in
def sysPredicate : String := Vocab.sys ++ "predicate"
open Tiramemsu.Engine in
def sysObject : String := Vocab.sys ++ "object"
open Tiramemsu.Engine in
def sysAnyRelationship : String := Vocab.sys ++ "anyRelationship"
open Tiramemsu.Engine in
def tmTxAdded : String := Vocab.tm ++ "txAdded"
open Tiramemsu.Engine in
def tmTxRetracted : String := Vocab.tm ++ "txRetracted"
open Tiramemsu.Engine in
def tmAddedAt : String := Vocab.tm ++ "addedAt"
open Tiramemsu.Engine in
def tmRetractedAt : String := Vocab.tm ++ "retractedAt"
open Tiramemsu.Engine in
def tmValidFrom : String := Vocab.tm ++ "validFrom"
open Tiramemsu.Engine in
def tmValidTo : String := Vocab.tm ++ "validTo"
open Tiramemsu.Engine in
def tmRetractKind : String := Vocab.tm ++ "retractKind"

end QVocab

/-- A virtual predicate: computed from the statement row, never stored. -/
inductive VirtualPred where
  | subject | predicate | object
  | txAdded | txRetracted | addedAt | retractedAt | validFrom | validTo | retractKind
  deriving Repr, DecidableEq, Inhabited

def VirtualPred.ofIri? (iri : String) : Option VirtualPred :=
  if iri == QVocab.sysSubject then some .subject
  else if iri == QVocab.sysPredicate then some .predicate
  else if iri == QVocab.sysObject then some .object
  else if iri == QVocab.tmTxAdded then some .txAdded
  else if iri == QVocab.tmTxRetracted then some .txRetracted
  else if iri == QVocab.tmAddedAt then some .addedAt
  else if iri == QVocab.tmRetractedAt then some .retractedAt
  else if iri == QVocab.tmValidFrom then some .validFrom
  else if iri == QVocab.tmValidTo then some .validTo
  else if iri == QVocab.tmRetractKind then some .retractKind
  else none

/-- The virtual predicate of a pattern's predicate position, if it is a constant one. -/
def TermOrVar.virtual? : TermOrVar → Option VirtualPred
  | .const (.iri s) => VirtualPred.ofIri? s
  | _ => none

end Tiramemsu.IR
