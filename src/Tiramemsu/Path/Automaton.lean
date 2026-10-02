/-
Path automata. An expression resolves to a regular expression over letter sets (inverse pushed
to the atoms, `+`, `?` and `{m,n}` unrolled) and compiles to a deterministic automaton over a
refined alphabet of letter classes by Brzozowski derivatives on normalized expressions (each
state is a normalized derivative). Every hop sequence has exactly one run, so an ambiguous
expression never produces a path twice. More than 4 096 states is `Unsupported`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Std.Data.HashMap
import Tiramemsu.IR.Types

namespace Tiramemsu.Path

open Tiramemsu.IR

--# @lat: [[query#Paths#Automaton]]

/-- A hop direction: along the statement (`out`) or against it (`inn`). -/
inductive Dir where
  | out | inn
  deriving Repr, DecidableEq, Inhabited, Hashable

def Dir.flip : Dir → Dir
  | .out => .inn
  | .inn => .out

def Dir.code : Dir → Nat
  | .out => 0
  | .inn => 1

/-- The virtual layer hops. Their codes are Rust's hop kinds (stored is 0). -/
inductive VKind where
  | subject | object | predicate
  deriving Repr, DecidableEq, Inhabited, Hashable

def VKind.code : VKind → Nat
  | .subject => 1 | .object => 2 | .predicate => 3

/-- The letters an atom matches. -/
inductive Cls where
  /-- One stored predicate (by IRI; an IRI that is not stored matches nothing). -/
  | pred (iri : String) (d : Dir)
  /-- The wildcard: every stored relationship statement. -/
  | anyRel (d : Dir)
  | virt (k : VKind) (d : Dir)
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- A concrete hop letter: a stored statement's predicate and whether it is a relationship, or a
virtual hop; with its direction. -/
inductive Letter where
  | stored (iri : String) (rel : Bool) (d : Dir)
  | virt (k : VKind) (d : Dir)
  deriving Repr, DecidableEq, Inhabited

def Cls.matches : Cls → Letter → Bool
  | .pred p d, .stored p' _ d' => p == p' && d == d'
  | .anyRel d, .stored _ rel d' => rel && d == d'
  | .virt k d, .virt k' d' => k == k' && d == d'
  | _, _ => false

/-- A regular expression over letter sets. -/
inductive RE where
  | empty
  | eps
  | sym (c : Cls)
  | seq (a b : RE)
  | alt (a b : RE)
  | star (a : RE)
  deriving Repr, DecidableEq, Inhabited, Hashable

def RE.size : RE → Nat
  | .empty | .eps | .sym _ => 1
  | .seq a b | .alt a b => a.size + b.size + 1
  | .star a => a.size + 1

/-! ## From path expressions -/

/-- The letter set of an atom IRI. -/
def atomCls (iri : String) (d : Dir) : Cls :=
  if iri == QVocab.sysSubject then .virt .subject d
  else if iri == QVocab.sysObject then .virt .object d
  else if iri == QVocab.sysPredicate then .virt .predicate d
  else if iri == QVocab.sysAnyRelationship then .anyRel d
  else .pred iri d

def RE.seqs : List RE → RE
  | [] => .eps
  | [a] => a
  | a :: rest => .seq a (RE.seqs rest)

def RE.alts : List RE → RE
  | [] => .empty
  | [a] => a
  | a :: rest => .alt a (RE.alts rest)

/-- `a{n}`. -/
def RE.pow (a : RE) : Nat → RE
  | 0 => .eps
  | n + 1 => .seq a (a.pow n)

/-- At most `n` more copies: `(a (a …)?)?`. -/
def RE.upTo (a : RE) : Nat → RE
  | 0 => .eps
  | n + 1 => .alt .eps (.seq a (a.upTo n))

/-- The expression with inversion pushed to its atoms (`inv`: read backwards). -/
def toRE (inv : Bool) : PathExpr → RE
  | .atom iri => .sym (atomCls iri (if inv then .inn else .out))
  | .inv e => toRE (!inv) e
  | .seq es =>
    let xs := es.attach.map fun ⟨e, _⟩ => toRE inv e
    RE.seqs (if inv then xs.reverse else xs)
  | .alt es => RE.alts (es.attach.map fun ⟨e, _⟩ => toRE inv e)
  | .star e => .star (toRE inv e)
  | .plus e => let a := toRE inv e; .seq a (.star a)
  | .opt e => .alt .eps (toRE inv e)
  | .rep e lo hi =>
    let a := toRE inv e
    .seq (a.pow lo) (match hi with
      | none => .star a
      | some h => a.upTo (h - lo))

/-! ## Normalization and derivatives -/

def RE.key (r : RE) : String := reprStr r

def RE.isEmpty : RE → Bool
  | .empty => true
  | _ => false

def mkSeq : RE → RE → RE
  | .empty, _ => .empty
  | _, .empty => .empty
  | .eps, b => b
  | a, .eps => a
  | .seq a b, c => .seq a (.seq b c)
  | a, b => .seq a b

/-- The alternatives of an expression. -/
def RE.altsOf : RE → List RE
  | .alt a b => a.altsOf ++ b.altsOf
  | .empty => []
  | r => [r]

/-- Union with flattening, deduplication and a canonical order (so states are normalized modulo
associativity, commutativity and idempotence). -/
def mkAlt (a b : RE) : RE :=
  let xs := (a.altsOf ++ b.altsOf).eraseDups
  RE.alts (xs.mergeSort fun x y => decide (x.key ≤ y.key))

def mkStar : RE → RE
  | .empty | .eps => .eps
  | .star a => .star a
  | a => .star a

def RE.nullable : RE → Bool
  | .empty | .sym _ => false
  | .eps | .star _ => true
  | .seq a b => a.nullable && b.nullable
  | .alt a b => a.nullable || b.nullable

/-- A letter class of the refined alphabet. -/
inductive LClass where
  /-- A mentioned stored predicate; `rel` splits it when the wildcard occurs in its direction. -/
  | pred (iri : String) (d : Dir) (rel : Option Bool)
  /-- Unmentioned relationship statements (only when the wildcard occurs in the direction). -/
  | other (d : Dir)
  | virt (k : VKind) (d : Dir)
  deriving Repr, DecidableEq, Inhabited

def Cls.matchesClass : Cls → LClass → Bool
  | .pred p d, .pred p' d' _ => p == p' && d == d'
  | .anyRel d, .pred _ d' (some true) => d == d'
  | .anyRel d, .other d' => d == d'
  | .virt k d, .virt k' d' => k == k' && d == d'
  | _, _ => false

/-- The derivative of an expression by a letter class. -/
def RE.deriv (c : LClass) : RE → RE
  | .empty | .eps => .empty
  | .sym s => if s.matchesClass c then .eps else .empty
  | .seq a b =>
    let d1 := mkSeq (a.deriv c) b
    if a.nullable then mkAlt d1 (b.deriv c) else d1
  | .alt a b => mkAlt (a.deriv c) (b.deriv c)
  | .star a => mkSeq (a.deriv c) (mkStar a)

/-- Normalization (applied once to the start state). -/
def RE.norm : RE → RE
  | .seq a b => mkSeq a.norm b.norm
  | .alt a b => mkAlt a.norm b.norm
  | .star a => mkStar a.norm
  | r => r

/-! ## The alphabet -/

def RE.syms : RE → List Cls
  | .sym c => [c]
  | .seq a b | .alt a b => a.syms ++ b.syms
  | .star a => a.syms
  | _ => []

def predOf (d : Dir) : Cls → Option String
  | .pred p d' => if d' == d then some p else none
  | _ => none

def virtOf (d : Dir) : Cls → Option VKind
  | .virt k d' => if d' == d then some k else none
  | _ => none

/-- The classes of one direction: each mentioned predicate (split by the relationship view when
the wildcard occurs), the wildcard's other relationships, and the virtual hops. -/
def alphabetDir (ss : List Cls) (d : Dir) : List LClass :=
  let any := ss.contains (.anyRel d)
  let preds := (ss.filterMap (predOf d)).eraseDups
  let virts := (ss.filterMap (virtOf d)).eraseDups
  preds.flatMap (fun p => if any then [.pred p d (some true), .pred p d (some false)] else [.pred p d none]) ++
    (if any then [.other d] else []) ++ virts.map (.virt · d)

/-- The refined alphabet of an expression. -/
def alphabet (r : RE) : List LClass :=
  [Dir.out, Dir.inn].flatMap (alphabetDir r.syms)

/-- The class of a concrete letter (`none`: no atom matches it). -/
def classOf (alpha : List LClass) : Letter → Option LClass
  | .stored p rel d =>
    if alpha.contains (.pred p d none) then some (.pred p d none)
    else if alpha.contains (.pred p d (some rel)) then some (.pred p d (some rel))
    else if rel && alpha.contains (.other d) then some (.other d)
    else none
  | .virt k d => if alpha.contains (.virt k d) then some (.virt k d) else none

/-! ## The deterministic automaton -/

/-- A compiled automaton: states (normalized derivatives), the live transitions of each state
by class index, and acceptance. State 0 is the start. -/
structure Dfa where
  alpha : Array LClass
  states : Array RE
  trans : Array (List (Nat × Nat))
  accepting : Array Bool
  deriving Inhabited

def maxDfaStates : Nat := 4096
def maxExprSize : Nat := 200000

/-- The transitions of one state: for each class (with its index) whose derivative is not
`empty`, the index of that derivative, adding it as a new state when it is not one yet. -/
def addRow (r : RE) : List (LClass × Nat) → Array RE × Std.HashMap RE Nat × List (Nat × Nat) →
    Array RE × Std.HashMap RE Nat × List (Nat × Nat)
  | [], acc => acc
  | (c, ci) :: rest, (states, index, row) =>
    let d := r.deriv c
    if d.isEmpty then addRow r rest (states, index, row)
    else match index.get? d with
      | some j => addRow r rest (states, index, row ++ [(ci, j)])
      | none => addRow r rest (states.push d, index.insert d states.size, row ++ [(ci, states.size)])

/-- `buildGo alpha fuel i states index trans`: states `0 … i-1` have their transitions;
explores the remaining states breadth-first and fails past the state cap. -/
def buildGo (alpha : Array LClass) : Nat → Nat → Array RE → Std.HashMap RE Nat → Array (List (Nat × Nat)) →
    Except QError Dfa
  | 0, _, _, _, _ => .error (.unsupported "path expression too complex")
  | fuel + 1, i, states, index, trans =>
    if h : i < states.size then
      let (states', index', row) := addRow states[i] alpha.toList.zipIdx (states, index, [])
      if states'.size > maxDfaStates then .error (.unsupported "path expression too complex")
      else buildGo alpha fuel (i + 1) states' index' (trans.push row)
    else .ok { alpha, states, trans, accepting := states.map RE.nullable }

/-- Subset-free construction: explores derivatives breadth-first; fails past the state cap. -/
def buildDfa (r0 : RE) : Except QError Dfa :=
  let r := r0.norm
  if r0.size > maxExprSize then .error (.unsupported "path expression too complex")
  else buildGo (alphabet r0).toArray (maxDfaStates + 1) 0 #[r] ((∅ : Std.HashMap RE Nat).insert r 0) #[]

def Dfa.step (d : Dfa) (q ci : Nat) : Option Nat :=
  ((d.trans.getD q []).find? (·.1 == ci)).map (·.2)

def Dfa.accepts (d : Dfa) (q : Nat) : Bool := d.accepting.getD q false

end Tiramemsu.Path
