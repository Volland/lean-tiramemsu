/-
Rows and bags of the reference semantics.

A row is positional over the query's variable table: cell `i` is the value of variable `i`, or
`none` when it is unbound (NULL under `Null3VL`). All rows of one evaluation have the width of
the table, so merging and compatibility are pointwise. A bag is a list read up to permutation.
A schema marks the variables an operator can bind (its possible variables); it decides
compatibility under `Null3VL`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Sem.Value

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[query#Reference Semantics#Rows And Bags]]

/-- A row: one optional value per variable of the table. -/
abbrev Row := List (Option Value)

/-- A bag of rows (equality up to permutation). -/
abbrev Bag := List Row

/-- The possible variables of an operator, positionally. -/
abbrev Schema := List Bool

def Row.empty (n : Nat) : Row := List.replicate n none

def Row.get (r : Row) (i : Nat) : Option Value := (r[i]?).join

/-- Sets cell `i`, padding a shorter row with unbound cells. -/
def Row.setAt (r : Row) (i : Nat) (v : Option Value) : Row :=
  if i < r.length then r.set i v else r ++ List.replicate (i - r.length) none ++ [v]

/-- Compatibility of two cells with schema bits `p`, `q`. Under `Null3VL` a variable both
inputs can bind joins only when both rows bind it to equal values; a bound cell counts as
bindable by its input. -/
def cellCompat (m : Missing) (p q : Bool) : Option Value → Option Value → Bool
  | some a, some b => a == b
  | a, b => m == .unbound || !((p || a.isSome) && (q || b.isSome))

/-- Pointwise compatibility of two rows under schemas `P`, `Q` (missing cells are unbound,
missing schema bits false). -/
def compat (m : Missing) (P Q : Schema) (a b : Row) : Bool :=
  (List.range (max (max P.length Q.length) (max a.length b.length))).all fun i =>
    cellCompat m (P.getD i false) (Q.getD i false) (a.getD i none) (b.getD i none)

/-- Pointwise merge: the left cell when bound, else the right one. -/
def merge : Row → Row → Row
  | a :: as, b :: bs => (a <|> b) :: merge as bs
  | [], bs => bs
  | as, [] => as

/-- Pointwise union of schemas. -/
def Schema.union : Schema → Schema → Schema
  | a :: as, b :: bs => (a || b) :: Schema.union as bs
  | [], bs => bs
  | as, [] => as

def Schema.none (n : Nat) : Schema := List.replicate n false

/-- Compatibility without schemas (agree wherever both are bound): `EXISTS` correlation. -/
def agree : Row → Row → Bool
  | a :: as, b :: bs =>
    (match a, b with
     | some x, some y => x == y
     | _, _ => true) && agree as bs
  | _, _ => true

/-- The bag natural join. -/
def joinB (m : Missing) (P Q : Schema) (xs ys : Bag) : Bag :=
  xs.flatMap fun a => ys.filterMap fun b => if compat m P Q a b then some (merge a b) else none

/-- An input of an n-ary join: its schema and its bag. -/
abbrev SBag := Schema × Bag

/-- The unit relation: one row with no bindings. -/
def unitSB (_n : Nat) : SBag := ([], [[]])

/-- The binary join of schema-bags. -/
def joinSB (m : Missing) (a b : SBag) : SBag := (Schema.union a.1 b.1, joinB m a.1 b.1 a.2 b.2)

/-- The n-ary join: a left fold from the unit. -/
def joinAll (m : Missing) (n : Nat) (xs : List SBag) : SBag := xs.foldl (joinSB m) (unitSB n)

/-- The canonical key of a row: its cells' keys in variable order. -/
def rowKey (r : Row) : List Nat := r.flatMap cellKey

/-- The canonical row order. -/
def rowLe (a b : Row) : Bool := cmpNats (rowKey a) (rowKey b) != .gt

/-- Restriction of a row to a set of positions. -/
def Row.restrict (keep : Nat → Bool) (r : Row) : Row :=
  r.zipIdx.map fun (c, i) => if keep i then c else none

end Tiramemsu.Sem
