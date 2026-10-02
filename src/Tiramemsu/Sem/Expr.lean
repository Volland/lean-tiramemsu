/-
Three-valued expression evaluation.

An expression is first resolved against the query's variable table: variables become
positions, constants canonical values, and every `EXISTS` subtree is replaced by its bag (the
reference semantics resolves with `denote`, the evaluator with `eval`). A resolved expression
evaluates on a row to a value or an error (`none`). Unbound variables, NULLs, type errors and
division by zero are errors; `AND`/`OR`/`NOT` follow the Kleene tables with error as the third
value; a filter keeps a row only when the effective boolean value is true.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Sem.Row

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[query#Reference Semantics#Expressions]]

/-- A resolved expression: positions instead of variable names, bags instead of `EXISTS`. -/
inductive RExpr where
  | var (i : Nat)
  | const (v : Value)
  /-- An unbound name (a variable outside the table, or a parameter left unbound). -/
  | err
  | cmp (op : CmpOp) (a b : RExpr)
  | sameTerm (a b : RExpr)
  | and (xs : List RExpr)
  | or (xs : List RExpr)
  | not (a : RExpr)
  | bound (i : Nat)
  | inList (a : RExpr) (xs : List RExpr) (negated : Bool)
  | arith (op : ArithOp) (a b : RExpr)
  | neg (a : RExpr)
  | coalesce (xs : List RExpr)
  | ite (c a b : RExpr)
  | func (f : Func) (args : List RExpr)
  | exists (bag : Bag) (negated : Bool)
  deriving Inhabited

/-- Three-valued truth. -/
inductive Tri where
  | t | f | err
  deriving Repr, DecidableEq, Inhabited

def Tri.ofOpt : Option Bool → Tri
  | some true => .t
  | some false => .f
  | none => .err

def Tri.toOpt : Tri → Option Bool
  | .t => some true
  | .f => some false
  | .err => none

/-- Kleene conjunction of a list. -/
def triAnd (xs : List Tri) : Tri :=
  if xs.contains .f then .f else if xs.contains .err then .err else .t

/-- Kleene disjunction of a list. -/
def triOr (xs : List Tri) : Tri :=
  if xs.contains .t then .t else if xs.contains .err then .err else .f

def triNot : Tri → Tri
  | .t => .f
  | .f => .t
  | .err => .err

/-- A comparison of two values. -/
def compareVals (op : CmpOp) (a b : Value) : Option Bool :=
  match op with
  | .eq => some (valueEq a b)
  | .ne => some (!valueEq a b)
  | _ =>
    (cmpOrder a b).map fun o =>
      match op with
      | .lt => o == .lt
      | .le => o != .gt
      | .gt => o == .gt
      | _ => o != .lt

/-- Arithmetic on two values (`none`: non-numbers or division by zero). -/
def arithVals (op : ArithOp) (a b : Value) : Option Value := do
  let x ← a.num?
  let y ← b.num?
  if op == .div && y.isZeroOrNaN && !(match y with | .dbl d => d.isNaN | _ => false) then none
  else some (arith op x y).toValue

mutual

/-- Evaluates a resolved expression on a row. -/
def RExpr.eval (r : Row) : RExpr → Option Value
  | .var i => r.get i
  | .const v => some v
  | .err => none
  | .cmp op a b => do
    let x ← a.eval r
    let y ← b.eval r
    return .bool (← compareVals op x y)
  | .sameTerm a b => do return .bool ((← a.eval r) == (← b.eval r))
  | .and xs => (triAnd (RExpr.tris r xs)).toOpt.map .bool
  | .or xs => (triOr (RExpr.tris r xs)).toOpt.map .bool
  | .not a => (triNot (Tri.ofOpt ((a.eval r).bind ebv))).toOpt.map .bool
  | .bound i => some (.bool (r.get i).isSome)
  | .inList a xs n =>
    let t := triOr (RExpr.eqTris r (a.eval r) xs)
    (if n then triNot t else t).toOpt.map .bool
  | .arith op a b => do arithVals op (← a.eval r) (← b.eval r)
  | .neg a => do
    let x ← (← a.eval r).num?
    return x.neg.toValue
  | .coalesce xs => RExpr.firstOk r xs
  | .ite c a b => match Tri.ofOpt ((c.eval r).bind ebv) with
    | .t => a.eval r
    | .f => b.eval r
    | .err => none
  | .func f args => do applyFunc f (← RExpr.evalAll r args)
  | .exists bag n => some (.bool ((bag.any (agree r)) != n))

def RExpr.tris (r : Row) : List RExpr → List Tri
  | [] => []
  | x :: xs => Tri.ofOpt ((x.eval r).bind ebv) :: RExpr.tris r xs

def RExpr.eqTris (r : Row) (a : Option Value) : List RExpr → List Tri
  | [] => []
  | x :: xs => Tri.ofOpt (do compareVals .eq (← a) (← x.eval r)) :: RExpr.eqTris r a xs

def RExpr.firstOk (r : Row) : List RExpr → Option Value
  | [] => none
  | x :: xs => match x.eval r with
    | some v => some v
    | none => RExpr.firstOk r xs

def RExpr.evalAll (r : Row) : List RExpr → Option (List Value)
  | [] => some []
  | x :: xs => do return (← x.eval r) :: (← RExpr.evalAll r xs)

end

/-- The truth value of an expression (its effective boolean value). -/
def RExpr.tri (r : Row) (e : RExpr) : Tri := Tri.ofOpt ((e.eval r).bind ebv)

/-- Whether a filter keeps a row. -/
def RExpr.holds (e : RExpr) (r : Row) : Bool := e.tri r == .t

end Tiramemsu.Sem
