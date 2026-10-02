/-
Variable scoping (Rust `tm_ir::validate::scope`): per operator, the variables it exposes in
order of first binding (a left-to-right depth-first walk) and those that may be missing in some
row. The certain variables are the exposed ones that are never missing. The result columns are
the root `Project`'s variables, otherwise every exposed variable in order of first binding.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.IR.Types

namespace Tiramemsu.IR

--# @lat: [[query#Logical IR#Scope]]

/-- The variables an operator exposes, and which of them may be missing. -/
structure Scope where
  vars : List Var := []
  maybeMissing : List Var := []
  deriving Repr, DecidableEq, Inhabited

namespace Scope

def push (s : Scope) (v : Var) : Scope :=
  if s.vars.contains v then s else { s with vars := s.vars ++ [v] }

def miss (s : Scope) (v : Var) : Scope :=
  if s.maybeMissing.contains v then s else { s with maybeMissing := s.maybeMissing ++ [v] }

def binds (s : Scope) (v : Var) : Bool := s.vars.contains v

/-- Bound in every row. -/
def certain (s : Scope) (v : Var) : Bool := s.binds v && !s.maybeMissing.contains v

def certainVars (s : Scope) : List Var := s.vars.filter s.certain

end Scope

def TermOrVar.vars : TermOrVar → List Var
  | .var v => [v]
  | _ => []

def GraphSel.vars : GraphSel → List Var
  | .var g => [g]
  | _ => []

/-- The variables a triple pattern binds, in position order. -/
def TriplePattern.vars (t : TriplePattern) : List Var :=
  t.s.vars ++ t.p.vars ++ t.o.vars ++ t.eid.toList ++ t.graph.vars

/-- The variables a path pattern binds. -/
def PathPattern.vars (p : PathPattern) : List Var :=
  p.start.vars ++ p.end.vars ++ p.bindPath.toList ++ p.graph.vars

def Scope.ofList (vs : List Var) : Scope := vs.foldl Scope.push {}

/-- Join of scopes: exposed in order; missing when missing in every input that binds it. -/
def joinScopes (ss : List Scope) : Scope :=
  let s0 : Scope := ss.foldl (fun acc sc => sc.vars.foldl Scope.push acc) {}
  s0.vars.foldl (fun acc v =>
    if (ss.filter (·.binds v)).all (·.maybeMissing.contains v) then acc.miss v else acc) s0

/-- Union of scopes: missing when some branch does not bind it or may miss it. -/
def unionScopes (ss : List Scope) : Scope :=
  let s0 : Scope := ss.foldl (fun acc sc => sc.vars.foldl Scope.push acc) {}
  s0.vars.foldl (fun acc v =>
    if ss.any (fun sc => !sc.binds v || sc.maybeMissing.contains v) then acc.miss v else acc) s0

def leftJoinScope (a b : Scope) : Scope :=
  let s0 : Scope := (a.vars ++ b.vars).foldl Scope.push {}
  let s1 : Scope := { s0 with maybeMissing := a.maybeMissing }
  b.vars.foldl (fun acc v => if a.binds v then acc else acc.miss v) s1

mutual

/-- The scope of an operator. -/
def scope : Op → Scope
  | .triple t => Scope.ofList t.vars
  | .path p => Scope.ofList p.vars
  | .values vs rows =>
    (List.range vs.length).foldl (fun acc i =>
      let v := vs.getD i ""
      let acc := acc.push v
      if rows.any (fun r => (r.getD i none).isNone) then acc.miss v else acc) {}
  | .join xs => joinScopes (scopeList xs)
  | .leftJoin l r _ => leftJoinScope (scope l) (scope r)
  | .union xs => unionScopes (scopeList xs)
  | .filter _ x => scope x
  | .extend v e x =>
    let inner := scope x
    let s := inner.push v
    let certain := match e with
      | .const _ | .param _ => true
      | .var w => inner.certain w
      | _ => false
    if certain then s else s.miss v
  | .aggregate g aggs x =>
    let inner := scope x
    let s := g.foldl (fun acc v =>
      let acc := acc.push v
      if inner.certain v then acc else acc.miss v) {}
    aggs.foldl (fun acc a =>
      let acc := acc.push a.1
      if a.2.1 == .count then acc else acc.miss a.1) s
  | .project vs _ x =>
    let inner := scope x
    vs.foldl (fun acc v =>
      let acc := acc.push v
      if inner.certain v then acc else acc.miss v) {}
  | .orderLimit _ _ _ x => scope x

def scopeList : List Op → List Scope
  | [] => []
  | x :: xs => scope x :: scopeList xs

end

/-- The result columns. -/
def outputVars (op : Op) : List Var := (scope op).vars

/-! ## All variables of a tree (expressions and `EXISTS` subtrees included) -/

mutual

def Expr.allVars : Expr → List Var
  | .var v | .bound v => [v]
  | .const _ | .param _ => []
  | .cmp _ a b | .sameTerm a b | .arith _ a b => a.allVars ++ b.allVars
  | .and xs | .or xs | .coalesce xs | .func _ xs => Expr.allVarsList xs
  | .not a | .neg a => a.allVars
  | .inList a xs _ => a.allVars ++ Expr.allVarsList xs
  | .ite c a b => c.allVars ++ a.allVars ++ b.allVars
  | .exists q _ => q.allVars

def Expr.allVarsList : List Expr → List Var
  | [] => []
  | x :: xs => x.allVars ++ Expr.allVarsList xs

def Op.allVars : Op → List Var
  | .triple t => t.vars
  | .path p => p.vars
  | .values vs _ => vs
  | .join xs | .union xs => Op.allVarsList xs
  | .leftJoin l r c => l.allVars ++ r.allVars ++ (match c with | some e => e.allVars | none => [])
  | .filter c x => x.allVars ++ c.allVars
  | .extend v e x => x.allVars ++ [v] ++ e.allVars
  | .aggregate g aggs x => x.allVars ++ g ++ Op.allVarsAggs aggs
  | .project vs _ x => x.allVars ++ vs
  | .orderLimit keys _ _ x => x.allVars ++ Op.allVarsKeys keys

def Op.allVarsList : List Op → List Var
  | [] => []
  | x :: xs => x.allVars ++ Op.allVarsList xs

def Op.allVarsAggs : List (Var × AggFunc × Option Expr × Bool) → List Var
  | [] => []
  | (v, _, a, _) :: rest => v :: (match a with | some e => e.allVars | none => []) ++ Op.allVarsAggs rest

def Op.allVarsKeys : List (Expr × Bool) → List Var
  | [] => []
  | (e, _) :: rest => e.allVars ++ Op.allVarsKeys rest

end

/-- The variable table of a query: every variable of the tree, without duplicates, in order of
first occurrence. Rows of the semantics are positional over this table. -/
def Op.varTable (op : Op) : List Var := op.allVars.eraseDups

end Tiramemsu.IR
