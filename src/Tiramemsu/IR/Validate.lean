/-
Structural validation and parameter binding.

`checkOp`/`checkExpr` are the local rules of one node; `validate` applies them to every node of
the tree (expressions and `EXISTS` subtrees included) and reports the first problem as
`InvalidQuery`. The reference semantics runs the same local checks at each node it evaluates, so
validation soundness (a validated query with complete parameters never fails with
`InvalidQuery`) is a theorem about these two definitions.

`bindParams` replaces every parameter by its value before any store read; a missing parameter
and a skip/limit parameter that is not a non-negative integer are `InvalidQuery`.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.IR.Scope

namespace Tiramemsu.IR

open Tiramemsu.Codec

--# @lat: [[query#Logical IR#Validation]]

def invalid {α : Type} (msg : String) : Except QError α := .error (.invalidQuery msg)

/-- A skip or limit position: a non-negative integer constant or a parameter. -/
def checkCount (what : String) : TermOrVar → Except QError Unit
  | .const (.int n) => if 0 ≤ n then .ok () else invalid s!"negative {what} {n}"
  | .param _ => .ok ()
  | _ => invalid s!"{what} must be a non-negative integer"

def checkCountOpt (what : String) : Option TermOrVar → Except QError Unit
  | none => .ok ()
  | some t => checkCount what t

/-- A graph set names at least one graph, by constants and parameters only. -/
def checkGraph : GraphSel → Except QError Unit
  | .set [] => invalid "a graph set must name at least one graph"
  | .set gs =>
    if gs.all (fun g => match g with | .const _ | .param _ => true | _ => false) then .ok ()
    else invalid "a graph set holds constants and parameters only"
  | _ => .ok ()

/-- The local rule of an expression node. -/
def checkExpr : Expr → Except QError Unit
  | .func f args =>
    if f.accepts args.length then .ok ()
    else invalid s!"{f.name} applied to {args.length} arguments"
  | _ => .ok ()

/-- Whether a values cell list holds a variable. -/
def cellsHaveVar (r : List (Option TermOrVar)) : Bool :=
  r.any fun c => match c with | some (.var _) => true | _ => false

/-- The local rule of an operator node (its children are checked separately). -/
def checkOp : Op → Except QError Unit
  | .triple t => do
    checkGraph t.graph
    match t.p.virtual? with
    | some _ =>
      if t.eid.isSome then invalid "a virtual-predicate pattern cannot bind an eid"
      else match t.graph with
        | .any => .ok ()
        | _ => invalid "a virtual-predicate pattern cannot be selected by graph"
    | none => .ok ()
  | .path p => checkGraph p.graph
  | .values vs rows =>
    if rows.any (·.length != vs.length) then invalid "a values row has the wrong number of cells"
    else if rows.any cellsHaveVar then invalid "a values cell cannot be a variable"
    else if vs.eraseDups.length != vs.length then invalid "values repeat a variable"
    else .ok ()
  | .extend v _ x =>
    if (scope x).binds v then invalid s!"Extend binds ?{v} which its input already binds" else .ok ()
  | .aggregate g aggs _ =>
    if (g ++ aggs.map (·.1)).eraseDups.length != g.length + aggs.length then
      invalid "an aggregate output collides with a grouping or aggregate variable"
    else if aggs.any (fun a => a.2.2.1.isNone && a.2.1 != .count) then
      invalid "an aggregate other than COUNT needs an argument"
    else .ok ()
  | .project vs _ x =>
    if vs.all (scope x).binds then .ok ()
    else invalid "a projected variable is not bound by the input"
  | .orderLimit _ skip limit _ => do
    checkCountOpt "skip" skip
    checkCountOpt "limit" limit
  | _ => .ok ()

mutual

/-- Every node of an expression passes its local rule. -/
def validateExpr : Expr → Except QError Unit
  | .var _ | .const _ | .param _ | .bound _ => .ok ()
  | .cmp _ a b | .sameTerm a b | .arith _ a b => do validateExpr a; validateExpr b
  | .and xs | .or xs | .coalesce xs => validateExprs xs
  | .func f xs => do checkExpr (.func f xs); validateExprs xs
  | .not a | .neg a => validateExpr a
  | .inList a xs _ => do validateExpr a; validateExprs xs
  | .ite c a b => do validateExpr c; validateExpr a; validateExpr b
  | .exists q _ => validateOp q

def validateExprs : List Expr → Except QError Unit
  | [] => .ok ()
  | x :: xs => do validateExpr x; validateExprs xs

/-- Every node of an operator tree passes its local rule. -/
def validateOp : Op → Except QError Unit
  | .triple t => checkOp (.triple t)
  | .path p => checkOp (.path p)
  | .values vs rows => checkOp (.values vs rows)
  | .join xs => validateOps xs
  | .union xs => validateOps xs
  | .leftJoin l r c => do
    validateOp l; validateOp r
    match c with
    | some e => validateExpr e
    | none => .ok ()
  | .filter c x => do validateExpr c; validateOp x
  | .extend v e x => do checkOp (.extend v e x); validateExpr e; validateOp x
  | .aggregate g aggs x => do checkOp (.aggregate g aggs x); validateAggs aggs; validateOp x
  | .project vs d x => do checkOp (.project vs d x); validateOp x
  | .orderLimit keys s l x => do checkOp (.orderLimit keys s l x); validateKeys keys; validateOp x

def validateOps : List Op → Except QError Unit
  | [] => .ok ()
  | x :: xs => do validateOp x; validateOps xs

def validateAggs : List (Var × AggFunc × Option Expr × Bool) → Except QError Unit
  | [] => .ok ()
  | (_, _, a, _) :: rest => do
    match a with
    | some e => validateExpr e
    | none => .ok ()
    validateAggs rest

def validateKeys : List (Expr × Bool) → Except QError Unit
  | [] => .ok ()
  | (e, _) :: rest => do validateExpr e; validateKeys rest

end

/-- Validates a query: needs no database. -/
def validate (q : Query) : Except QError Unit := validateOp q.root

/-! ## Parameter binding -/

def bindTerm (ps : Params) : TermOrVar → Except QError TermOrVar
  | .param n => match ps.get? n with
    | some v => .ok (.const v)
    | none => invalid s!"missing parameter ${n}"
  | t => .ok t

def bindCount (ps : Params) (what : String) : Option TermOrVar → Except QError (Option TermOrVar)
  | none => .ok none
  | some t => do
    let t ← bindTerm ps t
    match t with
    | .const (.int n) => if 0 ≤ n then .ok (some t) else invalid s!"negative {what} {n}"
    | _ => invalid s!"{what} must be a non-negative integer"

def bindTerms (ps : Params) : List TermOrVar → Except QError (List TermOrVar)
  | [] => .ok []
  | t :: ts => do return (← bindTerm ps t) :: (← bindTerms ps ts)

def bindGraph (ps : Params) : GraphSel → Except QError GraphSel
  | .set gs => do return .set (← bindTerms ps gs)
  | g => .ok g

def bindCell (ps : Params) : Option TermOrVar → Except QError (Option TermOrVar)
  | none => .ok none
  | some t => do return some (← bindTerm ps t)

def bindCells (ps : Params) : List (Option TermOrVar) → Except QError (List (Option TermOrVar))
  | [] => .ok []
  | c :: cs => do return (← bindCell ps c) :: (← bindCells ps cs)

def bindRows (ps : Params) : List (List (Option TermOrVar)) → Except QError (List (List (Option TermOrVar)))
  | [] => .ok []
  | r :: rs => do return (← bindCells ps r) :: (← bindRows ps rs)

def bindTriple (ps : Params) (t : TriplePattern) : Except QError TriplePattern := do
  return { t with s := ← bindTerm ps t.s, p := ← bindTerm ps t.p, o := ← bindTerm ps t.o,
                  graph := ← bindGraph ps t.graph }

def bindPathPat (ps : Params) (p : PathPattern) : Except QError PathPattern := do
  return { p with start := ← bindTerm ps p.start, «end» := ← bindTerm ps p.end,
                  graph := ← bindGraph ps p.graph }

mutual

def bindExpr (ps : Params) : Expr → Except QError Expr
  | .param n => match ps.get? n with
    | some v => .ok (.const v)
    | none => invalid s!"missing parameter ${n}"
  | .cmp op a b => do return .cmp op (← bindExpr ps a) (← bindExpr ps b)
  | .sameTerm a b => do return .sameTerm (← bindExpr ps a) (← bindExpr ps b)
  | .arith op a b => do return .arith op (← bindExpr ps a) (← bindExpr ps b)
  | .and xs => do return .and (← bindExprs ps xs)
  | .or xs => do return .or (← bindExprs ps xs)
  | .coalesce xs => do return .coalesce (← bindExprs ps xs)
  | .func f xs => do return .func f (← bindExprs ps xs)
  | .not a => do return .not (← bindExpr ps a)
  | .neg a => do return .neg (← bindExpr ps a)
  | .inList a xs n => do return .inList (← bindExpr ps a) (← bindExprs ps xs) n
  | .ite c a b => do return .ite (← bindExpr ps c) (← bindExpr ps a) (← bindExpr ps b)
  | .exists q n => do return .exists (← bindOp ps q) n
  | e => .ok e

def bindExprs (ps : Params) : List Expr → Except QError (List Expr)
  | [] => .ok []
  | x :: xs => do return (← bindExpr ps x) :: (← bindExprs ps xs)

def bindOp (ps : Params) : Op → Except QError Op
  | .triple t => do return .triple (← bindTriple ps t)
  | .path p => do return .path (← bindPathPat ps p)
  | .values vs rows => do return .values vs (← bindRows ps rows)
  | .join xs => do return .join (← bindOps ps xs)
  | .union xs => do return .union (← bindOps ps xs)
  | .leftJoin l r c => do
    let c' ← match c with
      | some e => do pure (some (← bindExpr ps e))
      | none => pure none
    return .leftJoin (← bindOp ps l) (← bindOp ps r) c'
  | .filter c x => do return .filter (← bindExpr ps c) (← bindOp ps x)
  | .extend v e x => do return .extend v (← bindExpr ps e) (← bindOp ps x)
  | .aggregate g aggs x => do return .aggregate g (← bindAggs ps aggs) (← bindOp ps x)
  | .project vs d x => do return .project vs d (← bindOp ps x)
  | .orderLimit keys s l x => do
    return .orderLimit (← bindKeys ps keys) (← bindCount ps "skip" s) (← bindCount ps "limit" l)
      (← bindOp ps x)

def bindOps (ps : Params) : List Op → Except QError (List Op)
  | [] => .ok []
  | x :: xs => do return (← bindOp ps x) :: (← bindOps ps xs)

def bindAggs (ps : Params) : List (Var × AggFunc × Option Expr × Bool) →
    Except QError (List (Var × AggFunc × Option Expr × Bool))
  | [] => .ok []
  | (v, f, a, d) :: rest => do
    let a' ← match a with
      | some e => do pure (some (← bindExpr ps e))
      | none => pure none
    return (v, f, a', d) :: (← bindAggs ps rest)

def bindKeys (ps : Params) : List (Expr × Bool) → Except QError (List (Expr × Bool))
  | [] => .ok []
  | (e, d) :: rest => do return (← bindExpr ps e, d) :: (← bindKeys ps rest)

end

end Tiramemsu.IR
