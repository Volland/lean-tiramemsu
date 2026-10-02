/-
The physical plan the evaluator runs, as a deterministic description (replacing Rust's SQLite
`EXPLAIN QUERY PLAN`, a listed deviation): per join the pattern order the greedy planner picks,
per pattern the index order or eid lookup, the key prefix, the index family and the pushed
filter conjuncts; per path the mode, the automaton size and the evaluation direction. The plan
is computed from the query alone (bindings are static), so it is the same for the same query.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Path.Engine

namespace Tiramemsu.Exec

open Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Codec

--# @lat: [[query#Index Nested-Loop Join#Explain]]

/-- One pattern's access path. -/
structure PatPlan where
  pattern : String
  /-- `spo`, `pos`, `osp` or `eid`. -/
  access : String
  /-- The key prefix, position by position. -/
  keyPrefix : List String
  /-- `live` under `Now`, `history` otherwise. -/
  family : String
  /-- The conjuncts applied right after this pattern. -/
  filters : List String
  deriving Repr, Inhabited

/-- One path pattern's plan. -/
structure PathPlan where
  pattern : String
  mode : String
  states : Nat
  /-- `forward` from the start, `inverted` from the end, or `unbound`. -/
  direction : String
  deriving Repr, Inhabited

/-- A plan node. -/
inductive Plan where
  | node (op : String) (pats : List PatPlan) (paths : List PathPlan) (children : List Plan)
  deriving Inhabited

def termText : TermOrVar → String
  | .var v => s!"?{v}"
  | .const (.iri s) => s!"<{s}>"
  | .const v => v.lexical
  | .id o => s!"#{o.raw}"
  | .param n => s!"${n}"

def patText (t : TriplePattern) : String :=
  s!"({termText t.s} {termText t.p} {termText t.o})" ++ (match t.eid with | some e => s!" eid ?{e}" | none => "")

mutual

def exprText : Expr → String
  | .var v => s!"?{v}"
  | .const (.iri s) => s!"<{s}>"
  | .const v => v.lexical
  | .param n => s!"${n}"
  | .cmp op a b =>
    let sym := match op with | .eq => "=" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
    s!"({exprText a} {sym} {exprText b})"
  | .sameTerm a b => s!"sameTerm({exprText a}, {exprText b})"
  | .and xs => "(" ++ " && ".intercalate (exprTexts xs) ++ ")"
  | .or xs => "(" ++ " || ".intercalate (exprTexts xs) ++ ")"
  | .not a => s!"!{exprText a}"
  | .bound v => s!"BOUND(?{v})"
  | .inList a xs n => s!"({exprText a} {if n then "NOT IN" else "IN"} ({", ".intercalate (exprTexts xs)}))"
  | .arith op a b =>
    let sym := match op with | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
    s!"({exprText a} {sym} {exprText b})"
  | .neg a => s!"-{exprText a}"
  | .coalesce xs => "COALESCE(" ++ ", ".intercalate (exprTexts xs) ++ ")"
  | .ite c a b => s!"IF({exprText c}, {exprText a}, {exprText b})"
  | .func f xs => f.name ++ "(" ++ ", ".intercalate (exprTexts xs) ++ ")"
  | .exists _ n => if n then "NOT EXISTS {…}" else "EXISTS {…}"

def exprTexts : List Expr → List String
  | [] => []
  | x :: xs => exprText x :: exprTexts xs

end

/-- The variables an expression reads directly, and whether it holds `EXISTS`. -/
def exprDirectVars (e : Expr) : List Var × Bool :=
  let vs := e.allVars
  (vs, ((exprText e).splitOn "EXISTS").length > 1)

def bindsPos (bound : List Var) : TermOrVar → Bool
  | .var v => bound.contains v
  | .param _ => false
  | _ => true

/-- The access of one pattern given the variables bound before it. -/
def patPlan (bound : List Var) (t : TriplePattern) (filters : List String) : PatPlan :=
  let fam := match t.view.tx with | .now => "live" | _ => "history"
  let eidBound := match t.eid with | some e => bound.contains e | none => false
  if eidBound then { pattern := patText t, access := "eid", keyPrefix := [s!"eid={t.eid.getD ""}"], family := fam, filters }
  else
    let s := if bindsPos bound t.s then some (termText t.s) else none
    let p := if bindsPos bound t.p then some (termText t.p) else none
    let o := if bindsPos bound t.o then some (termText t.o) else none
    let (ord, pfx) : String × List String := match s, p, o with
      | some s, some p, some o => ("spo", [s!"s={s}", s!"p={p}", s!"o={o}"])
      | some s, some p, none => ("spo", [s!"s={s}", s!"p={p}"])
      | some s, none, some o => ("osp", [s!"o={o}", s!"s={s}"])
      | some s, none, none => ("spo", [s!"s={s}"])
      | none, some p, some o => ("pos", [s!"p={p}", s!"o={o}"])
      | none, some p, none => ("pos", [s!"p={p}"])
      | none, none, some o => ("osp", [s!"o={o}"])
      | none, none, none => ("spo", [])
    { pattern := patText t, access := ord, keyPrefix := pfx, family := fam, filters }

/-- The plan of a path pattern. -/
def pathPlan (p : PathPattern) (bound : List Var) : PathPlan :=
  let states := match Path.buildDfa (Path.toRE false p.path) with
    | .ok d => d.states.size
    | .error _ => 0
  let startBound := bindsPos bound p.start
  let endBound := bindsPos bound p.end
  { pattern := s!"({termText p.start} {Path.PathExpr.print p.path} {termText p.end})", mode := p.mode.name, states,
    direction := if startBound then "forward" else if endBound then "inverted" else "unbound" }

/-- `?v = k` with an identity constant (it becomes a key prefix). -/
def seededVar? : Expr → Option Var
  | .cmp .eq (.var v) (.const k) | .cmp .eq (.const k) (.var v) =>
    match k with
    | .int _ | .double _ | .decimal _ | .dateTime .. => none
    | _ => some v
  | _ => none

/-- The plan of a join with pushed conjuncts. -/
def joinPlan (xs : List Op) (conds : List Expr) (children : List Plan) : Plan :=
  let pats := xs.zipIdx.filterMap fun (x, i) => (storedPat? x).map (i, ·)
  let others := xs.filter fun x => (storedPat? x).isNone && (match x with | .path _ => false | _ => true)
  let bound0 := others.flatMap (fun x => (scope x).certainVars) ++ conds.filterMap seededVar?
  let order := greedyOrder bound0 pats
  let early := conds.filter fun c => !((exprDirectVars c).2)
  let rec place : List (Nat × TriplePattern) → List Var → List Expr → List PatPlan
    | [], _, _ => []
    | (_, t) :: rest, bound, pending =>
      let bound' := bound ++ t.vars
      let (now, later) := pending.partition fun c => (exprDirectVars c).1.all bound'.contains
      patPlan bound t (now.map exprText) :: place rest bound' later
  let pplans := place order bound0 early
  let patVars := pats.flatMap (·.2.vars)
  let paths := (xs.filterMap Op.pathPat?).map (pathPlan · patVars)
  .node "Join" pplans paths children

mutual

/-- The plan of an operator tree. -/
def planOf : Op → Plan
  | .triple t => match t.p.virtual? with
    | some _ => .node s!"VirtualPattern {patText t}" [] [] []
    | none => joinPlan [.triple t] [] []
  | .path p => .node "Path" [] [pathPlan p []] []
  | .values vs _ => .node s!"Values {vs.map (s!"?{·}")}" [] [] []
  | .join xs => joinPlan xs [] (planInputs xs)
  | .leftJoin l r _ => .node "LeftJoin" [] [] [planOf l, planOf r]
  | .union xs => .node "Union" [] [] (planList xs)
  | .filter c (.join xs) =>
    joinPlan xs (match c with | .and ys => ys | e => [e]) (planInputs xs) |> fun
      | .node _ ps pp ch => .node s!"Filter+Join {exprText c}" ps pp ch
  | .filter c (.triple t) =>
    match t.p.virtual? with
    | some _ => .node s!"Filter {exprText c}" [] [] [planOf (.triple t)]
    | none => joinPlan [.triple t] (match c with | .and ys => ys | e => [e]) [] |> fun
      | .node _ ps pp ch => .node s!"Filter+Join {exprText c}" ps pp ch
  | .filter c x => .node s!"Filter {exprText c}" [] [] [planOf x]
  | .extend v e x => .node s!"Extend ?{v} := {exprText e}" [] [] [planOf x]
  | .aggregate g _ x => .node s!"Aggregate {g.map (s!"?{·}")}" [] [] [planOf x]
  | .project vs d x => .node s!"Project{if d then " distinct" else ""} {vs.map (s!"?{·}")}" [] [] [planOf x]
  | .orderLimit _ s l x => .node s!"OrderLimit skip={(s.map termText).getD "-"} limit={(l.map termText).getD "-"}" [] [] [planOf x]

def planList : List Op → List Plan
  | [] => []
  | x :: xs => planOf x :: planList xs

/-- The plans of a join's non-pattern, non-path inputs. -/
def planInputs : List Op → List Plan
  | [] => []
  | x :: xs =>
    match storedPat? x, x with
    | some _, _ => planInputs xs
    | none, .path _ => planInputs xs
    | none, _ => planOf x :: planInputs xs

end

def PatPlan.line (indent : String) (p : PatPlan) : String :=
  indent ++ "  pattern " ++ p.pattern ++ " via " ++ p.access ++ " [" ++ ", ".intercalate p.keyPrefix ++
    "] " ++ p.family ++ (if p.filters.isEmpty then "" else " filter " ++ " && ".intercalate p.filters)

def PathPlan.line (indent : String) (p : PathPlan) : String :=
  indent ++ "  path " ++ p.pattern ++ " " ++ p.mode ++ " states=" ++ toString p.states ++ " " ++ p.direction

mutual

/-- The plan text, one node per line, indented. -/
def Plan.render (indent : String := "") : Plan → List String
  | .node op pats paths children =>
    [indent ++ op] ++ pats.map (PatPlan.line indent) ++ paths.map (PathPlan.line indent) ++
      Plan.renderList (indent ++ "  ") children

def Plan.renderList (indent : String) : List Plan → List String
  | [] => []
  | p :: ps => Plan.render indent p ++ Plan.renderList indent ps

end

end Tiramemsu.Exec
