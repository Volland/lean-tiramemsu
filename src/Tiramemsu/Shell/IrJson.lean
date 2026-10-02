/-
The JSON form of IR queries shared by the Lean and Rust oracle drivers (`m3.*` operations): terms
`{"var"}`, `{"const": value}`, `{"id"}`, `{"param"}`; operators and expressions one key per
variant; path expressions as text. Values use the one-key form of `Shell.ValueJson`.
Shell module (unverified; oracle tooling).
-/
import Tiramemsu.Shell.ValueJson
import Tiramemsu.Path.Syntax

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.IR Tiramemsu.Codec

--# @lat: [[query#Differential Query Oracle]]

/-! ## Writing -/

def irTermOfIrJ : TermOrVar → Json
  | .var v => .obj #[("var", .str v)]
  | .const c => .obj #[("const", valueJ c)]
  | .id o => .obj #[("id", .int o.raw.toInt)]
  | .param n => .obj #[("param", .str n)]

def irViewJ (v : View.ViewSpec) : Json :=
  let tx : Json := match v.tx with
    | .now => .str "now"
    | .history => .str "history"
    | .asOf (.tx t) => .obj #[("asOfTx", .int t.toInt)]
    | .asOf (.instant ms) => .obj #[("asOfInstant", .int ms.toInt)]
  match v.valid with
  | .unfiltered => .obj #[("tx", tx)]
  | .at d => .obj #[("tx", tx), ("validAt", .int d.toInt)]

def irGraphJ : GraphSel → Json
  | .any => .str "any"
  | .set gs => .obj #[("set", .arr (gs.map irTermOfIrJ).toArray)]
  | .var g => .obj #[("var", .str g)]

def irCmpName : CmpOp → String
  | .eq => "=" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

def irArithName : ArithOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

mutual

def irExprJ : Expr → Json
  | .var v => .obj #[("var", .str v)]
  | .const c => .obj #[("const", valueJ c)]
  | .param n => .obj #[("param", .str n)]
  | .cmp op a b => .obj #[("cmp", .arr #[.str (irCmpName op), irExprJ a, irExprJ b])]
  | .sameTerm a b => .obj #[("sameTerm", .arr #[irExprJ a, irExprJ b])]
  | .and xs => .obj #[("and", .arr (irExprsJ xs).toArray)]
  | .or xs => .obj #[("or", .arr (irExprsJ xs).toArray)]
  | .not a => .obj #[("not", irExprJ a)]
  | .bound v => .obj #[("bound", .str v)]
  | .inList a xs n => .obj #[("in", .arr #[irExprJ a, .arr (irExprsJ xs).toArray, .bool n])]
  | .arith op a b => .obj #[("arith", .arr #[.str (irArithName op), irExprJ a, irExprJ b])]
  | .neg a => .obj #[("neg", irExprJ a)]
  | .coalesce xs => .obj #[("coalesce", .arr (irExprsJ xs).toArray)]
  | .ite c a b => .obj #[("if", .arr #[irExprJ c, irExprJ a, irExprJ b])]
  | .func f xs => .obj #[("func", .arr #[.str f.name, .arr (irExprsJ xs).toArray])]
  | .exists q n => .obj #[("exists", .arr #[irOpJ q, .bool n])]

def irExprsJ : List Expr → List Json
  | [] => []
  | x :: xs => irExprJ x :: irExprsJ xs

def irOpJ : Op → Json
  | .triple t => .obj #[("triple", .obj (#[("s", irTermOfIrJ t.s), ("p", irTermOfIrJ t.p), ("o", irTermOfIrJ t.o),
      ("view", irViewJ t.view), ("graph", irGraphJ t.graph)] ++
      (match t.eid with | some e => #[("eid", .str e)] | none => #[]) ++
      (match t.isoGroup with | some g => #[("group", .int g)] | none => #[])))]
  | .path p => .obj #[("path", .obj (#[("start", irTermOfIrJ p.start), ("end", irTermOfIrJ p.end),
      ("path", .str (Path.PathExpr.print p.path)), ("mode", .str p.mode.name), ("view", irViewJ p.view),
      ("graph", irGraphJ p.graph)] ++
      (match p.maxHops with | some h => #[("maxHops", .int h)] | none => #[]) ++
      (match p.bindPath with | some b => #[("bind", .str b)] | none => #[])))]
  | .values vs rows => .obj #[("values", .obj #[("vars", .arr (vs.map Json.str).toArray),
      ("rows", .arr (rows.map fun r => Json.arr (r.map fun c => match c with
        | some t => irTermOfIrJ t
        | none => Json.null).toArray).toArray)])]
  | .join xs => .obj #[("join", .arr (irOpsJ xs).toArray)]
  | .union xs => .obj #[("union", .arr (irOpsJ xs).toArray)]
  | .leftJoin l r c => .obj #[("leftJoin", .obj (#[("l", irOpJ l), ("r", irOpJ r)] ++
      (match c with | some e => #[("cond", irExprJ e)] | none => #[])))]
  | .filter c x => .obj #[("filter", .obj #[("cond", irExprJ c), ("input", irOpJ x)])]
  | .extend v e x => .obj #[("extend", .obj #[("var", .str v), ("expr", irExprJ e), ("input", irOpJ x)])]
  | .aggregate g aggs x => .obj #[("aggregate", .obj #[("group", .arr (g.map Json.str).toArray),
      ("aggs", .arr (irAggsJ aggs).toArray), ("input", irOpJ x)])]
  | .project vs d x => .obj #[("project", .obj #[("vars", .arr (vs.map Json.str).toArray), ("distinct", .bool d),
      ("input", irOpJ x)])]
  | .orderLimit keys s l x => .obj #[("orderLimit", .obj (#[("keys", .arr (irKeysJ keys).toArray), ("input", irOpJ x)] ++
      (match s with | some t => #[("skip", irTermOfIrJ t)] | none => #[]) ++
      (match l with | some t => #[("limit", irTermOfIrJ t)] | none => #[])))]

def irOpsJ : List Op → List Json
  | [] => []
  | x :: xs => irOpJ x :: irOpsJ xs

def irAggsJ : List (Var × AggFunc × Option Expr × Bool) → List Json
  | [] => []
  | (v, f, a, d) :: rest =>
    Json.obj (#[("var", .str v), ("func", .str f.name), ("distinct", .bool d)] ++
      (match a with | some e => #[("arg", irExprJ e)] | none => #[]) ++
      (match f with | .groupConcat sep => #[("sep", .str sep)] | _ => #[])) :: irAggsJ rest

def irKeysJ : List (Expr × Bool) → List Json
  | [] => []
  | (e, d) :: rest => Json.obj #[("expr", irExprJ e), ("desc", .bool d)] :: irKeysJ rest

end

def irSemanticsJ (s : Semantics) : Json :=
  .obj #[("matchMode", .str (if s.matchMode == .homomorphism then "Homomorphism" else "RelIsomorphism")),
    ("missing", .str (if s.missing == .unbound then "Unbound" else "Null3VL")),
    ("graphSet", .str (if s.graphSet == .setOfTriples then "SetOfTriples" else "BagOfEids"))]

def irQueryJ (q : Query) : Json := .obj #[("root", irOpJ q.root), ("semantics", irSemanticsJ q.sem)]

/-! ## Reading -/

abbrev JR := Except String

def irJfail {α : Type} (m : String) : JR α := .error m

def irKey1 (j : Json) : JR (String × Json) :=
  match j with
  | .obj #[(k, v)] => .ok (k, v)
  | _ => irJfail s!"expected a one-key object, got {j.compress}"

def irTermOfJ (j : Json) : JR TermOrVar := do
  let (k, v) ← irKey1 j
  match k, v with
  | "var", .str s => return .var s
  | "const", c => match valueOfJ? c with
    | some x => return .const x
    | none => irJfail "bad value"
  | "id", .int i => return .id ⟨Int64.ofInt i⟩
  | "param", .str s => return .param s
  | _, _ => irJfail s!"bad term {j.compress}"

def irViewOfJ (j : Json) : JR View.ViewSpec := do
  let tx : View.TxSpec ← match j.get? "tx" with
    | some (.str "now") | none => pure .now
    | some (.str "history") => pure .history
    | some t => match t.getInt? "asOfTx", t.getInt? "asOfInstant" with
      | some x, _ => pure (.asOf (.tx (Int64.ofInt x)))
      | _, some x => pure (.asOf (.instant (Int64.ofInt x)))
      | _, _ => irJfail "bad view"
  return { tx, valid := match j.getInt? "validAt" with
    | some d => .at (Int64.ofInt d)
    | none => .unfiltered }

def irGraphOfJ (j : Json) : JR GraphSel := do
  match j with
  | .str "any" => return .any
  | _ =>
    let (k, v) ← irKey1 j
    match k, v with
    | "set", .arr gs => return .set (← gs.toList.mapM irTermOfJ)
    | "var", .str g => return .var g
    | _, _ => irJfail "bad graph selector"

def irCmpOfName : String → JR CmpOp
  | "=" => .ok .eq | "!=" => .ok .ne | "<" => .ok .lt | "<=" => .ok .le | ">" => .ok .gt | ">=" => .ok .ge
  | o => irJfail s!"bad comparison {o}"

def irArithOfName : String → JR ArithOp
  | "+" => .ok .add | "-" => .ok .sub | "*" => .ok .mul | "/" => .ok .div
  | o => irJfail s!"bad arithmetic {o}"

def irAllFuncs : List Func :=
  [.str, .lang, .datatype, .isIri, .isLiteral, .isNumeric, .strLen, .ucase, .lcase, .contains, .strStarts,
   .strEnds, .regex, .isBlank, .langMatches, .iri, .strDt, .strLang, .substr, .strBefore, .strAfter, .concat,
   .encodeForUri, .replace, .abs, .ceil, .floor, .round, .year, .month, .day, .hours, .minutes, .seconds,
   .timezone, .tz, .castString, .castInteger, .castDecimal, .castDouble, .castBoolean, .castDate, .castDateTime]

def irFuncOfName (n : String) : JR Func :=
  match irAllFuncs.find? (·.name == n) with
  | some f => .ok f
  | none => irJfail s!"unknown function {n}"

def irStrOfJ : Json → JR String
  | .str s => .ok s
  | j => irJfail s!"expected a string, got {j.compress}"

def irModeOfName (s : String) : JR PathMode :=
  match PathMode.parse? s with
  | some m => .ok m
  | none => irJfail s!"unsupported path mode {s}"

def irAggFuncOf (n : String) (sep : Option String) : JR AggFunc :=
  match n with
  | "count" => .ok .count | "sum" => .ok .sum | "avg" => .ok .avg | "min" => .ok .min | "max" => .ok .max
  | "sample" => .ok .sample | "group_concat" => .ok (.groupConcat (sep.getD " "))
  | o => irJfail s!"unknown aggregate {o}"

/-- JSON nesting is bounded by the text, so the readers take a fuel bound (the depth). -/
def irExprOfJ : Nat → Json → JR Expr
  | 0, _ => irJfail "nested too deeply"
  | fuel + 1, j => do
    let (k, v) ← irKey1 j
    let ex := irExprOfJ fuel
    let exs (xs : Json) : JR (List Expr) := match xs with
      | .arr ys => ys.toList.mapM ex
      | _ => irJfail "expected a list of expressions"
    match k, v with
    | "var", .str s => return .var s
    | "const", c => match valueOfJ? c with
      | some x => return .const x
      | none => irJfail "bad value"
    | "param", .str s => return .param s
    | "cmp", .arr #[.str o, a, b] => return .cmp (← irCmpOfName o) (← ex a) (← ex b)
    | "sameTerm", .arr #[a, b] => return .sameTerm (← ex a) (← ex b)
    | "and", xs => return .and (← exs xs)
    | "or", xs => return .or (← exs xs)
    | "not", a => return .not (← ex a)
    | "bound", .str s => return .bound s
    | "in", .arr #[a, xs, .bool n] => return .inList (← ex a) (← exs xs) n
    | "arith", .arr #[.str o, a, b] => return .arith (← irArithOfName o) (← ex a) (← ex b)
    | "neg", a => return .neg (← ex a)
    | "coalesce", xs => return .coalesce (← exs xs)
    | "if", .arr #[c, a, b] => return .ite (← ex c) (← ex a) (← ex b)
    | "func", .arr #[.str n, xs] => return .func (← irFuncOfName n) (← exs xs)
    | "exists", .arr #[q, .bool n] => return .exists (← irOpOfJ fuel q) n
    | _, _ => irJfail s!"bad expression {j.compress}"
where
  irOpOfJ : Nat → Json → JR Op
    | 0, _ => irJfail "nested too deeply"
    | fuel + 1, j => do
      let (k, v) ← irKey1 j
      let op := irOpOfJ fuel
      let ops (xs : Json) : JR (List Op) := match xs with
        | .arr ys => ys.toList.mapM op
        | _ => irJfail "expected a list of operators"
      let ex := irExprOfJ fuel
      let field (o : Json) (f : String) : JR Json := match o.get? f with
        | some x => .ok x
        | none => irJfail s!"missing {f}"
      let strs (o : Json) (f : String) : JR (List String) := do
        match ← field o f with
        | .arr xs => xs.toList.mapM irStrOfJ
        | _ => irJfail s!"{f} is not a list"
      match k with
      | "triple" =>
        let s ← irTermOfJ (← field v "s")
        let p ← irTermOfJ (← field v "p")
        let o ← irTermOfJ (← field v "o")
        let view ← irViewOfJ ((v.get? "view").getD .null)
        let graph ← irGraphOfJ ((v.get? "graph").getD (.str "any"))
        let t : TriplePattern := { s, p, o, eid := v.getStr? "eid", view, isoGroup := (v.getInt? "group").map Int.toNat, graph }
        return .triple t
      | "path" =>
        let text ← irStrOfJ (← field v "path")
        let pe ← match Path.parse text with
          | .ok e => pure e
          | .error e => irJfail (toString e)
        let st ← irTermOfJ (← field v "start")
        let en ← irTermOfJ (← field v "end")
        let mode ← irModeOfName ((v.getStr? "mode").getD "REACH")
        let view ← irViewOfJ ((v.get? "view").getD .null)
        let graph ← irGraphOfJ ((v.get? "graph").getD (.str "any"))
        let pp : PathPattern := { start := st, «end» := en, path := pe, mode, maxHops := (v.getInt? "maxHops").map Int.toNat, bindPath := v.getStr? "bind", view, graph }
        return .path pp
      | "values" =>
        let rj ← field v "rows"
        let rows ← match rj with
          | .arr rs => rs.toList.mapM fun r => match r with
            | .arr cs => cs.toList.mapM fun c => match c with
              | .null => pure none
              | t => do pure (some (← irTermOfJ t))
            | _ => irJfail "bad values row"
          | _ => irJfail "bad values rows"
        return .values (← strs v "vars") rows
      | "join" => return .join (← ops v)
      | "union" => return .union (← ops v)
      | "leftJoin" =>
        let cond ← match v.get? "cond" with
          | some c => do pure (some (← ex c))
          | none => pure none
        return .leftJoin (← op (← field v "l")) (← op (← field v "r")) cond
      | "filter" => return .filter (← ex (← field v "cond")) (← op (← field v "input"))
      | "extend" => return .extend (← irStrOfJ (← field v "var")) (← ex (← field v "expr")) (← op (← field v "input"))
      | "aggregate" =>
        let aj ← field v "aggs"
        let aggs ← match aj with
          | .arr xs => xs.toList.mapM fun a => do
            let f ← irAggFuncOf ((a.getStr? "func").getD "") (a.getStr? "sep")
            let arg ← match a.get? "arg" with
              | some e => do pure (some (← ex e))
              | none => pure none
            pure ((a.getStr? "var").getD "", f, arg, (a.getBool? "distinct").getD false)
          | _ => irJfail "bad aggregates"
        return .aggregate (← strs v "group") aggs (← op (← field v "input"))
      | "project" => return .project (← strs v "vars") ((v.getBool? "distinct").getD false) (← op (← field v "input"))
      | "orderLimit" =>
        let kjs ← field v "keys"
        let keys ← match kjs with
          | .arr xs => xs.toList.mapM fun kj => do pure (← ex (← field kj "expr"), (kj.getBool? "desc").getD false)
          | _ => irJfail "bad keys"
        let cnt (f : String) : JR (Option TermOrVar) := match v.get? f with
          | some t => do pure (some (← irTermOfJ t))
          | none => pure none
        return .orderLimit keys (← cnt "skip") (← cnt "limit") (← op (← field v "input"))
      | other => irJfail s!"unknown operator {other}"

def irOpOfJ (j : Json) : JR Op := irExprOfJ.irOpOfJ 10000 j

def irSemanticsOfJ (j : Json) : Semantics :=
  { matchMode := if j.getStr? "matchMode" == some "RelIsomorphism" then .relIsomorphism else .homomorphism,
    missing := if j.getStr? "missing" == some "Null3VL" then .null3VL else .unbound,
    graphSet := if j.getStr? "graphSet" == some "BagOfEids" then .bagOfEids else .setOfTriples }

def irQueryOfJ (j : Json) : JR Query := do
  let some r := j.get? "root" | irJfail "missing root"
  return { root := ← irOpOfJ r, sem := irSemanticsOfJ ((j.get? "semantics").getD .null) }

end Tiramemsu.Shell
