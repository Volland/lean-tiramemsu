/-
End-to-end tests of the Rust recipes (`lat.md/recipes.md` of the pinned build) that need no
SPARQL or Cypher syntax, written as IR queries and API calls: impact analysis (dependents =
inverse-virtual-hop paths = a dry-run retraction, over random layered graphs), evidence chains
through time, provenance from transaction metadata, edit lineage, contradictions between
sources, when we learned it, answers that cite their facts, portable facts and reasoning inside
one graph. Each query runs through the reference semantics and the evaluator on the model and
on SQLite.
-/
import Test.Query.Util
import Test.Query.Paths
import Tiramemsu.Prov.EvalProv
import Tiramemsu.Shell.BundleJson

namespace Test.Query.Recipes

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem
open Test
open Test.Store (v sysV assertV assertI createV enc day retractE between stmt supersedeE)
open Test.Query
open Test.Query.Paths (lcg pick idOf)

def qq (o : IR.Op) : Query := { root := o }

/-- Runs a query on every evaluation path; returns the reference rows over `cols`. -/
def rowsAll (name : String) (f : Fix) (q : Query) (cols : List Var) : TestM (List (List (Option Value))) := do
  match denoteQ f.st [] q, evalModel f.st [] q, ← evalSqlite f.db [] q with
  | .ok (p, b), .ok (p', b'), .ok (p'', b'') =>
    let r := rowsBy p cols b
    checkEq s!"{name} [evaluator]" (rowsBy p' cols b') r
    checkEq s!"{name} [sqlite]" (rowsBy p'' cols b'') r
    return r
  | a, b, c =>
    check name false s!"{showErr a} / {showErr b} / {showErr c}"
    return []

def tpE (s p o e : String) (view : View.ViewSpec := {}) : IR.Op :=
  .triple { s := term s, p := term p, o := term o, eid := some e, view }
def tpV (s : TermOrVar) (p : String) (o : String) : IR.Op := .triple { s, p := term p, o := term o }

def path (s : TermOrVar) (e : TermOrVar) (text : String) (mode : PathMode := .reach)
    (view : View.ViewSpec := {}) (graph : GraphSel := .any) : IR.Op :=
  .path { start := s, «end» := e, path := (Path.parse text).toOption.getD (.atom "urn:none"), mode, view, graph }

def main : IO UInt32 := do
  let (_, r) ← (do
    -- Impact analysis: dependents = the inverse virtual-hop closure = a dry-run retraction
    for seed in List.range 30 do
      let bodies : List (TxProg Unit) := [do
        let mut eids : Array ObjectId := #[]
        let mut s := lcg (seed + 3)
        for _ in List.range (4 + seed % 6) do
          s := lcg s
          let subj : TxProg ObjectId :=
            if eids.isEmpty || (s / 65536) % 3 == 0 then enc (v (pick s ["a", "b", "c"])) else pure (eids.getD ((s / 7) % eids.size) default)
          s := lcg s
          let obj : TxProg ObjectId :=
            if eids.isEmpty || (s / 65536) % 3 != 0 then enc (v (pick s ["x", "y"])) else pure (eids.getD ((s / 11) % eids.size) default)
          let a ← TxProg.verb (.assert (← subj) (← enc (v "about")) (← obj) {})
          eids := eids.push a.eid
        pure ()]
      let f ← buildBoth s!"recipe-impact-{seed}" bodies
      for e in [1, 2, 3] do
        let deps : List Int64 := match (View.dependents {} (stmt e)).onModel f.st with
          | .ok xs => (xs.map ObjectId.raw).mergeSort fun (a b : Int64) => decide (a.toInt ≤ b.toInt)
          | .error _ => []
        let ends := match (do
            let rows ← Path.run {} { start := (stmt e).raw, expr := ← Path.parseText "(^sys:subject|^sys:object)*" }
            pure (rows.map (·.end)) : Exec.EvM _).run.onModel f.st with
          | .ok (.ok xs) => (if deps.isEmpty then [] else xs).mergeSort fun a b => decide (a.toInt ≤ b.toInt)
          | _ => []
        let (dry, _) := Model.dryRun 999000 {} (do let _ ← retractE (stmt e); pure ()) f.st
        let retracted := match dry with
          | .ok (_, rep) => (rep.retracted.toList.map (·.1.raw)).mergeSort fun a b => decide (a.toInt ≤ b.toInt)
          | .error _ => []
        checkEq s!"impact {seed}/{e}: dependents = path ends" ends deps
        checkEq s!"impact {seed}/{e}: dependents = dry-run retraction" retracted deps
      f.db.close
    -- Evidence chains through time
    let f1 ← buildBoth "recipe-evidence" [do
      let e0 ← assertV (v "paper") (v "states") (v "fact")
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← TxProg.verb (.assert e1.eid (← enc (v "derivedFrom")) e0.eid {})
      let _ ← TxProg.verb (.assert (← enc (v "belief9")) (← enc (v "supportedBy")) e1.eid {}); pure (),
      do let _ ← retractE (stmt 3); pure ()]
    let src := rowsAll "evidence now" f1 (qq (.project ["src"] false (path (.const (v "belief9")) (.var "src") "supportedBy/derivedFrom*"))) ["src"]
    checkEq "evidence chain now" (← src) [[some (.stmt 2)]]
    let srcThen ← rowsAll "evidence as of 1" f1
      (qq (.project ["src"] false (path (.const (v "belief9")) (.var "src") "supportedBy/derivedFrom*" (view := View.ViewSpec.asOfT 1)))) ["src"]
    checkEq "evidence chain as of 1 sees the retracted link" (srcThen.length) 2
    checkEq "who the evidence is about" (← rowsAll "evidence subject" f1
      (qq (.project ["who"] false (path (.const (v "belief9")) (.var "who") "supportedBy/sys:subject"))) ["who"]) [[some (v "alice")]]
    -- Provenance from transaction metadata
    let f2 ← buildBoth "recipe-txmeta" [do let _ ← assertV (v "alice") (v "worksAt") (v "acme"); pure (),
      do let _ ← assertV (v "bob") (v "worksAt") (v "globex"); pure (),
      do let _ ← assertV (.tx 1) (sysV "author") (v "agent7"); pure ()]
    checkEq "facts written by agent7" (← rowsAll "tx meta" f2
      (qq (.project ["who", "c"] false (.join [tpE "?who" "worksAt" "?c" "r", tpV (.var "r") "tm:txAdded" "?t",
          tpV (.var "t") "sys:author" "agent7"]))) ["who", "c"]) [[some (v "alice"), some (v "acme")]]
    -- Edit lineage over sys:supersedes
    let f3 ← buildBoth "recipe-lineage" [do let _ ← assertV (v "alice") (v "age") (.int 30); pure (),
      do let _ ← supersedeE (stmt 1) { o := some (.int 31) }; pure (),
      do let _ ← supersedeE (stmt 2) { o := some (.int 32) }; pure ()]
    let lineage ← rowsAll "edit lineage" f3 (qq (.project ["old"] false (.join [tpE "alice" "age" "?a" "r",
      path (.var "r") (.var "old") "sys:supersedes+"]))) ["old"]
    checkEq "edit lineage: both earlier versions" lineage.length 2
    -- Contradictions between sources
    let f4 ← buildBoth "recipe-contradiction" [
      do let _ ← assertV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2023-01-01"); pure (),
      do let _ ← assertV (v "alice") (v "worksAt") (v "globex") (between "2022-01-01" "2024-01-01"); pure (),
      do let _ ← assertV (v "alice") (v "worksAt") (v "initech") (between "2025-01-01" "2026-01-01"); pure (),
      do
        let _ ← assertV (.tx 1) (sysV "author") (v "hr")
        let _ ← assertV (.tx 2) (sysV "author") (v "chat")
        let _ ← assertV (.tx 3) (sysV "author") (v "chat"); pure ()]
    let x (n : String) : Expr := .var n
    let notB (n : String) : Expr := .not (.bound n)
    let q4 : IR.Op := .project ["o1", "o2"] false
      (.filter (.and [.or [notB "f1", notB "u2", .cmp .lt (x "f1") (x "u2")], .or [notB "f2", notB "u1", .cmp .lt (x "f2") (x "u1")]])
        (.leftJoin (.leftJoin (.leftJoin (.leftJoin
          (.filter (.and [.cmp .ne (x "a1") (x "a2"), .cmp .lt (.func .str [x "o1"]) (.func .str [x "o2"])])
            (.join [tpE "?s" "worksAt" "?o1" "r1", tpE "?s" "worksAt" "?o2" "r2",
             tpV (.var "r1") "tm:txAdded" "?t1", tpV (.var "t1") "sys:author" "?a1",
             tpV (.var "r2") "tm:txAdded" "?t2", tpV (.var "t2") "sys:author" "?a2"]))
          (tpV (.var "r1") "tm:validFrom" "?f1") none) (tpV (.var "r1") "tm:validTo" "?u1") none)
          (tpV (.var "r2") "tm:validFrom" "?f2") none) (tpV (.var "r2") "tm:validTo" "?u2") none))
    checkEq "contradictions between sources" (← rowsAll "contradictions" f4 (qq (q4)) ["o1", "o2"])
      [[some (v "acme"), some (v "globex")]]
    -- When we learned it: recorded after it stopped being true
    let f5 ← buildBoth "recipe-learned2" [do let _ ← assertV (v "bob") (v "worksAt") (v "acme") { vFrom := some 0, vTo := some 500 }; pure (),
      do let _ ← assertV (v "carol") (v "worksAt") (v "acme") { vFrom := some 0, vTo := some 10000000 }; pure ()]
    checkEq "recorded after it stopped being true" (← rowsAll "learned" f5 (qq (.project ["s"] false
      (.filter (.cmp .gt (x "a") (x "to")) (.join [tpE "?s" "worksAt" "?o" "r", tpV (.var "r") "tm:addedAt" "?a",
        tpV (.var "r") "tm:validTo" "?to"])))) ["s"]) [[some (v "bob")]]
    -- Answers that cite their facts, and stale answers
    let f6 ← buildBoth "recipe-cite" [do let _ ← assertV (v "alice") (v "worksAt") (v "acme"); pure (),
      do let _ ← retractE (stmt 1); pure ()]
    match (Prov.evalQueryProv {} [] (qq (tp "alice" "worksAt" "?c" (View.ViewSpec.asOfT 1)))).run.onModel f6.st with
    | .ok (.ok (_, rows)) =>
      checkEq "cited eids" (rows.map (·.2)) [[(stmt 1).raw]]
      checkEq "stale: retracted by transaction 2" (← rowsAll "stale" f6
        (qq (tpV (.const (.stmt 1)) "tm:txRetracted" "?t" |> fun o => match o with
            | .triple t => .triple { t with view := { tx := .history } }
            | o => o)) ["t"]) [[some (.tx 2)]]
    | _ => check "cited eids" false
    -- Portable facts with import provenance
    let fa ← buildBoth "recipe-portable" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← assertI e1.eid (v "confidence") (.decimal "0.9"); pure ()]
    match (Bundle.exportBundle {} (stmt 1)).run.onModel fa.st with
    | .ok (.ok b) =>
      let text := b.toJson
      match Bundle.Bundle.fromJson text with
      | .ok b' =>
        let (r1, st1) := Model.transact 5000 {} (do
          let rep ← Bundle.importBundle b'
          let _ ← assertV (.tx 1) (sysV "source") (v "agentA")
          pure rep) Test.Store.freshModelState
        checkEq "portable fact imported" (r1.toOption.map (·.1.statements.length)) (some 2)
        let (r2, _) := Model.transact 6000 {} (Bundle.importBundle b') st1
        checkEq "importing twice changes nothing" (r2.toOption.map (·.1.statements.map (·.new))) (some [false, false])
      | .error e => check "portable json" false (toString e)
    | _ => check "portable export" false
    -- Reasoning inside one graph
    let f7 ← buildBoth "recipe-graph" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let e2 ← TxProg.verb (.assert (← enc (v "belief9")) (← enc (v "supportedBy")) e1.eid {})
      let e3 ← assertV (v "bob") (v "knows") (v "carol")
      let _ ← TxProg.verb (.addToGraph e2.eid (← enc (v "session12")) {})
      let _ ← TxProg.verb (.addToGraph e1.eid (← enc (v "session12")) {})
      let _ ← TxProg.verb (.addToGraph e3.eid (← enc (v "session13")) {}); pure ()]
    checkEq "walk confined to a graph" (← rowsAll "graph walk" f7
      (qq (.project ["x"] false (path (.const (v "belief9")) (.var "x") "supportedBy/(sys:subject|sys:object)+"
          (graph := .set [.const (v "session12")])))) ["x"]) [[some (v "acme")], [some (v "alice")]]
    let perGraph ← rowsAll "per graph" f7 (qq (.project ["g", "x"] false (path (.const (v "bob")) (.var "x") "knows+" (graph := .var "g")))) ["g", "x"]
    checkEq "one row set per graph" perGraph [[some (v "session13"), some (v "carol")]]
    pure () : TestM Unit).run {}
  finish "recipes" r

end Test.Query.Recipes
