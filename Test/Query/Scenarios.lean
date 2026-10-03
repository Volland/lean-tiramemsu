/-
Scenarios of query-ir, query-semantics and nested-loop-join on the model store. Every query
runs through the reference semantics and the evaluator; both must agree as bags, and the
reference result must match the scenario.
-/
import Test.Query.Util

namespace Test.Query.Scenarios

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem
open Test
open Test.Store (v sysV assertV createV enc day retractE between)
open Test.Query

/-- Runs a query both ways; checks agreement and returns the projected reference rows. -/
def runQ (name : String) (f : Fix) (q : Query) (ps : Params := []) :
    TestM (Except QError (List Var × List (List (Option Value)))) := do
  let d := denoteQ f.st ps q
  let e := evalModel f.st ps q
  let sq ← evalSqlite f.db ps q
  match d, e, sq with
  | .ok (p, b), .ok (_, b'), .ok (_, b'') =>
    checkEq s!"{name}: evaluator = reference" (canon b') (canon b)
    checkEq s!"{name}: SQLite = model" (canon b'') (canon b')
    return .ok (p.columns, rowsOf p b)
  | .error e1, .error e2, .error e3 =>
    checkEq s!"{name}: same error" e2.code e1.code
    checkEq s!"{name}: same SQLite error" e3.code e1.code
    return .error e1
  | _, _, _ =>
    check s!"{name}: evaluator and reference disagree on success" false s!"reference {showErr d}, evaluator {showErr e}, sqlite {showErr sq}"
    return .error (.invalidQuery "disagreement")

def expectRows (name : String) (st : Fix) (q : Query) (want : List (List (Option Value)))
    (ps : Params := []) : TestM Unit := do
  match ← runQ name st q ps with
  | .ok (_, rows) => checkEq name rows (want.mergeSort fun a b => rowLe a b)
  | .error e => check name false s!"error {e}"

def expectErr (name : String) (st : Fix) (q : Query) (code : String) (ps : Params := []) : TestM Unit := do
  match ← runQ name st q ps with
  | .ok _ => check name false "expected an error"
  | .error e => checkEq name e.code code

def sp (o : IR.Op) : Query := { root := o, sem := .sparql }
def cy (o : IR.Op) : Query := { root := o, sem := .cypher }

def some' (x : Value) : Option Value := some x

def main : IO UInt32 := do
  let (_, r) ← (do
    -- a small company graph
    let st ← buildBoth "q1" [facts [("alice", "worksAt", v "acme"), ("bob", "worksAt", v "acme"),
                            ("carol", "worksAt", v "globex"), ("acme", "locatedIn", v "paris"),
                            ("alice", "knows", v "bob"), ("bob", "knows", v "carol"),
                            ("alice", "age", .int 31), ("bob", "age", .str "old"),
                            ("alice", "name", .str "alice"), ("bob", "name", .str "bob"),
                            ("alice", "vip", .bool false), ("carol", "vip", .bool true)]]
    -- query-ir: Basic graph pattern / implicit column order
    match ← runQ "bgp" st (sp (.join [tp "?a" "knows" "?b", tp "?b" "worksAt" "?c"])) with
    | .ok (cols, rows) =>
      checkEq "implicit column order" cols ["a", "b", "c"]
      checkEq "bgp rows" rows.length 2
    | .error e => check "bgp" false (toString e)
    -- Empty join is the unit relation
    expectRows "unit relation" st (sp (.join [])) [[]]
    -- Inline values with an undefined cell
    expectRows "values undefined cell" st
      (sp (.values ["x", "y"] [[some (.const (v "alice")), none]])) [[some (v "alice"), none]]
    -- Parameter as a pattern constant / missing parameter
    expectRows "parameter constant" st (sp (.project ["x"] false (tp "?x" "worksAt" "$org")))
      [[some (v "alice")], [some (v "bob")]] [("org", v "acme")]
    expectErr "missing parameter" st (sp (tp "?x" "worksAt" "$org")) "InvalidQuery"
    -- Project fixes column order
    match ← runQ "project order" st (sp (.project ["c", "a"] false (.join [tp "?a" "worksAt" "?c"]))) with
    | .ok (cols, _) => checkEq "project column order" cols ["c", "a"]
    | .error e => check "project order" false (toString e)
    -- Unknown IRI constant: no rows, dictionary unchanged
    expectRows "unknown constant" st (sp (tp "?x" "worksAt" "neverSeen")) []
    expectRows "union with one empty branch" st
      (sp (.union [tp "?x" "worksAt" "neverSeen", tp "?x" "worksAt" "acme"]))
      [[some (v "alice")], [some (v "bob")]]
    expectRows "extend unknown constant" st (sp (.extend "y" (c (.str "neverStored")) (.join [])))
      [[some (.str "neverStored")]]
    -- Validation
    expectErr "extend rebinds" st (sp (.extend "x" (c (.int 1)) (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "ragged values" st (sp (.values ["x", "y"] [[some (.const (.int 1)), some (.const (.int 2)), some (.const (.int 3))]])) "InvalidQuery"
    expectErr "negative limit" st (sp (.orderLimit [] none (some (.const (.int (-1)))) (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "empty graph set" st (sp (tpt { s := term "?x", p := term "p", o := term "?y", graph := .set [] })) "InvalidQuery"
    expectErr "project unbound" st (sp (.project ["zz"] false (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "wrong arity" st (sp (.filter (.func .strLen []) (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "virtual eid" st (sp (tpt { s := term "?e", p := term "sys:subject", o := term "?s", eid := some "k" })) "InvalidQuery"
    expectErr "aggregate collision" st (sp (.agg ["x"] [{ var := "x", func := .count }] (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "aggregate without argument" st (sp (.agg [] [{ var := "n", func := .sum }] (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "values cell variable" st (sp (.values ["x"] [[some (.var "y")]])) "InvalidQuery"
    expectErr "values repeated variable" st (sp (.values ["x", "x"] [[none, none]])) "InvalidQuery"
    expectErr "graph set variable" st (sp (tpt { s := term "?x", p := term "p", o := term "?y", graph := .set [term "?g"] })) "InvalidQuery"
    expectErr "virtual by graph" st (sp (tpt { s := term "?e", p := term "sys:subject", o := term "?s", graph := .var "g" })) "InvalidQuery"
    expectErr "non-integer skip" st (sp (.orderLimit [] (some (.const (.str "a"))) none (tp "?x" "p" "?y"))) "InvalidQuery"
    expectErr "negative skip param" st (sp (.orderLimit [] (some (.param "k")) none (tp "?x" "p" "?y"))) "InvalidQuery" [("k", .int (-2))]
    expectRows "count star valid" st (sp (.agg [] [{ var := "n", func := .count }] (tp "?x" "worksAt" "?c")))
      [[some (.int 3)]]
    checkEq "mode parse" (PathMode.parse? "all_shortest") (some .allShortest)
    checkEq "mode unsupported" (PathMode.parse? "SIMPLE") none
    checkEq "presets" (Semantics.sparql, Semantics.cypher)
      ({ matchMode := .homomorphism, missing := .unbound, graphSet := .setOfTriples },
       { matchMode := .relIsomorphism, missing := .null3VL, graphSet := .bagOfEids })
    -- Repeated variable
    let st2 ← buildBoth "q2" [facts [("a", "knows", v "a"), ("a", "knows", v "b")]]
    expectRows "repeated variable" st2 (sp (tp "?x" "knows" "?x")) [[some (v "a")]]
    -- Same tree, different graph set (parallel statements by create)
    let st3 ← buildBoth "q3" [do let _ ← createV (v "a") (v "knows") (v "b"); let _ ← createV (v "a") (v "knows") (v "b"); pure ()]
    expectRows "set of triples" st3 (sp (tp "?x" "knows" "?y")) [[some (v "a"), some (v "b")]]
    expectRows "bag of eids" st3 { root := tp "?x" "knows" "?y", sem := { graphSet := .bagOfEids } }
      [[some (v "a"), some (v "b")], [some (v "a"), some (v "b")]]
    -- Relationship isomorphism groups
    let st4 ← buildBoth "q4" [facts [("a", "knows", v "b")]]
    let grp (s o : String) : IR.Op := tpt { s := term s, p := term "knows", o := term o, isoGroup := some 1 }
    match ← runQ "iso" st4 { root := .project ["x", "y"] false (.join [grp "a" "?x", grp "?y" "b"]), sem := { matchMode := .relIsomorphism } } with
    | .ok (_, rows) => checkEq "isomorphism empty" rows.length 0
    | .error e => check "iso" false (toString e)
    expectRows "homomorphism one row" st4 (sp (.join [grp "a" "?x", grp "?y" "b"])) [[some (v "b"), some (v "a")]]
    -- Graphs: statement in two graphs of the set, one row per membership
    let st5 ← buildBoth "q5" [do
      let e ← assertV (v "a") (v "p") (v "b")
      let g1 ← enc (v "g1"); let g2 ← enc (v "g2")
      let _ ← TxProg.verb (.addToGraph e.eid g1 {})
      let _ ← TxProg.verb (.addToGraph e.eid g2 {})
      pure ()]
    expectRows "graph set once" st5
      (sp (tpt { s := term "?x", p := term "p", o := term "?y", graph := .set [term "g1", term "g2"] }))
      [[some (v "a"), some (v "b")]]
    expectRows "graph var per membership" st5
      (sp (tpt { s := term "?x", p := term "p", o := term "?y", graph := .var "g" }))
      [[some (v "a"), some (v "b"), some (v "g1")], [some (v "a"), some (v "b"), some (v "g2")]]
    -- Virtual predicates
    let st6 ← buildBoth "q6" [facts [("alice", "worksAt", v "acme")]]
    let e1 : TermOrVar := .const (.stmt 1)
    expectRows "virtual subject" st6 (sp (tpt { s := e1, p := term "sys:subject", o := term "?s" })) [[some (v "alice")]]
    expectRows "live has no retraction" st6 (sp (tpt { s := e1, p := term "tm:txRetracted", o := term "?t" })) []
    expectRows "variable predicate ignores virtual" st6 (sp (tpt { s := e1, p := term "?p", o := term "?o" })) []
    -- Compatibility
    expectRows "unbound joins" st
      (sp (.join [.values ["x"] [[none]], .values ["x"] [[some (.const (v "a"))]]])) [[some (v "a")]]
    expectRows "null never joins" st
      (cy (.join [.values ["x"] [[none]], .values ["x"] [[some (.const (v "a"))]]])) []
    expectRows "distinct terms" st
      (sp (.join [.values ["x"] [[some (.const (.int 1))]], .values ["x"] [[some (.const (.decimal "1.0"))]]])) []
    -- Optional absent, union keeps duplicates
    expectRows "optional absent" st
      (sp (.project ["x", "c", "city"] false (.leftJoin (tp "?x" "worksAt" "?c") (tp "?c" "locatedIn" "?city") none)))
      [[some (v "alice"), some (v "acme"), some (v "paris")], [some (v "bob"), some (v "acme"), some (v "paris")],
       [some (v "carol"), some (v "globex"), none]]
    expectRows "union duplicates" st (sp (.union [.values ["x"] [[some (.const (v "a"))]], .values ["x"] [[some (.const (v "a"))]]]))
      [[some (v "a")], [some (v "a")]]
    -- Three-valued logic
    expectRows "error drops row" st
      (sp (.project ["x"] false (.filter (.cmp .gt (x "age") (c (.int 30))) (tp "?x" "age" "?age"))))
      [[some (v "alice")]]
    expectRows "or absorbs error" st
      (sp (.project ["x"] false (.filter (.or [.cmp .gt (x "age") (c (.int 30)), eq (x "vip") (c (.bool true))])
        (.leftJoin (tp "?x" "vip" "?vip") (tp "?x" "age" "?age") none))))
      [[some (v "alice")], [some (v "carol")]]
    expectRows "mixed numeric" st (sp (.filter (.cmp .lt (x "x") (c (.decimal "2.5"))) (.values ["x"] [[some (.const (.int 2))]])))
      [[some (.int 2)]]
    -- Aggregation
    expectRows "count over empty" st (sp (.agg [] [{ var := "n", func := .count }] (tp "?x" "worksAt" "neverSeen")))
      [[some (.int 0)]]
    expectRows "grouped empty" st (sp (.agg ["c"] [{ var := "n", func := .count }] (tp "?x" "worksAt" "neverSeen"))) []
    expectRows "group count" st (sp (.agg ["c"] [{ var := "n", func := .count }] (tp "?x" "worksAt" "?c")))
      [[some (v "acme"), some (.int 2)], [some (v "globex"), some (.int 1)]]
    -- Ordering
    match ← runQ "order" st (sp (.order [{ expr := x "n" }] none none (tp "?x" "name" "?n"))) with
    | .ok (_, _) =>
      match denoteQ st.st [] (sp (.order [{ expr := x "n" }] none none (tp "?x" "name" "?n"))) with
      | .ok (p, b) => checkEq "strings sort by value" ((b.map p.project).map (·.getD 1 none)) [some (.str "alice"), some (.str "bob")]
      | .error e => check "order" false (toString e)
    | .error e => check "order" false (toString e)
    -- EXISTS correlation, not cited
    expectRows "exists" st
      (sp (.project ["x"] false (.filter (.exists (tp "?x" "knows" "?k") false) (tp "?x" "worksAt" "?c"))))
      [[some (v "alice")], [some (v "bob")]]
    -- Two views in one query
    let st7 ← buildBoth "q7" [facts [("alice", "worksAt", v "acme")],
      do let _ ← retractE (Test.Store.stmt 1); let _ ← assertV (v "alice") (v "worksAt") (v "globex"); pure ()]
    expectRows "two views" st7
      (sp (.join [tp "alice" "worksAt" "?before" (View.ViewSpec.asOfT 1), tp "alice" "worksAt" "?after"]))
      [[some (v "acme"), some (v "globex")]]
    -- Eid binding: annotation on a statement; eid equal to a constant
    let st8 ← buildBoth "qeid" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← Test.Store.assertI e1.eid (v "confidence") (.decimal "0.8")
      let _ ← assertV (v "bob") (v "worksAt") (v "acme"); pure ()]
    expectRows "annotation on a statement" st8
      (sp (.project ["x"] false (.join [tpe "alice" "worksAt" "?c" "e", tp "?e" "confidence" "?x"])))
      [[some (.decimal "0.8")]]
    expectRows "eid equal to a constant" st8
      (sp (.project ["c"] false (tpt { s := term "?s", p := term "worksAt", o := term "?c", eid := some "e" } |> fun o =>
        .join [.values ["e"] [[some (.const (.stmt 3))]], o])))
      [[some (v "acme")]]
    -- Overlaying one part of a view
    let d : Int64 := 1700000000000
    checkEq "overlay one part" (overlayView ((View.ViewSpec.now).validAt d) (some (.asOf (.tx 150))) none)
      { tx := .asOf (.tx 150), valid := .at d }
    -- Double arithmetic: one IEEE result, deterministic
    expectRows "double arithmetic" st (sp (.extend "y" (.arith .mul (x "x") (c (.double ⟨0x3FB999999999999A⟩)))
      (.values ["x"] [[some (.const (.double ⟨0x4008000000000000⟩))]])))
      [[some (.double ⟨0x4008000000000000⟩), some (.double ⟨0x3FD3333333333334⟩)]]
    -- Ties are deterministic under two join orders
    let tied (o : List IR.Op) : Query := sp (.order [{ expr := c (.int 1) }] none none (.join o))
    match denoteQ st.st [] (tied [tp "?a" "worksAt" "?c", tp "?c" "locatedIn" "?l"]),
          evalModel st.st [] (tied [tp "?c" "locatedIn" "?l", tp "?a" "worksAt" "?c"]) with
    | .ok (p, b), .ok (p', b') =>
      checkEq "ties are deterministic" ((b'.map fun r => ["a", "c", "l"].map fun n => r.get (p'.vars.idxOf n)))
        ((b.map fun r => ["a", "c", "l"].map fun n => r.get (p.vars.idxOf n)))
    | _, _ => check "ties" false
    -- Recompute after later writes (AsOf stability)
    let q150 : Query := sp (tp "?x" "worksAt" "?c" (View.ViewSpec.asOfT 1))
    let before := denoteQ st7.st [] q150
    let later ← buildBoth "qlater" [facts [("alice", "worksAt", v "acme")],
      do let _ ← retractE (Test.Store.stmt 1); let _ ← assertV (v "alice") (v "worksAt") (v "globex"); pure (),
      facts [("zed", "worksAt", v "acme")], facts [("ann", "worksAt", v "globex")]]
    checkEq "stable as of 1 after later writes" ((denoteQ later.st [] q150).toOption.map fun (p, b) => rowsOf p b)
      (before.toOption.map fun (p, b) => rowsOf p b)
    -- nested-loop-join: optional variable not pushed
    expectRows "not bound optional" st
      (sp (.project ["c"] true (.filter (.not (.bound "city"))
        (.leftJoin (tp "?x" "worksAt" "?c") (tp "?c" "locatedIn" "?city") none))))
      [[some (v "globex")]]
    expectRows "constant equality pushed" st
      (sp (.project ["x"] false (.filter (eq (x "c") (c (v "acme"))) (tp "?x" "worksAt" "?c"))))
      [[some (v "alice")], [some (v "bob")]]
    -- statistics change only speed: wrong counts give the same bag
    let qs := sp (.join [tp "?a" "knows" "?b", tp "?b" "worksAt" "?c", tp "?c" "locatedIn" "?d"])
    for bogus in [fun (_ : Value) => some 0, fun _ => some 1000000, fun p => if p == v "knows" then some 5 else none] do
      match (Exec.evalQueryWith (Path.evalPath {}) [] qs bogus).run.onModel st.st, denoteQ st.st [] qs with
      | .ok (.ok (_, b')), .ok (_, b) => checkEq "statistics change only speed" (canon b') (canon b)
      | _, _ => check "statistics" false
    -- every order agrees (4 patterns, 24 orders)
    let pats := [tp "?a" "knows" "?b", tp "?b" "worksAt" "?c", tp "?c" "locatedIn" "?d", tp "?a" "name" "?n"]
    let ref := denoteQ st.st [] (sp (.join pats))
    let cols := ["a", "b", "c", "d", "n"]
    for perm in perms pats do
      match ref, evalModel st.st [] (sp (.join perm)) with
      | .ok (p, b), .ok (p', b') => checkEq "every order agrees" (rowsBy p' cols b') (rowsBy p cols b)
      | _, _ => check "every order agrees" false "error"
    -- regression: constant equalities seed key prefixes only for identity constants. A statement
    -- id beyond 2^64 shares its sort key with a small one but is a different value; a language
    -- string with a NUL shares its key with another split of the same bytes (not seeded).
    let big : Nat := 2 ^ 64
    let sl ← buildBoth "q-seed" [facts [("alice", "label", .langStr "a\x00x" "y")]]
    for k in [1, 2, 3, 4] do
      expectRows s!"seed: statement id {k} + 2^64" st
        (sp (.project ["x"] false (.filter (eq (x "e") (c (.stmt (big + k)))) (tpe "?x" "worksAt" "?c" "e")))) []
      expectRows s!"seed: statement id {k} + 2^64, constant first" st
        (sp (.project ["x"] false (.filter (eq (c (.stmt (big + k))) (x "e")) (tpe "?x" "worksAt" "?c" "e")))) []
    expectRows "seed: language string with NUL" sl
      (sp (.project ["x"] false (.filter (eq (x "o") (c (.langStr "a" "x\x00y"))) (tp "?x" "label" "?o"))))
      [[some (v "alice")]]
    sl.db.close
    pure () : TestM Unit).run {}
  finish "query scenarios" r

end Test.Query.Scenarios
