/-
Scenarios of lean-api on SQLite files through the public API, including the listed deviations.
-/
import Test.Query.Util
import Tiramemsu.Api.Api

namespace Test.Query.ApiTest

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Api
open Test
open Test.Store (v sysV assertV assertI createV enc day retractE between stmt)
open Test.Query (tp term)

def ok! {α : Type} (what : String) : Except ApiError α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def codeOf {α : Type} : Except ApiError α → String
  | .ok _ => "ok"
  | .error e => e.code

def openFresh (name : String) (opts : OpenOptions := {}) : IO Api.Db := do
  let p ← freshPath s!"api-{name}"
  ok! "open" (← Api.Db.open p opts)

def main : IO UInt32 := do
  let (_, r) ← (do
    let clock ← Shell.ManualClock.new 1000
    let db ← openFresh "a" { clock := clock.clock }
    -- failed transaction leaves no trace
    let before ← db.now.triples none none none
    let bad ← db.transact (do
      let _ ← assertV (v "a") (v "p") (v "b")
      let _ ← assertV (v "c") (v "p") (v "d")
      TxProg.abort (.custom "boom") : TxProg Unit)
    checkEq "failed transaction error" (codeOf bad) "Custom"
    checkEq "failed transaction leaves no trace" ((← db.now.triples none none none).toOption.map (·.length)) (before.toOption.map (·.length))
    -- three transactions at known instants
    for (i, (s, o)) in [("alice", "acme"), ("acme", "paris"), ("bob", "acme")].zipIdx.map (fun (x, i) => (i, x)) do
      clock.set (1000 * (i + 1))
      let _ ← ok! "tx" (← db.transact (do let _ ← assertV (v s) (v (if i == 1 then "locatedIn" else "worksAt")) (v o); pure ()))
    -- speculative query
    let spec ← db.with (do let _ ← assertV (v "alice") (v "worksAt") (v "globex"); pure ())
      { root := .project ["c"] false (tp "alice" "worksAt" "?c") }
    checkEq "speculative query sees globex" ((spec.toOption.map (·.rows)).map (·.contains [some (v "globex")])) (some true)
    let after ← db.now.triples (some (v "alice")) (some (v "worksAt")) (some (v "globex"))
    checkEq "database afterwards does not" (after.toOption.map (·.length)) (some 0)
    -- as of an instant equals as of a transaction
    let a1 ← db.asOf (.instant 2500) |>.execute { root := tp "?x" "?p" "?y" }
    let a2 ← db.asOf (.tx 2) |>.execute { root := tp "?x" "?p" "?y" }
    checkEq "as of instant = as of tx" (a1.toOption.map (·.rows.length)) (a2.toOption.map (·.rows.length))
    -- encode never inserts
    let e1 ← db.now.encode (v "neverSeenIri")
    checkEq "encode of an absent IRI" (e1.toOption) (some none)
    checkEq "encode inserted nothing" ((← db.now.encode (v "neverSeenIri")).toOption) (some none)
    -- execute a two-pattern join
    match ← db.now.execute { root := .join [tp "?a" "worksAt" "?c", tp "?c" "locatedIn" "?city"] } with
    | .ok res =>
      checkEq "execute columns" res.columns ["a", "c", "city"]
      checkEq "execute rows" res.rows.length 2
    | .error e => check "execute" false (toString e)
    -- invalid query fails before reading (on a closed database it would otherwise fail on I/O)
    checkEq "invalid query" (codeOf (← db.now.execute { root := .extend "a" (.const (.int 1)) (tp "?a" "p" "?b") })) "InvalidQuery"
    checkEq "missing parameter" (codeOf (← db.now.execute { root := tp "?a" "p" "$x" })) "InvalidQuery"
    -- provenance
    match ← db.now.execute { root := .join [tp "alice" "worksAt" "?c", tp "?c" "locatedIn" "?city"] } (provenance := true) with
    | .ok res => checkEq "provenance cites both" (res.cites.map (·.map (·.length))) (some [2])
    | .error e => check "provenance" false (toString e)
    -- reach from the API
    let db2 ← openFresh "b"
    let _ ← ok! "tx" (← db2.transact (do
      let _ ← assertV (v "a") (v "knows") (v "b")
      let _ ← assertV (v "b") (v "knows") (v "c"); pure ()))
    let some a ← ok! "enc" (← db2.now.encode (v "a")) | check "encode a" false
    match ← db2.now.path a "knows+" with
    | .ok rows => checkEq "reach from the API" (rows.map (·.hops)) [1, 2]
    | .error e => check "reach" false (toString e)
    match ← db2.now.pathWith a "knows+" { timeRespecting := some none } with
    | .ok rows => checkEq "time-respecting arrival absent at −∞" (rows.map (·.arrival)) [none, none]
    | .error e => check "time respecting" false (toString e)
    -- path limit error
    let db3 ← openFresh "c" { pathMaxStates := 2 }
    let _ ← ok! "tx" (← db3.transact (do
      let _ ← assertV (v "a") (v "knows") (v "b")
      let _ ← assertV (v "b") (v "knows") (v "c"); pure ()))
    let some a3 ← ok! "enc" (← db3.now.encode (v "a")) | check "encode a" false
    checkEq "path limit error" (codeOf (← db3.now.path a3 "knows*" .trail)) "PathLimitExceeded"
    -- explain a chain join
    match db.now.explain { root := .join [tp "alice" "knows" "?b", tp "?b" "worksAt" "?c"] } with
    | .ok plan =>
      let txt := plan.text
      check "explain lists spo prefixes" ((txt.splitOn "via spo").length == 3) txt
      check "explain is deterministic" (txt == (db.now.explain { root := .join [tp "alice" "knows" "?b", tp "?b" "worksAt" "?c"] } |>.toOption |>.map Exec.Plan.text |>.getD ""))
    | .error e => check "explain" false (toString e)
    -- golden plans (text and JSON)
    let plans : List Query := [
      { root := .join [tp "alice" "knows" "?b", tp "?b" "worksAt" "?c"] },
      { root := .filter (.cmp .eq (.var "c") (.const (Test.Store.v "acme"))) (tp "?x" "worksAt" "?c") },
      { root := .project ["x"] true (.leftJoin (tp "?x" "worksAt" "?c") (tp "?c" "locatedIn" "?city") none) },
      { root := .path { start := .const (Test.Store.v "a"), «end» := .var "y", path := .plus (.atom (Vocab.vIri "knows")), mode := .trail } },
      { root := .join [tp "?s" "?p" "?o", .values ["s"] [[some (.const (Test.Store.v "a"))]]] }]
    let mut golden := ""
    for q in plans do
      match db.now.explain q with
      | .ok p => golden := golden ++ p.text ++ "\n" ++ (Tiramemsu.Shell.sortedText p.toJson) ++ "\n---\n"
      | .error e => check "explain" false (toString e)
    let gpath : System.FilePath := "testdata" / "explain" / "golden.txt"
    if ← gpath.pathExists then
      checkEq "golden plans" golden (← IO.FS.readFile gpath)
    else
      IO.FS.createDirAll ("testdata" / "explain")
      IO.FS.writeFile gpath golden
      note "wrote testdata/explain/golden.txt"
    -- double SUM folds in the canonical order (listed deviation): the same result for any insertion order
    let dsum (vals : List Float) : IO (Option (List (Option Value))) := do
      let dd ← openFresh s!"dsum{vals.length}{vals.headD 0}"
      let _ ← ok! "tx" (← dd.transact (do
        for (x, i) in vals.zipIdx do
          let _ ← assertV (Test.Store.v s!"n{i}") (Test.Store.v "w") (.double ⟨x.toBits⟩)
        pure ()))
      let r ← dd.now.execute { root := .agg [] [{ var := "s", func := .sum, arg := some (.var "w") }] (tp "?n" "w" "?w") }
      dd.close
      return r.toOption.bind (·.rows.head?)
    checkEq "double sum is canonical" (← dsum [1e16, 1.0, -1e16, 1.0]) (← dsum [1.0, -1e16, 1.0, 1e16])
    -- portable fact between two files
    let dbA ← openFresh "fa"
    let dbB ← openFresh "fb"
    let (root, _) ← ok! "tx" (← dbA.transact (do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← assertI e1.eid (v "confidence") (.decimal "0.8"); pure e1.eid))
    let b ← ok! "bundle" (← dbA.now.bundle root)
    let b' ← match Bundle.Bundle.fromJson (Bundle.Bundle.toJson b) with
      | .ok x => pure x
      | .error e => throw (IO.userError (toString e))
    let (rep, _) ← ok! "import" (← dbB.transact (Tx.importBundle b'))
    checkEq "portable fact" (rep.statements.map (·.new)) [true, true]
    checkEq "fresh eids hold the fact" ((← dbB.now.triples none none none).toOption.map (·.length)) (some 2)
    -- valid-time view
    let db4 ← openFresh "d"
    let _ ← ok! "tx" (← db4.transact (do let _ ← assertV (v "a") (v "p") (v "b") (between "2020-01-01" "2021-01-01"); pure ()))
    checkEq "valid at inside" ((← (db4.now.validAt (day "2020-06-01")).triples none none none).toOption.map (·.length)) (some 1)
    checkEq "valid at end excluded" ((← (db4.now.validAt (day "2021-01-01")).triples none none none).toOption.map (·.length)) (some 0)
    -- dependents on a past view
    let db5 ← openFresh "e"
    let (r1, _) ← ok! "tx" (← db5.transact (do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← assertI e1.eid (v "confidence") (.decimal "0.8"); pure e1.eid))
    let _ ← ok! "retract" (← db5.transact (do let _ ← retractE (stmt 2); pure ()))
    checkEq "dependents as of 1" ((← (db5.asOf (.tx 1)).dependents r1).toOption.map (·.length)) (some 2)
    checkEq "dependents now" ((← db5.now.dependents r1).toOption.map (·.length)) (some 1)
    for d in [db, db2, db3, dbA, dbB, db4, db5] do d.close
    pure () : TestM Unit).run {}
  finish "api scenarios" r

end Test.Query.ApiTest
