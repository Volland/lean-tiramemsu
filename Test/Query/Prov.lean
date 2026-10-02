/-
Scenarios of query-provenance, on the model store and on SQLite, plus erasure: the provenance
rows without their citations equal the plain rows.
-/
import Test.Query.Util
import Tiramemsu.Prov.EvalProv

namespace Test.Query.Prov

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Prov
open Test
open Test.Store (v sysV assertV createV enc day retractE between stmt)
open Test.Query

def provModel (st : ModelState) (q : Query) : Except QError (Prepared × ABag) :=
  match (evalQueryProv {} [] q).run.onModel st with
  | .ok r => r
  | .error e => .error (.store e)

def provSqlite (f : Fix) (q : Query) : IO (Except QError (Prepared × ABag)) := do
  match ← onSqlite f.db (evalQueryProv {} [] q).run with
  | .ok r => pure r
  | .error e => pure (.error (.store e))

def eidN (n : Nat) : Int64 := (stmt n).raw

/-- The projected rows with their citations (as statement numbers), canonically ordered. -/
def cited (p : Prepared) (b : ABag) : List (List (Option Value) × List Int64) :=
  (b.map fun (r, es) => (p.project r, es)).mergeSort fun a c => rowLe a.1 c.1

def runProv (name : String) (f : Fix) (q : Query) (want : List (List (Option Value) × List Nat)) : TestM Unit := do
  match provModel f.st q, ← provSqlite f q, evalModel f.st [] q with
  | .ok (p, b), .ok (_, b'), .ok (_, plain) =>
    checkEq s!"{name}" (cited p b) ((want.map fun (r, es) => (r, es.map eidN)).mergeSort fun a c => rowLe a.1 c.1)
    checkEq s!"{name} [sqlite]" (cited p b') (cited p b)
    checkEq s!"{name} [erasure]" (canon (b.map (·.1))) (canon plain)
  | a, _, _ => check name false (showErr a)

def main : IO UInt32 := do
  let (_, r) ← (do
    let f ← buildBoth "prov1" [do
      let _ ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← assertV (v "acme") (v "locatedIn") (v "paris")
      let _ ← assertV (v "bob") (v "worksAt") (v "acme")
      let _ ← assertV (v "carol") (v "worksAt") (v "globex")
      let _ ← assertV (v "dave") (v "worksAt") (v "acme")
      pure ()]
    runProv "basic graph pattern" f
      { root := .project ["c", "city"] false (.join [tp "alice" "worksAt" "?c", tp "?c" "locatedIn" "?city"]) }
      [([some (v "acme"), some (v "paris")], [1, 2])]
    runProv "optional present and absent" f
      { root := .project ["x", "city"] false (.leftJoin (tp "?x" "worksAt" "?c") (tp "?c" "locatedIn" "?city") none) }
      [([some (v "alice"), some (v "paris")], [1, 2]), ([some (v "bob"), some (v "paris")], [2, 3]),
       ([some (v "carol"), none], [4]), ([some (v "dave"), some (v "paris")], [2, 5])]
    runProv "existence test not cited" f
      { root := .project ["x"] false (.filter (.exists (tp "?c" "locatedIn" "?k") false) (tp "?x" "worksAt" "?c")) }
      [([some (v "alice")], [1]), ([some (v "bob")], [3]), ([some (v "dave")], [5])]
    runProv "distinct merges" f { root := .project ["c"] true (tp "?x" "worksAt" "?c") }
      [([some (v "acme")], [1, 3, 5]), ([some (v "globex")], [4])]
    runProv "group provenance" f { root := .agg ["c"] [{ var := "n", func := .count }] (tp "?x" "worksAt" "?c") }
      [([some (v "acme"), some (.int 3)], [1, 3, 5]), ([some (v "globex"), some (.int 1)], [4])]
    -- two episodes of one content under SetOfTriples
    let f2 ← buildBoth "prov2" [do
      let _ ← createV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2021-01-01")
      let _ ← createV (v "alice") (v "worksAt") (v "acme") (between "2022-01-01" "2023-01-01"); pure ()]
    runProv "two episodes" f2 { root := tp "alice" "worksAt" "?c" } [([some (v "acme")], [1, 2])]
    -- retracted statement cited from the past; stale answer detection
    let f3 ← buildBoth "prov3" [do let _ ← assertV (v "alice") (v "worksAt") (v "acme"); pure (),
                                do let _ ← retractE (stmt 1); pure ()]
    runProv "retracted cited from the past" f3 { root := tp "alice" "worksAt" "?c" (View.ViewSpec.asOfT 1) }
      [([some (v "acme")], [1])]
    checkEq "stale: not visible now" ((Model.query f3.st {} (ReadProg.query (.triples (some (stmt 1)) none none))).toOption.map (·.size)) (some 0)
    match Model.query f3.st { tx := .history } (do return (← ReadProg.query (.triples none none none)).toList) with
    | .ok rows => checkEq "stale: history shows the retraction" (rows.map (·.tRet)) [some 2]
    | .error e => check "stale" false (toString e)
    -- a trail cites its hops
    let f4 ← buildBoth "prov4" [do
      let _ ← assertV (v "a") (v "knows") (v "b")
      let _ ← assertV (v "b") (v "knows") (v "c"); pure ()]
    let pp : PathPattern := { start := .const (v "a"), «end» := .var "y", path := .plus (.atom (Vocab.vIri "knows")), mode := .trail }
    runProv "trail cites hops" f4 { root := .path pp } [([some (v "b")], [1]), ([some (v "c")], [1, 2])]
    runProv "reach cites nothing" f4 { root := .path { pp with mode := .reach } } [([some (v "b")], []), ([some (v "c")], [])]
    pure () : TestM Unit).run {}
  finish "provenance scenarios" r

end Test.Query.Prov
