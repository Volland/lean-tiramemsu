/-
Scenarios of retraction-cascade.
-/
import Test.Store.Run

namespace Test.Store.Cascade

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Test.Store

def tRetOf (h : Harness) (e : ObjectId) : IO (Option Int64) := do
  return (← rowOf h e).bind (·.tRet)

def pad (h : Harness) (n : Nat) : IO Unit := do
  for _ in [0:n] do let _ ← ok! "pad" (← h.tx 1 {} (pure ()))

def layers : Scenario := fun h => do
  let ((e1, e2, e7, e8), _) ← ok! "setup" (← h.tx 1 {} (do
    let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
    let e2 ← assertI e1.eid (v "confidence") (dbl "0.8")
    let e7 ← assertV (v "belief9") (v "supportedBy") (.stmt (ctr e1.eid))
    let e8 ← assertI e7.eid (v "method") (.str "llm")
    pure (e1.eid, e2.eid, e7.eid, e8.eid)))
  pad h 10
  let _ ← ok! "12" (← h.tx 12 {} (retractE e1))
  let ts ← [e1, e2, e7, e8].mapM (tRetOf h)
  pure (expect "t_ret" ts [some 12, some 12, some 12, some 12])

def nodesDoNotCascade : Scenario := fun h => do
  pad h 4
  let ((a, m, c, e1), _) ← ok! "5" (← h.tx 5 {} (do
    let a ← assertV (v "alice") (v "name") (.str "Alice")
    let m ← TxProg.verb (.metadata (← enc (sysV "author")) (← enc (v "agent7")))
    let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
    let c ← TxProg.verb (.confirm e1.eid)
    pure (a.eid, m, c, e1.eid)))
  let _ ← ok! "6" (← h.tx 6 {} (retractE e1))
  pure (expect "t_ret" (← [a, m, c].mapM (tRetOf h)) [none, none, some 6])

def notWalked : Scenario := fun h => do
  let ((e1, e2, e3), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertI e1.eid (v "note") (.str "a")
    let e3 ← assertI e2.eid (v "note") (.str "b")
    pure (e1.eid, e2.eid, e3.eid)))
  let _ ← ok! "2" (← h.tx 2 {} (retractE e2))
  let (e3', _) ← ok! "3" (← h.tx 3 {} (assertI e2 (v "note") (.str "b2")))
  let _ ← ok! "4" (← h.tx 4 {} (retractE e1))
  pure (expect "t_ret" (← [e1, e2, e3, e3'.eid].mapM (tRetOf h)) [some 4, some 2, some 2, none])

def diamond : Scenario := fun h => do
  let ((e1, e2, e3, e4), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p0") (v "b")
    let e2 ← assertI e1.eid (v "p") (v "x")
    let e3 ← assertI e1.eid (v "q") (v "y")
    let e4 ← TxProg.verb (.assert e2.eid (← enc (v "r")) e3.eid {})
    pure (e1.eid, e2.eid, e3.eid, e4.eid)))
  let (_, r) ← ok! "2" (← h.tx 2 {} (retractE e1))
  pure (expect "report" (kindsOf r.retracted)
    [(ctr e1, .explicit), (ctr e2, .cascade), (ctr e3, .cascade), (ctr e4, .cascade)])

def cycle : Scenario := fun h => do
  let ((e1, e2, e3), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertI e1.eid (v "x") (.stmt (ctr e1.eid + 2))
    let e3 ← TxProg.verb (.assert e2.eid (← enc (v "y")) e1.eid {})
    pure (e1.eid, e2.eid, e3.eid)))
  let (_, r) ← ok! "2" (← h.tx 2 {} (retractE e1))
  pure (expect "each once" (kindsOf r.retracted) [(ctr e1, .explicit), (ctr e2, .cascade), (ctr e3, .cascade)])

def cardinalityKinds : Scenario := fun h => do
  let ((e1, e2), _) ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "age" "cardinality" (sysV "one")
    let e1 ← assertV (v "alice") (v "age") (.int 30)
    let e2 ← assertI e1.eid (v "source") (v "form")
    pure (e1.eid, e2.eid)))
  let (n, r) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "age") (.int 31)))
  let deps ← ok! "q" (← h.query nowV (depsQ n.eid))
  pure <| allOk [expect "kinds" (kindsOf r.retracted) [(ctr e1, .cardinality), (ctr e2, .cardinality)],
    expect "no annotations carried" deps [ctr n.eid]]

def annotated (n : Nat) : TxProg ObjectId := do
  let e ← assertV (v "root") (v "p") (.int n)
  for i in [0:n] do let _ ← assertI e.eid (v "note") (.int i)
  pure e.eid

def atLimit : Scenario := fun h => do
  let (e, _) ← ok! "1" (← h.tx 1 {} (annotated 4))
  let (_, r) ← ok! "2" (← h.tx 2 { maxCascade := 5 } (retractE e))
  pure (expect "five" r.retracted.size 5)

def overLimit : Scenario := fun h => do
  let (e, _) ← ok! "1" (← h.tx 1 {} (annotated 5))
  let before ← h.tables
  let r ← h.tx 2 { maxCascade := 5 } (retractE e)
  pure <| allOk [
    (match r with
     | .error (.cascadeLimitExceeded root l) => expect "names" (root, l) (e, 5)
     | other => some s!"expected CascadeLimitExceeded, got {errCode other}"),
    expect "no trace" ((← h.tables) == before) true]

def perRoot : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do let _ ← annotated 4; let x ← assertV (v "root2") (v "p") (.int 0)
                                   for i in [0:4] do let _ ← assertI x.eid (v "note") (.int i)))
  let (got, r) ← ok! "2" (← h.tx 2 { maxCascade := 5 } (do TxProg.verb (.retractMatching none (some (← enc (v "p"))) none)))
  pure <| allOk [expect "roots" got.size 2, expect "retracted" r.retracted.size 10]

def defaultLimit : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (annotated 9999))
  let (b, _) ← ok! "2" (← h.tx 2 {} (do
    let e ← assertV (v "root") (v "q") (.int 0)
    for i in [0:10000] do let _ ← assertI e.eid (v "note") (.int i)
    pure e.eid))
  let ra ← h.tx 3 {} (retractE a)
  let rb ← h.tx 4 {} (retractE b)
  pure <| allOk [expect "9999 commits" (ra.toOption.map (·.2.retracted.size)) (some 10000),
    expect "10000 fails" (errCode rb) "CascadeLimitExceeded"]

/-! ## Dependents -/

def backThen : Scenario := fun h => do
  pad h 2
  let ((e1, e2, e7), _) ← ok! "3" (← h.tx 3 {} (do
    let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
    let e2 ← assertI e1.eid (v "confidence") (dbl "0.8")
    let e7 ← assertV (v "belief9") (v "supportedBy") (.stmt (ctr e1.eid))
    pure (e1.eid, e2.eid, e7.eid)))
  let (live, _) ← ok! "in tx" (← h.tx 4 {} (do let d ← TxProg.verb (.dependents e1); let _ ← retractE e1; pure d))
  pure <| allOk [expect "in tx before" (eidsOf live) [ctr e1, ctr e2, ctr e7],
    expect "now" (← ok! "q" (← h.query nowV (depsQ e1))) [],
    expect "as of 3" (← ok! "q" (← h.query (asOf 3) (depsQ e1))) [ctr e1, ctr e2, ctr e7]]

def everDepended : Scenario := fun h => do
  let ((e1, e2), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertI e1.eid (v "note") (.str "old")
    pure (e1.eid, e2.eid)))
  pad h 1
  let _ ← ok! "3" (← h.tx 3 {} (retractE e2))
  let (e3, _) ← ok! "4" (← h.tx 4 {} (assertI e1 (v "note") (.str "new")))
  pure <| allOk [expect "history" (← ok! "q" (← h.query hist (depsQ e1))) [ctr e1, ctr e2, ctr e3.eid],
    expect "now" (← ok! "q" (← h.query nowV (depsQ e1))) [ctr e1, ctr e3.eid]]

def depsLargerThanLimit : Scenario := fun h => do
  let (e, _) ← ok! "1" (← h.tx 1 {} (annotated 20))
  let deps ← ok! "q" (← h.query nowV (depsQ e))
  let r ← h.tx 2 { maxCascade := 10 } (retractE e)
  pure <| allOk [expect "21" deps.length 21, expect "limit" (errCode r) "CascadeLimitExceeded"]

def depsValidAt : Scenario := fun h => do
  let ((e1, e2, _e3), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertI e1.eid (v "note") (.str "x") (between "2025-01-01" "2025-06-01")
    let e3 ← assertI e1.eid (v "note") (.str "y") (between "2026-01-01" "2026-06-01")
    pure (e1.eid, e2.eid, e3.eid)))
  pure (expect "valid at" (← ok! "q" (← h.query ({ valid := .at (day "2025-03-01") }) (depsQ e1))) [ctr e1, ctr e2])

def pastVisible : Scenario := fun h => do
  let ((e1, e2, e7), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
    let e2 ← assertI e1.eid (v "confidence") (dbl "0.8")
    let e7 ← assertV (v "belief9") (v "supportedBy") (.stmt (ctr e1.eid))
    pure (e1.eid, e2.eid, e7.eid)))
  pad h 18
  let _ ← ok! "20" (← h.tx 20 {} (retractE e1))
  let rows ← ok! "q" (← h.query (asOf 19) triplesQ)
  let hist ← h.tables
  pure <| allOk [expect "as of 19" (rows.toList.map (·.eid)) [e1.raw, e2.raw, e7.raw],
    expect "unchanged" (rows.toList.map fun r => (r.s, r.p, r.o))
      ((hist.triples.filter fun r => [e1.raw, e2.raw, e7.raw].contains r.eid).map fun r => (r.s, r.p, r.o))]

def all : List (String × Scenario) :=
  [("cascade layers", layers), ("cascade nodes", nodesDoNotCascade), ("cascade not walked", notWalked),
   ("cascade diamond", diamond), ("cascade cycle", cycle), ("cascade cardinality", cardinalityKinds),
   ("cascade at limit", atLimit), ("cascade over limit", overLimit), ("cascade per root", perRoot),
   ("dependents back then", backThen), ("dependents ever", everDepended),
   ("dependents larger than limit", depsLargerThanLimit), ("dependents valid at", depsValidAt),
   ("cascade past visible", pastVisible)]

/-- Scenarios at sizes only SQLite runs. -/
def large : List (String × Scenario) := [("cascade default limit", defaultLimit)]

end Test.Store.Cascade
