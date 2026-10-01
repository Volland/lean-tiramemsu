/-
Scenarios of the transaction-log capability.
-/
import Test.Store.Run

namespace Test.Store.TxLog

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Test.Store

def tSeq (h : Harness) : IO (List (Int × Int)) := do
  return (← h.tables).txs.map fun r => (r.t.toInt, r.instant.toInt)

/-- Numbers across failures, dry runs and speculation. -/
def numbering : Scenario := fun h => do
  for i in [0:3] do
    let _ ← ok! "commit" (← h.tx (1000 + i) {} (assertV (v "a") (v "p") (.int i)))
  let f ← h.tx 2000 {} (do let _ ← assertV (v "a") (v "p") (.int 9); TxProg.abort (.custom "stop") : TxProg Unit)
  let d ← h.dry 2001 {} (assertV (v "a") (v "p") (.int 10))
  let s ← h.spec 2002 (assertV (v "a") (v "p") (.int 11)) none (pure ())
  let r ← ok! "commit" (← h.tx 2003 {} (assertV (v "a") (v "p") (.int 12)))
  pure <| allOk [
    expect "failed" (errCode f) "Custom",
    expect "dry run t" ((d.toOption.map (·.2.t))) (some 4),
    expect "speculation ok" (s.isOk) true,
    expect "last t" r.2.t 4,
    expect "tx table" ((← tSeq h).map (·.1)) [1, 2, 3, 4]]

/-- Backwards and standing clocks. -/
def clocks : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 10000 {} (pure ()))
  let _ ← ok! "2" (← h.tx 5000 {} (pure ()))
  let _ ← ok! "3" (← h.tx 7000 {} (pure ()))
  let _ ← ok! "4" (← h.tx 7000 {} (pure ()))
  pure (expect "instants" ((← tSeq h).map (·.2)) [10000, 10001, 10002, 10003])

/-- Empty and all-no-op transactions are recorded. -/
def emptyAndNoOp : Scenario := fun h => do
  let r1 ← ok! "empty" (← h.tx 1 {} (pure ()))
  let (a, _) ← ok! "assert" (← h.tx 2 {} (assertV (v "a") (v "p") (v "b")))
  let (b, r3) ← ok! "again" (← h.tx 3 {} (assertV (v "a") (v "p") (v "b")))
  pure <| allOk [
    expect "empty report" (r1.2.asserted.size, r1.2.t) (0, 1),
    expect "existing" b (.existing a.eid),
    expect "no-op report" (eidsOf r3.asserted, eidsOf r3.existing) ([], [ctr a.eid]),
    expect "tx rows" ((← tSeq h).length) 3]

/-- Metadata about the transaction; reserved metadata on a non-transaction. -/
def metadata : Scenario := fun h => do
  for _ in [0:4] do let _ ← ok! "pad" (← h.tx 1 {} (pure ()))
  let ((e1, e2), r) ← ok! "meta" (← h.tx 2 {} (do
    let a ← TxProg.verb (.metadata (← enc (.iri (Vocab.sys ++ "author"))) (← enc (v "agent7")))
    let b ← TxProg.verb (.metadata (← enc (.iri (Vocab.sys ++ "reason"))) (← enc (.str "user correction")))
    pure (a, b)))
  let rows ← ok! "rows" (← h.query {} (triplesQ (some (.tx 5)) none none))
  let bad ← h.tx 3 {} (assertV (v "alice") (.iri (Vocab.sys ++ "reason")) (.str "x"))
  pure <| allOk [
    expect "t" r.t 5,
    expect "two statements" (rows.toList.map (·.eid)) [e1.raw, e2.raw],
    expect "t_add" (rows.toList.map (·.tAdd)) [5, 5],
    expect "reserved" (errCode bad) "ReservedNamespace"]

/-- The mixed report of the spec. -/
def mixedReport : Scenario := fun h => do
  let ((b, c, d), _) ← ok! "setup" (← h.tx 1 {} (do
    let b ← assertV (v "b") (v "p") (v "x")
    let c ← assertV (v "c") (v "p") (v "y")
    let d ← assertI c.eid (v "note") (.str "annotation")
    pure (b.eid, c.eid, d.eid)))
  let (a, r) ← ok! "mixed" (← h.tx 2 {} (do
    let a ← assertV (v "a") (v "p") (v "z")
    let _ ← assertV (v "b") (v "p") (v "x")
    let _ ← retractE c
    pure a.eid))
  pure <| allOk [
    expect "asserted" (eidsOf r.asserted) [ctr a],
    expect "existing" (eidsOf r.existing) [ctr b],
    expect "retracted" (kindsOf r.retracted) [(ctr c, .explicit), (ctr d, .cascade)]]

/-- The same new statement twice in one transaction. -/
def repeatedAssert : Scenario := fun h => do
  let ((a, b), r) ← ok! "twice" (← h.tx 1 {} (do
    let a ← assertV (v "a") (v "p") (v "b")
    let b ← assertV (v "a") (v "p") (v "b")
    pure (a, b)))
  pure <| allOk [
    expect "second existing" b (.existing a.eid),
    expect "asserted once" (eidsOf r.asserted) [ctr a.eid],
    expect "not existing" (eidsOf r.existing) []]

/-- Atomic failure leaves every table as it was. -/
def atomicFailure : Scenario := fun h => do
  let (e, _) ← ok! "setup" (← h.tx 1 {} (do
    let _ ← TxProg.verb (.assert (← enc (v "email")) (← enc (.iri Vocab.sysUnique)) (← enc (.bool true)) {})
    let _ ← assertV (v "alice") (v "email") (.str "a@x.org")
    assertV (v "x") (v "p") (v "y")))
  let before ← h.tables
  let r ← h.tx 2 {} (do
    let _ ← assertV (v "q") (v "p") (.str "a long string that needs the dictionary")
    let _ ← retractE e.eid
    let _ ← TxProg.verb (.setVolatile (← enc (v "alice")) (← enc (v "seen")) (← enc (.int 1)))
    assertV (v "bob") (v "email") (.str "a@x.org"))
  let after ← h.tables
  pure <| allOk [expect "error" (errCode r) "UniqueViolation", expect "tables" (after == before) true]

/-- The body's own error. -/
def bodyAbort : Scenario := fun h => do
  let before ← h.tables
  let r ← h.tx 1 {} (do let _ ← assertV (v "a") (v "p") (v "b"); TxProg.abort (.custom "mine") : TxProg Unit)
  pure <| allOk [expect "error" (errCode r) "Custom", expect "tables" ((← h.tables) == before) true]

def all : List (String × Scenario) :=
  [("txlog numbering", numbering), ("txlog clocks", clocks), ("txlog empty and no-op", emptyAndNoOp),
   ("txlog metadata", metadata), ("txlog mixed report", mixedReport),
   ("txlog repeated assert", repeatedAssert), ("txlog atomic failure", atomicFailure),
   ("txlog body abort", bodyAbort)]

end Test.Store.TxLog
