/-
Scenarios of temporal-views and speculative-transactions.
-/
import Test.Store.Run

namespace Test.Store.Views

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Test.Store

def pad (h : Harness) (n : Nat) : IO Unit := do
  for _ in [0:n] do let _ ← ok! "pad" (← h.tx 1 {} (pure ()))

def eidsIn (h : Harness) (view : View.ViewSpec) : IO (List Nat) := do ok! "q" (← h.query view eidsQ)

def validOptIn : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2022-01-01")))
  pure (expect "now" (← eidsIn h nowV) [ctr a.eid])

def validAtWithAsOf : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme") (fromD "2020-01-01")))
  pad h 7
  let _ ← ok! "9" (← h.tx 9 {} (supersedeE e1.eid { vTo := some (some (day "2026-03-01")) }))
  pure <| allOk [expect "as of 8" (← eidsIn h ((asOf 8).validAt (day "2026-06-01"))) [ctr e1.eid],
    expect "now" (← ok! "q" (← h.query (nowV.validAt (day "2026-06-01")) (eidsQ (some (v "alice")) (some (v "worksAt")) none))) []]

def beforeRetraction : Scenario := fun h => do
  pad h 2
  let (e1, _) ← ok! "3" (← h.tx 3 {} (assertV (v "a") (v "p") (v "b")))
  pad h 2
  let _ ← ok! "6" (← h.tx 6 {} (retractE e1.eid))
  let mut seen := []
  for t in [2, 3, 4, 5, 6] do
    let rows ← ok! "q" (← h.query (asOf t) triplesQ)
    seen := seen ++ [(t, rows.toList.map fun r => (ctr ⟨r.eid⟩, r.tRet))]
  pure (expect "as-of" seen [(2, []), (3, [(ctr e1.eid, none)]), (4, [(ctr e1.eid, none)]), (5, [(ctr e1.eid, none)]), (6, [])])

def historyBoth : Scenario := fun h => do
  let ((e1, e2), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← assertV (v "a") (v "p") (v "b"); let b ← assertV (v "c") (v "p") (v "d"); pure (a.eid, b.eid)))
  pad h 4
  let _ ← ok! "6" (← h.tx 6 {} (retractE e1))
  let rows ← ok! "q" (← h.query hist triplesQ)
  pure (expect "history" (rows.toList.map fun r => (ctr ⟨r.eid⟩, r.tRet, r.retKind)) [(ctr e1, some 6, some 0), (ctr e2, none, none)])

def asOfBounds : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  pure <| allOk [expect "as of 0" (← eidsIn h (asOf 0)) [], expect "as of 99" (← eidsIn h (asOf 99)) [ctr a.eid]]

def instants : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1000 {} (assertV (v "a") (v "p") (.int 1)))
  let _ ← ok! "2" (← h.tx 2000 {} (assertV (v "a") (v "p") (.int 2)))
  let at_ (ms : Int64) : View.ViewSpec := { tx := .asOf (.instant ms) }
  pure <| allOk [expect "1500" (← eidsIn h (at_ 1500)) [1], expect "2000" (← eidsIn h (at_ 2000)) [1, 2],
    expect "999" (← eidsIn h (at_ 999)) []]

def backwardsInstants : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 10000 {} (assertV (v "a") (v "p") (.int 1)))
  let _ ← ok! "2" (← h.tx 5000 {} (assertV (v "a") (v "p") (.int 2)))
  let _ ← ok! "3" (← h.tx 5000 {} (assertV (v "a") (v "p") (.int 3)))
  let mut out := []
  for ms in [10000, 10001, 10002] do
    out := out ++ [(← ok! "q" (← h.query { tx := .asOf (.instant ms) } (ReadProg.query .basis)), ← eidsIn h { tx := .asOf (.instant ms) })]
  pure (expect "resolved" (out.map (·.2.length)) [1, 2, 3])

def validBoundaries : Scenario := fun h => do
  let ((a, b), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← assertV (v "a") (v "p") (v "b") (between "2025-01-01" "2026-03-01")
    let b ← assertV (v "c") (v "p") (v "d")
    pure (a.eid, b.eid)))
  let at_ (d : Int64) := eidsIn h (nowV.validAt d)
  pure <| allOk [expect "start" (← at_ (day "2025-01-01")) [ctr a, ctr b],
    expect "last ms" (← at_ (day "2026-03-01" - 1)) [ctr a, ctr b],
    expect "before" (← at_ (day "2024-12-31")) [ctr b], expect "end" (← at_ (day "2026-03-01")) [ctr b]]

def lookup : Scenario := fun h => do
  let ((a, b), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← assertV (v "alice") (v "likes") (v "tea")
    let b ← assertV (v "alice") (v "likes") (v "coffee")
    let _ ← assertV (v "bob") (v "likes") (v "tea")
    pure (a.eid, b.eid)))
  let mut combos := []
  for s in [none, some (v "alice")] do
    for p in [none, some (v "likes")] do
      for o in [none, some (v "tea")] do
        combos := combos ++ [(← ok! "q" (← h.query nowV (eidsQ s p o)))]
  pure <| allOk [expect "alice likes" (← ok! "q" (← h.query nowV (eidsQ (some (v "alice")) (some (v "likes")) none))) [ctr a, ctr b],
    expect "all combinations" combos [[1, 2, 3], [1, 3], [1, 2, 3], [1, 3], [1, 2], [1], [1, 2], [1]]]

def unknownConstant : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let before ← h.tables
  let rows ← ok! "q" (← h.query nowV (triplesQ none none (some (.str "twenty bytes string!"))))
  pure <| allOk [expect "empty" rows.size 0, expect "terms unchanged" ((← h.tables).terms == before.terms) true]

def eventLog : Scenario := fun h => do
  pad h 3
  let ((e1, e2), _) ← ok! "4" (← h.tx 4 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertI e1.eid (v "note") (.str "x")
    pure (e1.eid, e2.eid)))
  let _ ← ok! "5" (← h.tx 5 {} (retractE e1))
  let evs ← ok! "q" (← h.query nowV (ReadProg.query (.events 3)))
  pure (expect "events" (evs.toList.map fun e => (e.t, ctr e.eid, e.op, e.kind))
    [(4, ctr e1, .assert, none), (4, ctr e2, .assert, none), (5, ctr e1, .retract, some .explicit),
     (5, ctr e2, .retract, some .cascade)])

/-! ## Speculation and dry runs -/

def specVisible : Scenario := fun h => do
  let r ← h.spec 1 (assertV (v "alice") (v "worksAt") (v "globex")) none
    (do return (← triplesQ (some (v "alice")) (some (v "worksAt")) none).size)
  pure <| allOk [expect "seen" r.toOption (some 1), expect "nothing kept" (← h.tables).triples.length 0]

def specRetraction : Scenario := fun h => do
  let ((e1, _), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b"); let e2 ← assertI e1.eid (v "note") (.str "x"); pure (e1.eid, e2.eid)))
  let r ← h.spec 2 (retractE e1) none eidsQ
  pure <| allOk [expect "inside" r.toOption (some []), expect "after" (← eidsIn h nowV) [1, 2]]

def specFails : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do let _ ← flagV "email" "unique" (.bool true); assertV (v "alice") (v "email") (.str "a@x.org")))
  let r ← h.spec 2 (assertV (v "bob") (v "email") (.str "a@x.org")) none (ReadProg.fail (.custom "query ran") : ReadProg Unit)
  pure (expect "error" (errCode r) "UniqueViolation")

def specTablesUnchanged : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let before ← h.tables
  let r ← h.spec 2 (do
    let _ ← assertV (v "x") (v "p") (.str "a long string for the dictionary")
    let _ ← supersedeE e1.eid { o := some (v "c") }
    TxProg.verb (.setVolatile (← enc (v "x")) (← enc (v "k")) (← enc (.int 1)))) none (pure ())
  let after ← h.tables
  let same := after.triples == before.triples && after.terms == before.terms && after.txs == before.txs &&
    after.volatile == before.volatile && after.predMulti == before.predMulti
  let (_, r5) ← ok! "next" (← h.tx 3 {} (pure ()))
  pure <| allOk [expect "ok" (errCode r) "ok", expect "unchanged" same true, expect "number" r5.t 2]

def burnedIds : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let shown ← h.spec 2 (do
    let mut last := stmt 0
    for i in [0:20] do last ← createV (v "a") (v "q") (.int i)
    let iri ← enc (.iri "urn:x:speculative-iri")
    pure (last, iri)) none (pure ())
  let r ← h.spec 2 (do
    let mut last := stmt 0
    for i in [0:3] do last ← createV (v "a") (v "q") (.int i)
    pure last) none (pure ())
  let (e, _) ← ok! "2" (← h.tx 3 {} (assertV (v "a") (v "q") (v "c")))
  let (iri, _) ← ok! "3" (← h.tx 4 {} (enc (.iri "urn:x:speculative-iri")))
  pure <| allOk [expect "spec ok" (errCode shown, errCode r) ("ok", "ok"),
    expect "eid above burned" (decide (ctr e.eid > 21 + 3)) true, expect "term above burned" (decide (iri.upayload.toNat > 3)) true]

def burnedOnFailure : Scenario := fun h => do
  let _ ← h.spec 1 (do
    for i in [0:5] do let _ ← createV (v "a") (v "q") (.int i)
    TxProg.abort (.custom "no") : TxProg Unit) none (pure ())
  let (e, _) ← ok! "1" (← h.tx 2 {} (assertV (v "a") (v "q") (v "c")))
  pure (expect "eid" (ctr e.eid) 6)

def dryRunPreview : Scenario := fun h => do
  let (c, _) ← ok! "1" (← h.tx 1 {} (do let c ← assertV (v "c") (v "p") (v "d"); let _ ← assertI c.eid (v "note") (.str "x"); pure c.eid))
  let before ← h.tables
  let (_, r) ← ok! "dry" (← h.dry 2 {} (do
    let _ ← assertV (v "a") (v "p") (v "b"); let _ ← assertV (v "a") (v "p") (v "z"); retractE c))
  let after ← h.tables
  let (_, r2) ← ok! "commit" (← h.tx 3 {} (pure ()))
  pure <| allOk [expect "asserted" r.asserted.size 2, expect "retracted" (kindsOf r.retracted) [(ctr c, .explicit), (2, .cascade)],
    expect "tables" (after.triples == before.triples && after.txs == before.txs) true,
    expect "next t" (r.t, r2.t) (2, 2)]

def dryEqualsCommit : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do let c ← assertV (v "c") (v "p") (v "d"); let _ ← assertI c.eid (v "note") (.str "x")))
  let body : TxProg Unit := do
    let _ ← assertV (v "a") (v "p") (v "b")
    let _ ← assertV (v "c") (v "p") (v "d")
    let _ ← supersedeE (stmt 1) { o := some (v "e") }
  let d ← h.dry 7 {} body
  let c ← h.tx 7 {} body
  -- the dry run burned the four eids it showed, so the commit's new eids are four higher
  let sh (e : ObjectId) : ObjectId := if ctr e ≥ 3 then stmt (ctr e + 4) else e
  let shift (r : TxReport) : TxReport :=
    { r with asserted := r.asserted.map sh, existing := r.existing.map sh,
             retracted := r.retracted.map fun (e, k) => (sh e, k),
             superseded := r.superseded.map fun (a, b) => (sh a, sh b) }
  pure <| allOk [expect "ok" (errCode d) "ok", expect "same report" (d.toOption.map (shift ·.2)) (c.toOption.map (·.2))]

def all : List (String × Scenario) :=
  [("views valid opt-in", validOptIn), ("views valid-at with as-of", validAtWithAsOf),
   ("views before retraction", beforeRetraction), ("views history", historyBoth), ("views as-of bounds", asOfBounds),
   ("views instants", instants), ("views backwards instants", backwardsInstants),
   ("views valid boundaries", validBoundaries), ("views lookup", lookup), ("views unknown constant", unknownConstant),
   ("views event log", eventLog),
   ("speculation visible", specVisible), ("speculation retraction", specRetraction),
   ("speculation fails", specFails), ("speculation tables", specTablesUnchanged),
   ("speculation burned", burnedIds), ("speculation burned on failure", burnedOnFailure),
   ("dry run preview", dryRunPreview), ("dry run equals commit", dryEqualsCommit)]

end Test.Store.Views
