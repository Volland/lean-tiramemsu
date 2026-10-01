/-
Scenarios of memory-verbs and statement-lifecycle.
-/
import Test.Store.Run

namespace Test.Store.Verbs

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Test.Store

def allEids (h : Harness) (view : View.ViewSpec) : IO (List Nat) := do
  ok! "query" (← h.query view (eidsQ))

/-! ## Write pipeline and reserved namespaces -/

def literalSubject : Scenario := fun h => do
  let before ← h.tables
  let r ← h.tx 1 {} (assertV (.int 5) (v "p") (v "o"))
  pure <| allOk [expect "error" (errCode r) "InvalidTerm", expect "no trace" ((← h.tables) == before) true]

def emptyInterval : Scenario := fun h => do
  let r ← h.tx 1 {} (assertV (v "a") (v "p") (v "o") (between "2025-01-01" "2025-01-01"))
  pure (expect "error" (errCode r) "InvalidInterval")

def forgedConfirmation : Scenario := fun h => do
  let (e, _) ← ok! "setup" (← h.tx 1 {} (assertV (v "a") (v "p") (v "o")))
  let r ← h.tx 2 {} (assertI e.eid (sysV "confirmedBy") (.tx 1))
  let r2 ← h.tx 3 {} (assertI e.eid (sysV "supersedes") (.stmt 1))
  let r3 ← h.tx 4 {} (assertI e.eid (.iri (Vocab.tm ++ "x")) (.int 1))
  let r4 ← h.tx 5 {} (assertV (v "a") (sysV "sensitive") (.bool true))
  pure <| allOk [expect "confirmedBy" (errCode r) "ReservedNamespace",
    expect "supersedes" (errCode r2) "ReservedNamespace", expect "tm" (errCode r3) "ReservedNamespace",
    expect "sensitive" (errCode r4) "Unsupported"]

def allowedFlag : Scenario := fun h => do
  let r ← h.tx 1 {} (flagV "email" "unique" (.bool true))
  let r2 ← h.tx 2 {} (assertV (sysV "db") (sysV "vocab") (.iri "urn:x:"))
  pure <| allOk [expect "flag" (r.toOption.map (·.1.isNew)) (some true),
    expect "vocab" (r2.toOption.map (·.1.isNew)) (some true)]

/-! ## Assert -/

def sameFactTwice : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  let (b, r) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  pure <| allOk [expect "existing" b (.existing a.eid), expect "nothing inserted" r.asserted.size 0,
    expect "rows" (← h.tables).triples.length 1]

def touchingIntervals : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2022-01-01")))
  let (b, _) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "worksAt") (v "acme") (between "2022-01-01" "2024-01-01")))
  pure <| allOk [expect "new" b.isNew true, expect "both live" (← allEids h nowV) [ctr a.eid, ctr b.eid]]

def overlappingDifferent : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2022-01-01")))
  let (b, _) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "worksAt") (v "acme") (between "2021-01-01" "2024-01-01")))
  let row ← rowOf h a.eid
  pure <| allOk [expect "existing" b (.existing a.eid),
    expect "interval unchanged" (row.map fun r => (r.vFrom, r.vTo)) (some (some (day "2020-01-01"), some (day "2022-01-01")))]

def retractedMatchIgnored : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  let _ ← ok! "2" (← h.tx 2 {} (retractE a.eid))
  let (b, _) ← ok! "3" (← h.tx 3 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  pure <| allOk [expect "new" b.isNew true, expect "fresh greater" (decide (ctr b.eid > ctr a.eid)) true,
    expect "old stays retracted" ((← rowOf h a.eid).bind (·.tRet)) (some 2)]

def confirmingReassert : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  for _ in [0:7] do let _ ← ok! "pad" (← h.tx 2 {} (pure ()))
  let (b, r) ← ok! "9" (← h.tx 3 {} (assertV (v "alice") (v "worksAt") (v "acme") {} .confirm))
  let conf ← ok! "q" (← h.query nowV (triplesQ (some (.stmt (ctr a.eid))) (some (sysV "confirmedBy")) (some (.tx 9))))
  pure <| allOk [expect "t" r.t 9, expect "existing" b (.existing a.eid), expect "confirmation" conf.size 1]

def createParallel : Scenario := fun h => do
  let ((a, b), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← createV (v "a") (v "called") (v "b")
    let b ← createV (v "a") (v "called") (v "b")
    pure (a, b)))
  let t ← h.tables
  pure <| allOk [expect "different" (a != b) true, expect "both live" (← allEids h nowV) [ctr a, ctr b],
    expect "pred_multi" t.predMulti.length 1,
    expect "multi_version" ((t.counters.find? (·.1 == "multi_version")).map (·.2)) (some 1)]

def retractTwice : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  let ((x, y), _) ← ok! "2" (← h.tx 2 {} (do let x ← retractE a.eid; let y ← retractE a.eid; pure (x, y)))
  let (z, _) ← ok! "3" (← h.tx 3 {} (retractE (stmt 99)))
  pure (expect "results" (x, y, z) (true, false, false))

def retractMatchingCascade : Scenario := fun h => do
  let ((e1, e2), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "alice") (v "note") (.str "y")
    let e2 ← assertI e1.eid (v "note") (.str "x")
    pure (e1.eid, e2.eid)))
  let (got, r) ← ok! "2" (← h.tx 2 {} (do TxProg.verb (.retractMatching none (some (← enc (v "note"))) none)))
  pure <| allOk [expect "matched" (eidsOf got) [ctr e1, ctr e2],
    expect "kinds" (kindsOf r.retracted) [(ctr e1, .explicit), (ctr e2, .cascade)]]

def confirmTwice : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  for _ in [0:3] do let _ ← ok! "pad" (← h.tx 2 {} (pure ()))
  let _ ← ok! "5" (← h.tx 5 {} (TxProg.verb (.confirm a.eid)))
  for _ in [0:2] do let _ ← ok! "pad" (← h.tx 6 {} (pure ()))
  let _ ← ok! "8" (← h.tx 8 {} (TxProg.verb (.confirm a.eid)))
  let c5 ← ok! "q" (← h.query nowV (eidsQ (some (.stmt (ctr a.eid))) (some (sysV "confirmedBy")) none))
  let row ← rowOf h a.eid
  let bad ← h.tx 9 {} (TxProg.verb (.confirm (stmt 77)))
  pure <| allOk [expect "two confirmations" c5.length 2, expect "unchanged" (row.bind (·.tRet)) none,
    expect "not live" (errCode bad) "NotLive"]

def freshNodes : Scenario := fun h => do
  let ((a, b, c), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← TxProg.verb .newNode
    let b ← TxProg.verb .newNode
    let c ← TxProg.verb .newBNode
    pure (a, b, c)))
  pure <| allOk [expect "different" (a != b) true, expect "tags" (a.tag.toOption, c.tag.toOption) (some .node, some .bnode),
    expect "no statement" (← h.tables).triples.length 0]

/-! ## Statement lifecycle -/

def contentSurvives : Scenario := fun h => do
  for _ in [0:2] do let _ ← ok! "pad" (← h.tx 1 {} (pure ()))
  let (a, _) ← ok! "3" (← h.tx 3 {} (assertV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2022-01-01")))
  for _ in [0:3] do let _ ← ok! "pad" (← h.tx 4 {} (pure ()))
  let _ ← ok! "7" (← h.tx 7 {} (retractE a.eid))
  let rows ← ok! "history" (← h.query hist triplesQ)
  pure <| match rows.toList with
    | [r] => allOk [expect "content" (r.eid, r.tAdd, r.vFrom, r.vTo) (a.eid.raw, 3, some (day "2020-01-01"), some (day "2022-01-01")),
                    expect "retraction" (r.tRet, r.retKind) (some 7, some 0)]
    | _ => some "one row expected"

def secondRetraction : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  for _ in [0:2] do let _ ← ok! "pad" (← h.tx 2 {} (pure ()))
  let _ ← ok! "4" (← h.tx 4 {} (retractE a.eid))
  let (x, _) ← ok! "5" (← h.tx 5 {} (retractE a.eid))
  let row ← rowOf h a.eid
  pure <| allOk [expect "false" x false, expect "kept" (row.map fun r => (r.tRet, r.retKind)) (some (some 4, some 0))]

def assertedAndRetracted : Scenario := fun h => do
  for _ in [0:6] do let _ ← ok! "pad" (← h.tx 1 {} (pure ()))
  let (a, _) ← ok! "7" (← h.tx 7 {} (do let a ← assertV (v "a") (v "p") (v "b"); let _ ← retractE a.eid; pure a))
  let mut asOfs := []
  for t in [0:9] do asOfs := asOfs ++ [(← allEids h (asOf t.toInt64))]
  let row ← rowOf h a.eid
  pure <| allOk [expect "times" (row.map fun r => (r.tAdd, r.tRet)) (some (7, some 7)),
    expect "now" (← allEids h nowV) [], expect "as-of" (asOfs.all (·.isEmpty)) true,
    expect "history" (← allEids h hist) [ctr a.eid]]

def failedMayReissue : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let f ← h.tx 2 {} (do let x ← assertV (v "a") (v "p") (v "c"); let _ ← (TxProg.abort (.custom "no") : TxProg Unit); pure x)
  let (b, _) ← ok! "3" (← h.tx 3 {} (assertV (v "a") (v "p") (v "d")))
  pure <| allOk [expect "failed" (errCode f) "Custom", expect "reissued" (ctr b.eid) (ctr a.eid + 1)]

def guessedOwnEid : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let r ← h.tx 2 {} (assertV (v "a") (v "p") (.stmt (ctr a.eid + 1)))
  pure <| match r with
    | .error (.selfReference e) => expect "eid" (ctr e) (ctr a.eid + 1)
    | other => some s!"expected SelfReference, got {errCode other}"

def annotateRetracted : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let _ ← ok! "2" (← h.tx 2 {} (retractE a.eid))
  let (n, _) ← ok! "3" (← h.tx 3 {} (assertI a.eid (v "note") (.str "was wrong")))
  let (f, _) ← ok! "4" (← h.tx 4 {} (assertV (v "x") (v "refersTo") (.stmt 1000)))
  pure <| allOk [expect "inserted" n.isNew true, expect "future eid accepted" f.isNew true,
    expect "live" ((← allEids h nowV).contains (ctr n.eid)) true]

def all : List (String × Scenario) :=
  [("verbs literal subject", literalSubject), ("verbs empty interval", emptyInterval),
   ("verbs reserved", forgedConfirmation), ("verbs allowed flag", allowedFlag),
   ("verbs same fact twice", sameFactTwice), ("verbs touching intervals", touchingIntervals),
   ("verbs overlapping different", overlappingDifferent), ("verbs retracted match", retractedMatchIgnored),
   ("verbs confirming reassert", confirmingReassert), ("verbs create parallel", createParallel),
   ("verbs retract twice", retractTwice), ("verbs retract matching", retractMatchingCascade),
   ("verbs confirm twice", confirmTwice), ("verbs fresh nodes", freshNodes),
   ("lifecycle content", contentSurvives), ("lifecycle second retraction", secondRetraction),
   ("lifecycle same transaction", assertedAndRetracted), ("lifecycle failed reissue", failedMayReissue),
   ("lifecycle self reference", guessedOwnEid), ("lifecycle annotate retracted", annotateRetracted)]

end Test.Store.Verbs
