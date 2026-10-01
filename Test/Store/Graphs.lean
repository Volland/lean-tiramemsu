/-
Scenarios of named-graph-membership and volatile-state.
-/
import Test.Store.Run

namespace Test.Store.Graphs

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Test.Store

def addG (e : ObjectId) (g : Value) (valid : Valid := {}) : TxProg (ObjectId × Bool) := do
  TxProg.verb (.addToGraph e (← enc g) { valid })

def membersQ (g : Value) : ReadProg (List Nat) := do
  match ← ReadProg.query (.lookup g) with
  | some g => return (← ReadProg.query (.graphMembers g)).toList.map ctr
  | none => pure []

def inTwo : Scenario := fun h => do
  let ((e1, m1, m2), r) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let m1 ← addG e1.eid (v "g1")
    let m2 ← addG e1.eid (v "g2")
    pure (e1.eid, m1.1, m2.1)))
  let one ← ok! "q" (← h.query nowV (eidsQ (some (v "a")) (some (v "p")) (some (v "b"))))
  let gs ← ok! "q" (← h.query nowV (do return (← ReadProg.query .graphs).size))
  pure <| allOk [expect "one statement" one [ctr e1], expect "memberships" (eidsOf r.memberships) [ctr m1, ctr m2],
    expect "asserted excludes memberships" (eidsOf r.asserted) [ctr e1], expect "graphs" gs 2]

def literalName : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let before ← h.tables
  let r ← h.tx 2 {} (addG e1.eid (.str "g"))
  pure <| allOk [expect "error" (errCode r) "InvalidGraphName", expect "nothing" ((← h.tables) == before) true]

def idempotentAdd : Scenario := fun h => do
  let ((a, b), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let a ← addG e1.eid (v "g1")
    let b ← addG e1.eid (v "g1")
    pure (a, b)))
  pure <| allOk [expect "same eid" a.1 b.1, expect "new then not" (a.2, b.2) (true, false)]

def removeOne : Scenario := fun h => do
  let ((e1, m1, m2), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let m1 ← addG e1.eid (v "g1")
    let m2 ← addG e1.eid (v "g2")
    pure (e1.eid, m1.1, m2.1)))
  let (removed, r) ← ok! "2" (← h.tx 2 {} (do TxProg.verb (.removeFromGraph e1 (← enc (v "g1")))))
  let (again, _) ← ok! "3" (← h.tx 3 {} (do TxProg.verb (.removeFromGraph e1 (← enc (v "g1")))))
  let live ← ok! "q" (← h.query nowV eidsQ)
  pure <| allOk [expect "removed" (removed, again) (true, false),
    expect "membership retracted" (kindsOf r.membershipsRetracted) [(ctr m1, .explicit)],
    expect "live" live [ctr e1, ctr m2]]

def schemaNotMember : Scenario := fun h => do
  let (f, _) ← ok! "1" (← h.tx 1 {} (flagV "email" "unique" (.bool true)))
  let r ← h.tx 2 {} (addG f.eid (v "g1"))
  let r2 ← h.tx 2 {} (addG (stmt 40) (v "g1"))
  pure <| allOk [expect "error" (errCode r) "ReservedNamespace", expect "unknown" (errCode r2) "NotLive"]

def manage : Scenario := fun h => do
  let ((e1, m, d, s), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let m ← addG e1.eid (v "g1")
    let d ← TxProg.verb (.createGraph (← enc (v "g1")))
    let s ← assertV (v "g1") (v "startedBy") (v "agent7")
    pure (e1.eid, m.1, d.eid, s.eid)))
  let (again, r0) ← ok! "2" (← h.tx 2 {} (do TxProg.verb (.createGraph (← enc (v "g1")))))
  let (out, _) ← ok! "3" (← h.tx 3 {} (do TxProg.verb (.dropGraph (← enc (v "g1")))))
  let live ← ok! "q" (← h.query nowV eidsQ)
  pure <| allOk [expect "existing declaration" again (.existing d), expect "report existing" (eidsOf r0.existing) [ctr d],
    expect "dropped" (eidsOf out) [ctr m, ctr d], expect "others live" live [ctr e1, ctr s]]

def clear : Scenario := fun h => do
  let ((e1, e2, m1, m2), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertV (v "c") (v "p") (v "d")
    let m1 ← addG e1.eid (v "g1")
    let m2 ← addG e2.eid (v "g1")
    pure (e1.eid, e2.eid, m1.1, m2.1)))
  let (out, _) ← ok! "2" (← h.tx 2 {} (do TxProg.verb (.clearGraph (← enc (v "g1")))))
  pure <| allOk [expect "cleared" (eidsOf out) [ctr m1, ctr m2],
    expect "members live" (← ok! "q" (← h.query nowV eidsQ)) [ctr e1, ctr e2]]

def directWrite : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "a") (v "p") (v "b")))
  let before ← h.tables
  let r ← h.tx 2 {} (assertI e1.eid (sysV "inGraph") (v "g1"))
  pure <| allOk [expect "error" (errCode r) "ReservedNamespace", expect "nothing" ((← h.tables) == before) true]

def cascadeMembers : Scenario := fun h => do
  let ((e1, m), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let m ← addG e1.eid (v "g1")
    pure (e1.eid, m.1)))
  let (_, r) ← ok! "2" (← h.tx 2 {} (retractE e1))
  pure <| allOk [expect "statement" (kindsOf r.retracted) [(ctr e1, .explicit)],
    expect "membership" (kindsOf r.membershipsRetracted) [(ctr m, .cascade)]]

def supersedeDrops : Scenario := fun h => do
  let ((e1, m), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let m ← addG e1.eid (v "g1")
    pure (e1.eid, m.1)))
  let (n, r) ← ok! "2" (← h.tx 2 {} (supersedeE e1 { o := some (v "c") }))
  pure <| allOk [expect "membership" (kindsOf r.membershipsRetracted) [(ctr m, .supersede)],
    expect "not copied" (← ok! "q" (← h.query nowV (membersQ (v "g1")))) [],
    expect "new root live" ((← ok! "q" (← h.query nowV eidsQ)).contains (ctr n)) true]

def timeTravel : Scenario := fun h => do
  for _ in [0:4] do let _ ← ok! "pad" (← h.tx 1 {} (pure ()))
  let (e1, _) ← ok! "5" (← h.tx 5 {} (do let e ← assertV (v "a") (v "p") (v "b"); let _ ← addG e.eid (v "g1"); pure e.eid))
  for _ in [0:3] do let _ ← ok! "pad" (← h.tx 6 {} (pure ()))
  let _ ← ok! "9" (← h.tx 9 {} (do TxProg.verb (.removeFromGraph e1 (← enc (v "g1")))))
  pure <| allOk [expect "as of 7" (← ok! "q" (← h.query (asOf 7) (membersQ (v "g1")))) [ctr e1],
    expect "as of 9" (← ok! "q" (← h.query (asOf 9) (membersQ (v "g1")))) []]

def boundedMembership : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (do
    let e ← assertV (v "a") (v "p") (v "b")
    let _ ← addG e.eid (v "g1") (between "2025-01-01" "2025-07-01")
    pure e.eid))
  pure <| allOk [expect "inside" (← ok! "q" (← h.query { valid := .at (day "2025-03-01") } (membersQ (v "g1")))) [ctr e1],
    expect "outside" (← ok! "q" (← h.query { valid := .at (day "2025-08-01") } (membersQ (v "g1")))) []]

/-! ## Volatile state -/

def setVol (s k : Value) (x : Value) : TxProg Unit := do
  TxProg.verb (.setVolatile (← enc s) (← enc k) (← enc x))

def valuesQ (s k : Value) : ReadProg (List ObjectId) := do
  match ← ReadProg.query (.lookup s), ← ReadProg.query (.lookup k) with
  | some s, some k => return (← ReadProg.query (.values s k)).toList
  | _, _ => pure []

def overwrite : Scenario := fun h => do
  for _ in [0:2] do let _ ← ok! "pad" (← h.tx 100 {} (pure ()))
  let _ ← ok! "3" (← h.tx 300 {} (setVol (v "alice") (v "lastSeen") (.int 1)))
  let (_, r) ← ok! "4" (← h.tx 400 {} (setVol (v "alice") (v "lastSeen") (.int 2)))
  let vol := (← h.tables).volatile
  pure <| allOk [expect "one row" vol.length 1, expect "value" (vol.map fun x => (x.value, x.updatedAt)) [((ObjectId.ofSigned .int 2).raw, r.instant)]]

def failedDiscards : Scenario := fun h => do
  let before ← h.tables
  let r ← h.tx 1 {} (do setVol (v "alice") (v "x") (.int 1); TxProg.abort (.custom "no") : TxProg Unit)
  pure <| allOk [expect "error" (errCode r) "Custom", expect "unchanged" ((← h.tables).volatile == before.volatile) true]

def clearTwice : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (setVol (v "alice") (v "score") (.int 1)))
  let a ← h.tx 2 {} (do TxProg.verb (.clearVolatile (← enc (v "alice")) (← enc (v "score"))))
  let b ← h.tx 3 {} (do TxProg.verb (.clearVolatile (← enc (v "alice")) (← enc (v "score"))))
  pure <| allOk [expect "both" (errCode a, errCode b) ("ok", "ok"), expect "gone" (← h.tables).volatile.length 0,
    expect "tx rows" (← h.tables).txs.length 3]

def notStatement : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (pure ()))
  let _ ← ok! "2" (← h.tx 2 {} (setVol (v "alice") (v "lastSeen") (.int 5)))
  let ts ← ok! "q" (← h.query nowV (eidsQ (some (v "alice")) (some (v "lastSeen")) none))
  let evs ← ok! "q" (← h.query nowV (ReadProg.query (.events 1)))
  let bad ← h.tx 3 {} (setVol (v "alice") (.int 3) (.int 5))
  let bad2 ← h.tx 3 {} (setVol (.int 1) (v "k") (.int 5))
  pure <| allOk [expect "no triple" ts [], expect "no event" evs.size 0, expect "tx rows" (← h.tables).txs.length 2,
    expect "key" (errCode bad) "InvalidTerm", expect "subject" (errCode bad2) "InvalidTerm"]

def resolveNowOnly : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do
    setVol (v "alice") (v "lastSeen") (.int 5)
    setVol (v "alice") (v "status") (.str "busy")
    let _ ← assertV (v "alice") (v "status") (.str "away")))
  let now ← ok! "q" (← h.query nowV (valuesQ (v "alice") (v "lastSeen")))
  let asof ← ok! "q" (← h.query (asOf 1) (valuesQ (v "alice") (v "lastSeen")))
  let hst ← ok! "q" (← h.query hist (valuesQ (v "alice") (v "lastSeen")))
  let st ← ok! "q" (← h.query nowV (valuesQ (v "alice") (v "status")))
  pure <| allOk [expect "now" now [ObjectId.ofSigned .int 5], expect "as of" asof [], expect "history" hst [],
    expect "statement wins" (st.map (·.raw)) [(ObjectId.ofPayload .shortStr (Codec.packShort "away")).raw]]

def specSeesOwn : Scenario := fun h => do
  let r ← h.spec 1 (setVol (v "alice") (v "mood") (.int 7)) none (valuesQ (v "alice") (v "mood"))
  pure <| allOk [expect "seen" r.toOption (some [ObjectId.ofSigned .int 7]), expect "gone" (← h.tables).volatile.length 0]

def all : List (String × Scenario) :=
  [("graphs two graphs", inTwo), ("graphs literal name", literalName), ("graphs idempotent add", idempotentAdd),
   ("graphs remove one", removeOne), ("graphs schema statements", schemaNotMember), ("graphs manage", manage),
   ("graphs clear", clear), ("graphs direct write", directWrite), ("graphs cascade", cascadeMembers),
   ("graphs supersede", supersedeDrops), ("graphs time travel", timeTravel), ("graphs valid at", boundedMembership),
   ("volatile overwrite", overwrite), ("volatile failed", failedDiscards), ("volatile clear twice", clearTwice),
   ("volatile not statement", notStatement), ("volatile now only", resolveNowOnly),
   ("volatile speculation", specSeesOwn)]

end Test.Store.Graphs
