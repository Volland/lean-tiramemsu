/-
Scenarios of supersede and patch rules (memory-verbs).
-/
import Test.Store.Run

namespace Test.Store.Supersede

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Test.Store

def tRetKind (h : Harness) (e : ObjectId) : IO (Option (Int64 × Int64)) := do
  return (← rowOf h e).bind fun r => match r.tRet, r.retKind with
    | some t, some k => some (t, k)
    | _, _ => none

def rewires : Scenario := fun h => do
  let ((e1, e2, e7), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
    let e2 ← assertI e1.eid (v "confidence") (dbl "0.8")
    let e7 ← assertV (v "belief9") (v "supportedBy") (.stmt (ctr e1.eid))
    pure (e1.eid, e2.eid, e7.eid)))
  let (n, r) ← ok! "2" (← h.tx 2 {} (supersedeE e1 { vFrom := some (some (day "2025-02-01")) }))
  let rows ← ok! "q" (← h.query nowV triplesQ)
  let newRoot := rows.toList.find? (·.eid == n.raw)
  let sp ← ok! "q" (← h.query nowV (do
    let p ← ReadProg.query (.lookup (sysV "supersedes"))
    let ps := p.map some
    match ps with
    | some p => ReadProg.query (.triples (some n) p (some e1))
    | none => pure #[]))
  let conf ← ok! "q" (← h.query nowV (triplesQ none (some (v "confidence")) none))
  let belief ← ok! "q" (← h.query nowV (triplesQ (some (v "belief9")) none none))
  pure <| allOk [
    expect "root" (newRoot.map fun r => (r.vFrom, r.vTo)) (some (some (day "2025-02-01"), none)),
    expect "annotation rewired" (conf.toList.map (·.s)) [n.raw],
    expect "reference rewired" (belief.toList.map (·.o)) [n.raw],
    expect "link" sp.size 1,
    expect "old retracted" (← [e1, e2, e7].mapM (tRetKind h)) [some (2, 2), some (2, 2), some (2, 2)],
    expect "superseded pairs" (r.superseded.toList.map (·.1)) [e1, e2, e7]]

def cyclesRewired : Scenario := fun h => do
  let ((e1, _e2, _e3), _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let e2 ← assertI e1.eid (v "x") (.stmt (ctr e1.eid + 2))
    let e3 ← TxProg.verb (.assert e2.eid (← enc (v "y")) e1.eid {})
    pure (e1.eid, e2.eid, e3.eid)))
  let (_, r) ← ok! "2" (← h.tx 2 {} (supersedeE e1 { o := some (v "c") }))
  let olds := r.superseded.toList.map (·.1.raw)
  let news := r.superseded.toList.map (·.2.raw)
  let rows ← ok! "q" (← h.query nowV triplesQ)
  let replays := rows.toList.filter fun x => news.contains x.eid
  pure <| allOk [expect "three replays" replays.length 3,
    expect "no old reference" (replays.all fun x => !olds.contains x.s && !olds.contains x.o) true]

def chain : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "city") (.str "Kyiv")))
  let (e10, _) ← ok! "2" (← h.tx 2 {} (supersedeE e1.eid { o := some (.str "Lviv") }))
  let (e20, _) ← ok! "3" (← h.tx 3 {} (supersedeE e10 { o := some (.str "Odesa") }))
  let links ← ok! "q" (← h.query nowV (triplesQ none (some (sysV "supersedes")) none))
  let hist ← ok! "q" (← h.query hist (triplesQ none (some (sysV "supersedes")) none))
  pure <| allOk [
    expect "live links" (links.toList.map fun r => (r.s, r.o)) [(e20.raw, e1.eid.raw), (e20.raw, e10.raw)],
    expect "old link retracted" ((hist.toList.filter (·.s == e10.raw)).map (·.retKind)) [some 2]]

def closeOpen : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme") (fromD "2020-01-01")))
  let (n, _) ← ok! "2" (← h.tx 2 {} (supersedeE e1.eid { vTo := some (some (day "2026-03-01")) }))
  let (m, _) ← ok! "3" (← h.tx 3 {} (supersedeE n { vFrom := some none }))
  let row ← rowOf h n
  let row2 ← rowOf h m
  pure <| allOk [expect "closed" (row.map fun r => (r.vFrom, r.vTo)) (some (some (day "2020-01-01"), some (day "2026-03-01"))),
    expect "cleared" (row2.map fun r => (r.vFrom, r.vTo)) (some (none, some (day "2026-03-01")))]

def noChange : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  let before ← h.tables
  let a ← h.tx 2 {} (supersedeE e1.eid {})
  let b ← h.tx 2 {} (supersedeE e1.eid { o := some (v "acme") })
  let c ← h.tx 2 {} (supersedeE e1.eid { vFrom := some (some 10), vTo := some (some 10) })
  pure <| allOk [expect "empty" (errCode a) "InvalidPatch", expect "same object" (errCode b) "InvalidPatch",
    expect "empty interval" (errCode c) "InvalidPatch", expect "no trace" ((← h.tables) == before) true]

def twice : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (assertV (v "alice") (v "worksAt") (v "acme")))
  let r ← h.tx 2 {} (do let _ ← supersedeE e1.eid { o := some (v "globex") }; supersedeE e1.eid { o := some (v "initech") })
  let r2 ← h.tx 2 {} (supersedeE (stmt 50) { o := some (v "x") })
  pure <| allOk [
    (match r with
     | .error (.notLive e) => expect "eid" e e1.eid
     | other => some s!"expected NotLive, got {errCode other}"),
    expect "unknown" (errCode r2) "NotLive"]

def deepLayers : Scenario := fun h => do
  let (e1, _) ← ok! "1" (← h.tx 1 {} (do
    let e1 ← assertV (v "a") (v "p") (v "b")
    let mut cur := e1.eid
    for i in [0:5] do cur := (← assertI cur (v "layer") (.int i)).eid
    pure e1.eid))
  let (_, r) ← ok! "2" (← h.tx 2 {} (supersedeE e1 { o := some (v "c") }))
  let live ← ok! "q" (← h.query nowV triplesQ)
  pure <| allOk [expect "replayed" r.superseded.size 6, expect "live" live.size 7]

def limit : Scenario := fun h => do
  let (e, _) ← ok! "1" (← h.tx 1 {} (do
    let e ← assertV (v "root") (v "p") (.int 1)
    for i in [0:5] do let _ ← assertI e.eid (v "note") (.int i)
    pure e.eid))
  let r ← h.tx 2 { maxCascade := 5 } (supersedeE e { o := some (.int 2) })
  pure (expect "limit" (errCode r) "CascadeLimitExceeded")

def schemaFailures : Scenario := fun h => do
  let (e, _) ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "age" "valueType" (.iri xsdInteger)
    assertV (v "alice") (v "age") (.int 30)))
  let r ← h.tx 2 {} (supersedeE e.eid { o := some (.str "thirty") })
  let (_, _) ← ok! "unique" (← h.tx 3 {} (do
    let _ ← flagV "email" "unique" (.bool true)
    let _ ← assertV (v "alice") (v "email") (.str "a@x.org")
    assertV (v "bob") (v "email") (.str "b@x.org")))
  let bobRow ← ok! "q" (← h.query nowV (triplesQ (some (v "bob")) (some (v "email")) none))
  let r2 ← match bobRow.toList with
    | [b] => h.tx 4 {} (supersedeE ⟨b.eid⟩ { o := some (.str "a@x.org") })
    | _ => pure (.error (.custom "setup"))
  pure <| allOk [expect "value type" (errCode r) "ValueTypeMismatch", expect "unique" (errCode r2) "UniqueViolation"]

def cardinalityOnNewRoot : Scenario := fun h => do
  let ((a, b), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← assertV (v "alice") (v "status") (.str "away") (between "2020-01-01" "2021-01-01")
    let b ← assertV (v "alice") (v "status") (.str "busy") (between "2022-01-01" "2023-01-01")
    pure (a.eid, b.eid)))
  let _ ← ok! "2" (← h.tx 2 {} (flagV "status" "cardinality" (sysV "one")))
  let (_, r) ← ok! "3" (← h.tx 3 {} (supersedeE a { vTo := some none }))
  pure <| allOk [expect "kinds" (kindsOf r.retracted) [(ctr a, .supersede), (ctr b, .cardinality)]]

def all : List (String × Scenario) :=
  [("supersede rewires", rewires), ("supersede cycles", cyclesRewired), ("supersede chain", chain),
   ("supersede close open", closeOpen), ("supersede no change", noChange), ("supersede twice", twice),
   ("supersede deep layers", deepLayers), ("supersede limit", limit),
   ("supersede schema failures", schemaFailures), ("supersede cardinality", cardinalityOnNewRoot)]

end Test.Store.Supersede
