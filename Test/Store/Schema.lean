/-
Scenarios of predicate-schema.
-/
import Test.Store.Run

namespace Test.Store.Schema

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Test.Store

def withinTx : Scenario := fun h => do
  let r ← h.tx 1 {} (do
    let _ ← flagV "email" "unique" (.bool true)
    let _ ← assertV (v "alice") (v "email") (.str "a@x.org")
    assertV (v "bob") (v "email") (.str "a@x.org"))
  pure (expect "error" (errCode r) "UniqueViolation")

def liftConstraint : Scenario := fun h => do
  let (f, _) ← ok! "1" (← h.tx 1 {} (flagV "email" "unique" (.bool true)))
  let _ ← ok! "2" (← h.tx 2 {} (retractE f.eid))
  let r ← h.tx 3 {} (do
    let _ ← assertV (v "alice") (v "email") (.str "a@x.org")
    assertV (v "bob") (v "email") (.str "a@x.org"))
  pure (expect "ok" (errCode r) "ok")

def changeFlag : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (flagV "tag" "cardinality" (sysV "one")))
  let (b, r) ← ok! "2" (← h.tx 2 {} (flagV "tag" "cardinality" (sysV "many")))
  let live ← ok! "q" (← h.query nowV (eidsQ (some (v "tag")) none none))
  pure <| allOk [expect "kind" (kindsOf r.retracted) [(ctr a.eid, .cardinality)], expect "live" live [ctr b.eid]]

def subjectTypesAccumulate : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (flagV "note" "subjectType" (tagV .stmt)))
  let (b, r) ← ok! "2" (← h.tx 2 {} (flagV "note" "subjectType" (tagV .tx)))
  let live ← ok! "q" (← h.query nowV (eidsQ (some (v "note")) none none))
  pure <| allOk [expect "nothing retracted" r.retracted.size 0, expect "both" live [ctr a.eid, ctr b.eid]]

def flagValidation : Scenario := fun h => do
  let a ← h.tx 1 {} (flagV "x" "unique" (.int 5))
  let b ← h.tx 1 {} (assertV (sysV "foo") (sysV "unique") (.bool true))
  let c ← h.tx 1 {} (flagV "x" "cardinality" (v "three"))
  let d ← h.tx 1 {} (flagV "x" "subjectType" (tagV .int))
  let e ← h.tx 1 {} (flagV "x" "valueType" (sysV "NOPE"))
  let f ← h.tx 1 {} (assertV (.node 1) (sysV "unique") (.bool true))
  let g ← h.tx 1 {} (flagV "x" "valueType" (tagV .int))
  pure <| allOk [expect "unique int" (errCode a) "ValueTypeMismatch", expect "sys subject" (errCode b) "ReservedNamespace",
    expect "cardinality three" (errCode c) "ValueTypeMismatch", expect "subjectType INT" (errCode d) "ValueTypeMismatch",
    expect "valueType sys" (errCode e) "ValueTypeMismatch", expect "node subject" (errCode f) "InvalidTerm",
    expect "valueType tag ok" (errCode g) "ok"]

def valueTypeFirst : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "confidence" "valueType" (.iri xsdDouble)
    flagV "confidence" "subjectType" (tagV .stmt)))
  let r ← h.tx 2 {} (assertV (v "alice") (v "confidence") (.str "high"))
  pure (expect "error" (errCode r) "ValueTypeMismatch")

def uniqueOnlyOnInsert : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "email" "unique" (.bool true)
    assertV (v "alice") (v "email") (.str "a@x.org")))
  let (b, _) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "email") (.str "a@x.org")))
  pure (expect "existing" b (.existing a.eid))

def replacementWithoutAnnotations : Scenario := fun h => do
  let ((e1, e2), _) ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "age" "cardinality" (sysV "one")
    let e1 ← assertV (v "alice") (v "age") (.int 30)
    let e2 ← assertI e1.eid (v "source") (v "form")
    pure (e1.eid, e2.eid)))
  let (n, r) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "age") (.int 31)))
  pure <| allOk [expect "kinds" (kindsOf r.retracted) [(ctr e1, .cardinality), (ctr e2, .cardinality)],
    expect "no annotation" (← ok! "q" (← h.query nowV (eidsQ (some (.stmt (ctr n.eid))) none none))) []]

def episodes : Scenario := fun h => do
  let (a, _) ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "worksAt" "cardinality" (sysV "one")
    assertV (v "alice") (v "worksAt") (v "acme") (between "2020-01-01" "2022-01-01")))
  let (b, _) ← ok! "2" (← h.tx 2 {} (assertV (v "alice") (v "worksAt") (v "globex") (fromD "2022-01-01")))
  pure (expect "both live" (← ok! "q" (← h.query nowV (eidsQ (some (v "alice")) none none))) [ctr a.eid, ctr b.eid])

def secondSubject : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do
    let _ ← flagV "email" "unique" (.bool true)
    assertV (v "alice") (v "email") (.str "a@x.org")))
  let before ← h.tables
  let r ← h.tx 2 {} (assertV (v "bob") (v "email") (.str "a@x.org"))
  let ids ← ok! "q" (← h.query nowV (do
    let p ← ReadProg.query (.lookup (v "email"))
    let s ← ReadProg.query (.lookup (v "alice"))
    let o ← ReadProg.query (.lookup (.str "a@x.org"))
    pure (p, s, o)))
  pure <| allOk [
    (match r, ids with
     | .error (.uniqueViolation p o x), (some p', some s', some o') => expect "names" (p, o, x) (p', o', s')
     | _, _ => some s!"expected UniqueViolation, got {errCode r}"),
    expect "no trace" ((← h.tables) == before) true]

def upsertTwice : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (flagV "email" "unique" (.bool true)))
  let ((a, b), r) ← ok! "2" (← h.tx 2 {} (do
    let p ← enc (v "email")
    let o ← enc (.str "new@x.org")
    let a ← TxProg.verb (.upsert p o)
    let b ← TxProg.verb (.upsert p o)
    pure (a, b)))
  let bad ← h.tx 3 {} (do TxProg.verb (.upsert (← enc (v "name")) (← enc (.str "x"))))
  pure <| allOk [expect "same node" a b, expect "node" (a.tag.toOption) (some .node),
    expect "one statement" r.asserted.size 1, expect "not unique" (errCode bad) "NotUniquePredicate"]

def typedLayer : Scenario := fun h => do
  let ((e1, _), _) ← ok! "1" (← h.tx 1 {} (do
    let f ← flagV "confidence" "subjectType" (tagV .stmt)
    let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
    pure (e1.eid, f)))
  let ok1 ← h.tx 2 {} (assertI e1 (v "confidence") (dbl "0.8"))
  let bad ← h.tx 3 {} (assertV (v "alice") (v "confidence") (dbl "0.8"))
  pure <| allOk [expect "layer ok" (errCode ok1) "ok", expect "node level" (errCode bad) "SubjectTypeMismatch"]

def stringType : Scenario := fun h => do
  let r ← h.tx 1 {} (do
    let _ ← flagV "name" "valueType" (.iri xsdString)
    let _ ← assertV (v "a") (v "name") (.str "Al")
    assertV (v "b") (v "name") (.str "Alexandrina"))
  let r2 ← h.tx 2 {} (assertV (v "c") (v "name") (.int 5))
  pure <| allOk [expect "both" (errCode r) "ok", expect "int rejected" (errCode r2) "ValueTypeMismatch"]

def uniqueOnDuplicated : Scenario := fun h => do
  let ((a, b), _) ← ok! "1" (← h.tx 1 {} (do
    let a ← assertV (v "alice") (v "email") (.str "a@x.org")
    let b ← assertV (v "bob") (v "email") (.str "a@x.org")
    pure (a.eid, b.eid)))
  let r ← h.tx 2 {} (flagV "email" "unique" (.bool true))
  pure <| match r with
    | .error (.schemaConflict xs) => expect "violating" (xs.map ctr) [ctr a, ctr b]
    | other => some s!"expected SchemaConflict, got {errCode other}"

def otherConflicts : Scenario := fun h => do
  let _ ← ok! "1" (← h.tx 1 {} (do
    let _ ← assertV (v "alice") (v "age") (.int 30)
    let _ ← assertV (v "alice") (v "age") (.int 31)
    let _ ← assertV (v "alice") (v "nick") (.str "al")
    assertV (v "alice") (v "conf") (.int 1)))
  let a ← h.tx 2 {} (flagV "age" "cardinality" (sysV "one"))
  let b ← h.tx 2 {} (flagV "nick" "valueType" (.iri xsdInteger))
  let c ← h.tx 2 {} (flagV "conf" "subjectType" (tagV .stmt))
  pure <| allOk [expect "one" (errCode a) "SchemaConflict", expect "valueType" (errCode b) "SchemaConflict",
    expect "subjectType" (errCode c) "SchemaConflict"]

def subjectTypeRetraction : Scenario := fun h => do
  let ((fs, ft, l), _) ← ok! "1" (← h.tx 1 {} (do
    let fs ← flagV "note" "subjectType" (tagV .stmt)
    let ft ← flagV "note" "subjectType" (tagV .tx)
    let e ← assertV (v "a") (v "p") (v "b")
    let l ← assertI e.eid (v "note") (.str "layer")
    pure (fs.eid, ft.eid, l.eid)))
  let narrowing ← h.tx 2 {} (retractE fs)
  let _ ← ok! "3" (← h.tx 3 {} (retractE ft))
  let (lastOk, _) ← ok! "4" (← h.tx 4 {} (retractE fs))
  pure <| allOk [
    (match narrowing with
     | .error (.schemaConflict xs) => expect "violating" (xs.map ctr) [ctr l]
     | other => some s!"expected SchemaConflict, got {errCode other}"),
    expect "last lifts" lastOk true]

def all : List (String × Scenario) :=
  [("schema within tx", withinTx), ("schema lift", liftConstraint), ("schema change flag", changeFlag),
   ("schema subject types", subjectTypesAccumulate), ("schema flag validation", flagValidation),
   ("schema value type first", valueTypeFirst), ("schema unique only on insert", uniqueOnlyOnInsert),
   ("schema replacement", replacementWithoutAnnotations), ("schema episodes", episodes),
   ("schema second subject", secondSubject), ("schema upsert", upsertTwice),
   ("schema typed layer", typedLayer), ("schema string type", stringType),
   ("schema unique conflict", uniqueOnDuplicated), ("schema other conflicts", otherConflicts),
   ("schema subject type retraction", subjectTypeRetraction)]

end Test.Store.Schema
