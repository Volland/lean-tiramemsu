/-
Scenarios of fact-bundles on the model store and on SQLite: members, exclusions, order and
stability, anonymous nodes, import (round trip, atomic failure, re-import), cycles, the past,
and the JSON form (round trip, strict reading).
-/
import Test.Query.Util
import Tiramemsu.Shell.BundleJson
import Test.Query.Paths

namespace Test.Query.Bundles

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.Bundle Tiramemsu.Shell
open Test
open Test.Store (v sysV assertV assertI createV enc day retractE between stmt supersedeE flagV)
open Test.Query

def exportM (st : ModelState) (vs : View.ViewSpec) (root : ObjectId) : Except Error Bundle :=
  match (exportBundle vs root).run.onModel st with
  | .ok r => r
  | .error e => .error (.store e)

def exportS (f : Fix) (vs : View.ViewSpec) (root : ObjectId) : IO (Except Error Bundle) := do
  match ← onSqlite f.db (exportBundle vs root).run with
  | .ok r => pure r
  | .error e => pure (.error (.store e))

/-- Exports on both stores; they must agree. -/
def exportBoth (name : String) (f : Fix) (vs : View.ViewSpec) (root : ObjectId) : TestM (Except Error Bundle) := do
  let a := exportM f.st vs root
  let b ← exportS f vs root
  checkEq s!"{name} [sqlite = model]" (b.toOption.map Bundle.toJson) (a.toOption.map Bundle.toJson)
  return a

def preds (b : Bundle) : List String := b.statements.map fun s => s.p.lexical

def errCode {α : Type} : Except Error α → String
  | .ok _ => "ok"
  | .error e => e.code

def main : IO UInt32 := do
  let (_, r) ← (do
    -- e1 = alice worksAt acme; e2 = e1 confidence 0.8; e3 = e2 source chat; e4 = belief9 supportedBy e1
    let f ← buildBoth "bundle1" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let e2 ← assertI e1.eid (v "confidence") (.decimal "0.8")
      let _ ← assertI e2.eid (v "source") (v "chat")
      let _ ← TxProg.verb (.assert (← enc (v "belief9")) (← enc (v "supportedBy")) e1.eid {})
      pure ()]
    match ← exportBoth "layers" f {} (stmt 1) with
    | .ok b =>
      checkEq "layers, nested layers, supporting belief" b.statements.length 4
      checkEq "references come first" (preds b |>.take 1) [Vocab.vIri "worksAt"]
      checkEq "stable output" (exportM f.st {} (stmt 1) |>.toOption) (some b)
      -- JSON round trip
      checkEq "json round trip" (Bundle.fromJson b.toJson |>.toOption) (some b)
    | .error e => check "layers" false (toString e)
    match ← exportBoth "evidence downward" f {} (stmt 4) with
    | .ok b => checkEq "evidence carried downward" (preds b) [Vocab.vIri "worksAt", Vocab.vIri "supportedBy"]
    | .error e => check "evidence" false (toString e)
    match ← exportBoth "layer root" f {} (stmt 2) with
    | .ok b => checkEq "root after its reference" b.root 1
    | .error e => check "layer root" false (toString e)
    checkEq "not live" (errCode (exportM f.st {} (stmt 99))) "NotLive"
    -- exclusions: confirmation and supersede links
    let f2 ← buildBoth "bundle2" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← TxProg.verb (.confirm e1.eid); pure (),
      do let _ ← supersedeE (stmt 1) { o := some (v "globex") }; pure ()]
    match ← exportBoth "confirmation" f2 (View.ViewSpec.asOfT 1) (stmt 1) with
    | .ok b => checkEq "confirmation left out" (preds b) [Vocab.vIri "worksAt"]
    | .error e => check "confirmation" false (toString e)
    let rows := f2.st.triples.filter fun r => r.tRet.isNone
    let newRoot := (rows.find? fun r => r.p == (Test.Query.Paths.idOf f2.st (v "worksAt"))).map (·.eid)
    match newRoot with
    | some e =>
      match ← exportBoth "supersede" f2 {} ⟨e⟩ with
      | .ok b => checkEq "supersede link left out" ((preds b).contains (Vocab.sys ++ "supersedes")) false
      | .error err => check "supersede" false (toString err)
    | none => check "supersede root" false
    -- round trip into an empty database; re-import changes nothing
    let fa ← buildBoth "bundle3" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← assertI e1.eid (v "confidence") (.decimal "0.8"); pure ()]
    match exportM fa.st {} (stmt 1) with
    | .ok b =>
      let bJ := Bundle.fromJson b.toJson
      match bJ with
      | .ok b' =>
        let (r1, st1) := Model.transact 5000 {} (importBundle b') Test.Store.freshModelState
        match r1 with
        | .ok (rep, _) =>
          checkEq "round trip: two new statements" (rep.statements.map (·.new)) [true, true]
          let layer := st1.triples.find? fun r => r.eid == ((rep.statements.getD 1 default).eid.raw)
          checkEq "layer subject is the new root" (layer.map (·.s)) (some rep.root.raw)
          let (r2, st2) := Model.transact 6000 {} (importBundle b') st1
          match r2 with
          | .ok (rep2, _) =>
            checkEq "second import: nothing new" (rep2.statements.map (·.new)) [false, false]
            checkEq "second import: no statement added" st2.triples.length st1.triples.length
          | .error e => check "second import" false (toString e)
          -- export of the imported root equals the original bundle
          checkEq "export after import" (exportM st1 {} rep.root |>.toOption) (some b)
        | .error e => check "round trip" false (toString e)
      | .error e => check "json" false (toString e)
    | .error e => check "export" false (toString e)
    -- schema violation fails atomically
    let fb ← build [do
      let _ ← flagV "worksAt" "unique" (.bool true)
      let _ ← assertV (v "zed") (v "worksAt") (v "acme"); pure ()]
    match exportM fa.st {} (stmt 1) with
    | .ok b =>
      let (r3, st3) := Model.transact 7000 {} (importBundle b) fb
      checkEq "schema violation fails" (errCode r3) "UniqueViolation"
      checkEq "target unchanged" (st3.triples.length) fb.triples.length
    | .error e => check "export" false (toString e)
    -- anonymous nodes
    let b4 : Bundle := { root := 0, statements := [
      { local_ := 0, s := .node 0, p := v "knows", o := .node 1 },
      { local_ := 1, s := .node 0, p := v "likes", o := .value (v "x") }] }
    let (r4, st4) := Model.transact 1000 {} (importBundle b4) Test.Store.freshModelState
    match r4 with
    | .ok _ =>
      let subj := st4.triples.map (·.s)
      checkEq "two fresh nodes, first shared" (subj.eraseDups.length, (st4.triples.map (·.o)).length) (1, 2)
    | .error e => check "anonymous nodes" false (toString e)
    -- a cycle fails before writing
    let b5 : Bundle := { root := 0, statements := [
      { local_ := 0, s := .stmt 1, p := v "about", o := .value (v "x") },
      { local_ := 1, s := .stmt 0, p := v "about", o := .value (v "y") }] }
    let (r5, st5) := Model.transact 1000 {} (importBundle b5) Test.Store.freshModelState
    checkEq "cycle unsupported" (match r5 with | .error (.unsupported m) => m | _ => "") "bundle with a reference cycle"
    checkEq "cycle writes nothing" st5.triples.length 0
    -- malformed: unknown reference, skolem term
    let b6 : Bundle := { root := 0, statements := [{ local_ := 0, s := .stmt 7, p := v "p", o := .value (v "x") }] }
    checkEq "unknown reference" (errCode (Model.transact 1000 {} (importBundle b6) Test.Store.freshModelState).1) "InvalidTerm"
    let b7 : Bundle := { root := 0, statements := [{ local_ := 0, s := .value (.node 3), p := v "p", o := .value (v "x") }] }
    checkEq "skolem term rejected" (errCode (Model.transact 1000 {} (importBundle b7) Test.Store.freshModelState).1) "InvalidTerm"
    -- the past: a layer retracted at transaction 2, bundle as of 1
    let fc ← buildBoth "bundle4" [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← assertI e1.eid (v "confidence") (.decimal "0.8"); pure (),
      do let _ ← retractE (stmt 2); pure ()]
    match ← exportBoth "past" fc (View.ViewSpec.asOfT 1) (stmt 1) with
    | .ok b => checkEq "since-retracted layer" b.statements.length 2
    | .error e => check "past" false (toString e)
    match ← exportBoth "now" fc {} (stmt 1) with
    | .ok b => checkEq "layer gone now" b.statements.length 1
    | .error e => check "now" false (toString e)
    -- JSON: unknown version
    checkEq "unknown version" (errCode (Bundle.fromJson "{\"format\":\"tiramemsu-bundle/2\",\"root\":0,\"statements\":[]}")) "InvalidTerm"
    checkEq "json text" (b4.toJson)
      "{\"format\":\"tiramemsu-bundle/1\",\"root\":0,\"statements\":[{\"id\":0,\"o\":{\"blank\":1},\"p\":\"urn:tiramemsu:v:knows\",\"s\":{\"blank\":0}},{\"id\":1,\"o\":{\"iri\":\"urn:tiramemsu:v:x\"},\"p\":\"urn:tiramemsu:v:likes\",\"s\":{\"blank\":0}}]}"
    -- JSON round trip on generated bundles (all term kinds, valid times)
    let vals : List Value := [v "x", .str "a \"quoted\"\n line", .langStr "hi" "en", .int (-5), .decimal "1.5",
      .double ⟨0x3FF8000000000000⟩, .bool true, .dateTime 1700000000000 (some 60), .date 19000, .typed "x" "urn:dt"]
    for seed in List.range 200 do
      let n := 1 + seed % 4
      let sts := (List.range n).map fun i =>
        let k := (seed * 7 + i * 13) % 11
        let t : BTerm := if k < 3 && i > 0 then .stmt (i - 1) else if k < 5 then .node (k % 2) else .value (vals.getD (k % vals.length) (v "x"))
        ({ local_ := i, s := (if i > 0 && seed % 2 == 0 then .stmt 0 else .value (v s!"s{i}")), p := v s!"p{k}", o := t,
           vFrom := if k % 3 == 0 then some (Int64.ofInt (k * 1000)) else none,
           vTo := if k % 5 == 0 then some (Int64.ofInt (k * 100000)) else none } : BStmt)
      let b : Bundle := { root := seed % n, statements := sts }
      checkEq s!"json round trip {seed}" (Bundle.fromJson b.toJson |>.toOption) (some b)
    pure () : TestM Unit).run {}
  finish "bundle scenarios" r

end Test.Query.Bundles
