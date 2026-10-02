/-
Refinement and property tests of the query core on random stores:
- sorted range scans: every order × prefix × view, model store vs SQLite, exactly;
- join-order independence: every permutation of 2–4-pattern joins (sampled for 5) equals the
  reference semantics;
- random validated IR trees: reference semantics = evaluator on the model = evaluator on SQLite,
  and provenance rows without citations = plain rows;
- paths, dependents and bundles: model vs SQLite.
-/
import Test.Query.Paths
import Tiramemsu.Prov.EvalProv
import Tiramemsu.Shell.BundleJson

namespace Test.Query.Refine

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Exec
open Test
open Test.Store (v sysV assertV assertI createV enc day retractE between stmt supersedeE)
open Test.Query
open Test.Query.Paths (lcg pick idOf)

/-- A random store: transactions of asserts, parallel creates, layers, memberships, retractions,
valid-time intervals. -/
def randStore (seed : Nat) : List (TxProg Unit) :=
  let nodes := ["a", "b", "c", "d"]
  let preds := ["p", "q", "r"]
  let rec txs : Nat → Nat → Nat → List (TxProg Unit)
    | 0, _, _ => []
    | k + 1, s, nst =>
      let s1 := lcg s; let s2 := lcg s1; let s3 := lcg s2; let s4 := lcg s3; let s5 := lcg s4
      let kind := (s1 / 65536) % 8
      let body : TxProg Unit := do
        if kind == 0 && nst > 0 then
          let _ ← retractE (stmt (1 + (s2 / 65536) % nst)); pure ()
        else if kind == 1 && nst > 0 then
          let _ ← assertI (stmt (1 + (s2 / 65536) % nst)) (v (pick s3 preds)) (v (pick s4 nodes)); pure ()
        else if kind == 2 then
          let _ ← createV (v (pick s2 nodes)) (v (pick s3 preds)) (v (pick s4 nodes)); pure ()
        else if kind == 3 && nst > 0 then
          let _ ← TxProg.verb (.addToGraph (stmt (1 + (s2 / 65536) % nst)) (← enc (v (pick s3 ["g1", "g2"]))) {}); pure ()
        else if kind == 4 then
          let _ ← assertV (v (pick s2 nodes)) (v (pick s3 preds)) (.int ((s4 / 65536) % 5 : Nat)); pure ()
        else if kind == 5 then
          let y := 2020 + (s5 / 65536) % 4
          let _ ← assertV (v (pick s2 nodes)) (v (pick s3 preds)) (v (pick s4 nodes)) (between s!"{y}-01-01" s!"{y + 1}-01-01"); pure ()
        else
          let _ ← assertV (v (pick s2 nodes)) (v (pick s3 preds)) (v (pick s4 nodes)); pure ()
      -- statements created so far (upper bound, for picking eids; misses are fine)
      body :: txs k s5 (nst + 2)
  txs (6 + seed % 10) (lcg (seed * 977 + 13)) 0

/-- Builds a fixture, skipping failing transactions on both stores alike. -/
def buildLenient (name : String) (bodies : List (TxProg Unit)) : IO Fix := do
  let safe := bodies.map fun b => (b : TxProg Unit)
  let mut st := Test.Store.freshModelState
  let path ← freshPath s!"m3r-{name}"
  let db ← Test.Store.openStore path
  let h := Test.Store.sqliteHarness path db (← Term.WriterCache.new none)
  let mut i : Int := 1
  for b in safe do
    let (r, st') := Model.transact (1000 * i) {} b st
    match r with
    | .ok _ =>
      st := st'
      let _ ← h.tx (1000 * i) {} b
      i := i + 1
    | .error _ => pure ()
  return { st, db }

def views (st : ModelState) : List Store.View :=
  let lastT := (st.txs.map (·.t)).foldl (fun a b => if b.toInt > a.toInt then b else a) 0
  [{}, { tx := .asOf 1 }, { tx := .asOf lastT }, { tx := .history }, { valid := .at (day "2021-06-01") },
   { tx := .history, valid := .at (day "2022-06-01") }]

def scanModel (st : ModelState) (p : RProg (List TripleRow)) : Option (List TripleRow) := (p.onModel st).toOption

def termIds (st : ModelState) : List Int64 :=
  ((st.triples.flatMap fun r => [r.s, r.p, r.o]).eraseDups.take 12) ++ [(stmt 1).raw, 999999]

/-! ## Random queries -/

def vars : List String := ["a", "b", "c", "d"]

def randPos (s : Nat) (pool : List String) : TermOrVar :=
  let k := (s / 65536) % 4
  if k == 0 then .const (v (pick (s / 7) pool)) else .var (pick (s / 11) vars)

def randPattern (s : Nat) (sem : Semantics) : IR.Op :=
  let s1 := lcg s; let s2 := lcg s1; let s3 := lcg s2
  let eid := if (s3 / 65536) % 5 == 0 then some "e" else none
  let graph : GraphSel := if (s3 / 65536) % 7 == 1 then .var "g" else if (s3 / 65536) % 7 == 2 then .set [.const (v "g1")] else .any
  let _ := sem
  .triple { s := randPos s1 ["a", "b", "c", "d"], p := (if (s2 / 65536) % 5 == 0 then .var "x" else .const (v (pick s2 ["p", "q", "r"]))),
            o := randPos s3 ["a", "b", "c", "d"], eid, graph,
            view := if (s2 / 65536) % 6 == 0 then View.ViewSpec.asOfT 2 else {} }

/-- A random operator tree that passes validation. -/
def randOp : Nat → Nat → Semantics → IR.Op
  | 0, s, sem => randPattern s sem
  | d + 1, s, sem =>
    let s1 := lcg s; let s2 := lcg s1; let s3 := lcg s2
    let a := randOp d s2 sem
    let b := randOp d s3 sem
    match (s1 / 65536) % 10 with
    | 0 | 1 => .join [a, b]
    | 2 => .union [a, b]
    | 3 => .leftJoin a b none
    | 4 => .filter (.cmp .ne (.var "a") (.const (v "b"))) a
    | 5 => .filter (.bound "b") a
    | 6 => let vs := (outputVars a).take 2; if vs.isEmpty then a else .project vs ((s3 / 65536) % 2 == 0) a
    | 7 => .order [{ expr := .var (pick s3 vars), desc := (s2 / 65536) % 2 == 0 }] none (some (.const (.int 3))) a
    | 8 => let g := (outputVars a).take 1
           if (outputVars a).contains "n" then a else .agg g [{ var := "n", func := .count }] a
    | _ => .join [a, b, randPattern (lcg s3) sem]

def sems : List Semantics := [.sparql, .cypher, { graphSet := .bagOfEids }, { missing := .null3VL }]

def main (seeds : Nat := 30) : IO UInt32 := do
  let (_, r) ← (do
    let mut nQueries := 0
    let mut nScans := 0
    let mut nonEmpty := 0
    for seed in List.range seeds do
      let f ← buildLenient s!"s{seed}" (randStore seed)
      -- scans
      for vw in views f.st do
        for ord in [IndexOrder.spo, .pos, .osp] do
          let ids := termIds f.st
          for k in [0, 1, 2, 3] do
            for x in ids.take 4 do
              let pfx := (List.replicate k x).zipIdx.map fun (y, i) => if i == 0 then y else (ids.getD (i + seed) y)
              let m := scanModel f.st (rangeScan ord vw pfx)
              let sq ← onSqlite f.db (rangeScan ord vw pfx)
              nScans := nScans + 1
              checkEq s!"scan seed {seed} {reprStr ord} {pfx}" sq.toOption m
      -- join orders
      for k in [2, 3, 4, 5] do
        let pats := (List.range k).map fun i => randPattern (lcg (seed * 101 + i * 37 + k)) .sparql
        for sem in sems do
          let q : Query := { root := .join pats, sem }
          let ref := denoteQ f.st [] q
          let ps := if k ≤ 4 then perms pats else (perms pats).take 12
          for perm in ps do
            match ref, evalModel f.st [] { q with root := .join perm } with
            | .ok (p, b), .ok (p', b') =>
              checkEq s!"order seed {seed} k {k}" (rowsBy p' vars b') (rowsBy p vars b)
            | .error _, .error _ => pure ()
            | x, y => check s!"order seed {seed}" false s!"{showErr x} vs {showErr y}"
      -- random trees on every store
      for i in List.range 12 do
        let sem := pick (lcg (seed + i)) sems
        let op := randOp 3 (lcg (seed * 7919 + i)) sem
        let q : Query := { root := op, sem }
        if (validate q).toOption.isNone then continue
        nQueries := nQueries + 1
        let d := denoteQ f.st [] q
        let e := evalModel f.st [] q
        let s ← evalSqlite f.db [] q
        let pr := (Prov.evalQueryProv {} [] q).run.onModel f.st
        match d, e, s with
        | .ok (p, b), .ok (_, b'), .ok (_, b'') =>
          if !b.isEmpty then nonEmpty := nonEmpty + 1
          let isOrder : Bool := match op with | .orderLimit .. => true | _ => false
          if isOrder then
            checkEq s!"tree {seed}/{i} ordered" (b'.map p.project) (b.map p.project)
          else
            checkEq s!"tree {seed}/{i} evaluator" (canon b') (canon b)
          checkEq s!"tree {seed}/{i} sqlite" (canon b'') (canon b')
          match pr with
          | .ok (.ok (_, ab)) => checkEq s!"tree {seed}/{i} provenance erasure" (canon (ab.map (·.1))) (canon b)
          | _ => check s!"tree {seed}/{i} provenance" false
        | .error _, .error _, .error _ => pure ()
        | x, y, z => check s!"tree {seed}/{i}" false s!"{showErr x} / {showErr y} / {showErr z}"
      -- paths, dependents, bundles: model vs SQLite
      for (start, text) in [(v "a", "p+"), (v "b", "(p|q)*/^r"), (.stmt 1, "sys:subject/p?"), (v "c", "sys:anyRelationship{1,3}")] do
        for mode in [PathMode.reach, .trail, .anyShortest, .allShortest] do
          let prog : EvM (List Path.PathRow) := do
            let some sx ← lookupE start | return []
            Path.run {} { start := sx, expr := ← Path.parseText text, mode, maxHops := some 4 }
          let m := (prog.run.onModel f.st)
          let sq ← onSqlite f.db prog.run
          checkEq s!"path seed {seed} {text} {mode.name}" (sq.toOption.bind (·.toOption)) (m.toOption.bind (·.toOption))
      for e in [1, 2, 3] do
        for vs in [({} : View.ViewSpec), View.ViewSpec.asOfT 2] do
          let dm := (View.dependents vs (stmt e)).onModel f.st
          let ds ← onSqlite f.db (View.dependents vs (stmt e))
          checkEq s!"dependents seed {seed} {e}" ds.toOption dm.toOption
          let bm := (Bundle.exportBundle vs (stmt e)).run.onModel f.st
          let bs ← onSqlite f.db (Bundle.exportBundle vs (stmt e)).run
          checkEq s!"bundle seed {seed} {e}" ((bs.toOption.bind (·.toOption)).map Bundle.Bundle.toJson)
            ((bm.toOption.bind (·.toOption)).map Bundle.Bundle.toJson)
      f.db.close
    IO.println s!"  {nScans} scans, {nQueries} random trees ({nonEmpty} with rows)"
    pure () : TestM Unit).run {}
  finish "query refinement" r

end Test.Query.Refine
