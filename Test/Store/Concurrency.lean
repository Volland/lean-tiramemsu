/-
Connection-concurrency tests on the shell `Db`: one mutex-guarded writer, a reader pool and
views pinned to one WAL snapshot; plus the concurrency oracle (N readers and one writer on random
scripts, every recorded read checked against the model store at the view's basis).
-/
import Test.Store.Refine

namespace Test.Store.Concurrency

open Tiramemsu Tiramemsu.Json Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Shell Tiramemsu.Codec
open Test Test.Store

def openDb (name : String) (readers : Nat := 4) (clock : Clock := systemClock) : IO Db := do
  let p ← freshPath name
  match ← Db.open p { readers } clock with
  | .ok db => pure db
  | .error e => throw (IO.userError s!"open {p}: {e}")

def spawn {α : Type} (act : IO α) : IO (Task (Except IO.Error α)) :=
  IO.asTask act (prio := .dedicated)

def join {α : Type} (t : Task (Except IO.Error α)) : IO α := do
  match ← IO.wait t with
  | .ok a => pure a
  | .error e => throw e

def tablesOf (db : Db) : IO ModelState := do
  match ← (loadModelState db.path).run with
  | .ok s => pure s
  | .error e => throw (IO.userError s!"{e}")

/-- 8 tasks × 100 transactions: gap-free numbers and strictly increasing instants. -/
def manyWriters : TestM Unit := do
  let db ← openDb "conc-writers"
  let tasks ← (List.range 8).mapM fun w => spawn do
    for i in [0:100] do
      match ← db.transact {} (assertV (v s!"w{w}") (v "n") (.int i)) with
      | .ok _ => pure ()
      | .error e => throw (IO.userError s!"writer {w}: {e}")
  for t in tasks do join t
  let st ← tablesOf db
  let ts := st.txs.map (·.t.toInt)
  let is := st.txs.map (·.instant.toInt)
  checkEq "800 transactions numbered 1..800" ts ((List.range 800).map (Int.ofNat · + 1))
  check "instants strictly increasing" ((is.zip is.tail).all fun (a, b) => a < b)
  db.close

/-- Two tasks upsert the same value of a unique predicate. -/
def concurrentUpsert : TestM Unit := do
  let db ← openDb "conc-upsert"
  let _ ← db.transact {} (flagV "email" "unique" (.bool true))
  let up : IO ObjectId := do
    match ← db.transact {} (do TxProg.verb (.upsert (← enc (v "email")) (← enc (.str "same@x.org")))) with
    | .ok (n, _) => pure n
    | .error e => throw (IO.userError s!"{e}")
  let a ← spawn up
  let b ← spawn up
  let na ← join a
  let nb ← join b
  let live ← db.withView {} fun pv => pv.run (triplesQ none (some (v "email")) (some (.str "same@x.org")))
  checkEq "same node" na nb
  checkEq "one live statement" (live.toOption.map (·.size)) (some 1)
  db.close

/-- Two handles on one file commit concurrently. -/
def twoHandles : TestM Unit := do
  let p ← freshPath "conc-handles"
  let open1 : IO Db := do
    match ← Db.open p {} with
    | .ok db => pure db
    | .error e => throw (IO.userError s!"{e}")
  let d1 ← open1
  let d2 ← open1
  let work (db : Db) (tag : String) : IO Unit := do
    for i in [0:50] do
      match ← db.transact {} (assertV (v tag) (v "n") (.int i)) with
      | .ok _ => pure ()
      | .error e => throw (IO.userError s!"{tag}: {e}")
  let a ← spawn (work d1 "h1")
  let b ← spawn (work d2 "h2")
  join a; join b
  let st ← tablesOf d1
  checkEq "gap-free across handles" (st.txs.map (·.t.toInt)) ((List.range 100).map (Int.ofNat · + 1))
  d1.close; d2.close

/-- A read completes while the writer is held, and sees only committed state. -/
def readDuringWrite : TestM Unit := do
  let db ← openDb "conc-read-write"
  let _ ← db.transact {} (assertV (v "a") (v "p") (v "b"))
  let started ← IO.mkRef false
  let holder ← spawn (db.withWriter do started.set true; IO.sleep 600)
  while !(← started.get) do IO.sleep 5
  let t0 ← IO.monoMsNow
  let rows ← db.withView {} fun pv => pv.run triplesQ
  let dt := (← IO.monoMsNow) - t0
  join holder
  checkEq "committed rows" (rows.toOption.map (·.size)) (some 1)
  check "did not wait for the writer" (dt < 400) s!"{dt} ms"
  db.close

/-- With two readers held by open views, a third view waits until one ends. -/
def poolExhaustion : TestM Unit := do
  let db ← openDb "conc-pool" 2
  let _ ← db.transact {} (assertV (v "a") (v "p") (v "b"))
  let held ← IO.mkRef 0
  let hold : IO Unit := db.withView {} fun _ => do held.modify (· + 1); IO.sleep 400
  let a ← spawn hold
  let b ← spawn hold
  while (← held.get) < 2 do IO.sleep 5
  let t0 ← IO.monoMsNow
  let r ← db.withView {} fun pv => pv.run triplesQ
  let dt := (← IO.monoMsNow) - t0
  join a; join b
  checkEq "third view succeeds" (r.toOption.map (·.size)) (some 1)
  check "third view waited" (dt ≥ 200) s!"{dt} ms"
  db.close

/-- Two reads of one view see the same snapshot while another task commits in between. -/
def stableView : TestM Unit := do
  let db ← openDb "conc-stable"
  let _ ← db.transact {} (assertV (v "a") (v "p") (v "b"))
  let (r1, r2, b1, b2) ← db.withView {} fun pv => do
    let r1 ← pv.run triplesQ
    let b1 ← pv.run (ReadProg.query .basis)
    let w ← spawn (db.transact {} (assertV (v "c") (v "p") (v "d")))
    let _ ← join w
    let r2 ← pv.run triplesQ
    let b2 ← pv.run (ReadProg.query .basis)
    pure (r1.toOption.map (·.size), r2.toOption.map (·.size), b1.toOption, b2.toOption)
  checkEq "same rows" r1 r2
  checkEq "same basis" b1 b2
  let after ← db.withView {} fun pv => pv.run triplesQ
  checkEq "new view sees the commit" (after.toOption.map (·.size)) (some 2)
  db.close

/-- A term interned by a failed transaction never becomes visible. -/
def failedIntern : TestM Unit := do
  let db ← openDb "conc-intern"
  let _ ← db.transact {} (assertV (v "a") (v "p") (v "b"))
  let r ← db.transact {} (do
    let x ← enc (.str "a string that only a failed transaction interned")
    let _ ← (TxProg.abort (.custom "no") : TxProg Unit)
    pure x)
  check "failed" (!r.isOk)
  -- the id the string would have had is the next term id
  let nextTerm := ((← tablesOf db).counters.find? (·.1 == "next_term")).map (·.2.toNatClampNeg) |>.getD 0
  let id := Term.termId .str nextTerm
  let dec ← db.withView {} fun pv => pv.run (ReadProg.query (.decode id))
  check "reader cannot decode it" (!dec.isOk)
  let w ← db.transact {} (do let x ← enc (.str "another string never seen before"); TxProg.verb (.decode x))
  checkEq "writer cache clean" (w.toOption.map (·.1)) (some (.str "another string never seen before"))
  db.close

/-- Readers never see a speculation's state. -/
def readersDuringSpeculation : TestM Unit := do
  let db ← openDb "conc-spec"
  let _ ← db.transact {} (assertV (v "a") (v "p") (v "b"))
  let done ← IO.mkRef false
  let spec ← spawn do
    for _ in [0:5] do
      let _ ← db.speculate (do for i in [0:400] do let _ ← assertV (v "spec") (v "marker") (.int i)) none
        (do return (← triplesQ (some (v "spec"))).size)
    done.set true
  let mut seen := 0
  let mut reads := 0
  while !(← done.get) do
    let r ← db.withView {} fun pv => pv.run (triplesQ (some (v "spec")))
    seen := seen + (r.toOption.map (·.size)).getD 0
    reads := reads + 1
  join spec
  checkEq "speculative rows seen by readers" seen 0
  check "readers ran during speculation" (reads > 0)
  db.close

/-! ## The concurrency oracle -/

/-- One writer runs a random script (manual clock, set before every step) while readers
record (basis, view, read, result); afterwards every read is checked against the model state
after `basis` commits, obtained by replaying the writer's script on the model. -/
def oracle (seed : Nat) (readers : Nat) (steps : Nat) : TestM Unit := do
  let clock ← ManualClock.new 1000
  let db ← openDb s!"conc-oracle-{seed}" 4 clock.clock
  let script := (Gen.script seed steps).filter (·.op != "m2.read")
  let stop ← IO.mkRef false
  -- the writer: the same steps as the refinement suite, through the shell
  let writer ← spawn do
    let mut ms : Int := 1000
    for s in script do
      match s.op with
      | "m2.setClock" => ms := (s.args.getInt? "ms").getD 0
      | "m2.transact" =>
        clock.set ms
        let opts := (txOptionsOf ((s.args.get? "options").getD .null)).toOption.getD {}
        let _ ← db.transact opts (opsProg ((s.args.getArr? "ops").getD #[]))
      | "m2.with" =>
        clock.set ms
        let _ ← db.speculate (opsProg ((s.args.getArr? "ops").getD #[])) none (pure ())
      | _ => pure ()
    stop.set true
  let readerTasks ← (List.range readers).mapM fun r => spawn do
    let mut log : Array (Int64 × Json × Json) := #[]
    let mut k : Nat := 0
    while !(← stop.get) || k < 3 do
      k := k + 1
      let kk : Nat := k
      let viewJ : Json := match (kk + r) % 4 with
        | 0 => .obj #[("kind", .str "now")]
        | 1 => .obj #[("kind", .str "asOf"), ("tx", .int (((kk * 7 + r) % 9 : Nat) : Int))]
        | 2 => .obj #[("kind", .str "history")]
        | _ => .obj #[("kind", .str "now"), ("validAt", .int 250)]
      let q : Json := match (kk / 4 + r) % 3 with
        | 0 => .obj #[("op", .str "triples")]
        | 1 => .obj #[("op", .str "dependents"), ("eid", .int (((kk % 12) + 1 : Nat) : Int))]
        | _ => .obj #[("op", .str "graphs")]
      let spec := (viewOfJ viewJ).toOption.getD {}
      let rec_ ← db.withView spec fun pv => do
        let res ← pv.run (readProg ((q.getStr? "op").getD "") q)
        pure (pv.basis, Refine.outJ id res)
      log := log.push (rec_.1, .arr #[viewJ, q], rec_.2)
    pure log
  join writer
  let logs ← (readerTasks.mapM join : IO (List (Array (Int64 × Json × Json))))
  -- replay the writer on the model, recording the committed state after every t
  let ref ← IO.mkRef freshModelState
  let m := modelHarness ref
  let states ← IO.mkRef (#[freshModelState] : Array ModelState)
  let cm ← IO.mkRef (1000 : Int)
  for s in script do
    let _ ← Refine.runStep m cm s
    let st ← ref.get
    if st.txs.length + 1 > (← states.get).size then states.modify (·.push st)
  let sts ← states.get
  let mut checked := 0
  let mut bad := 0
  for log in logs do
    for (basis, vq, got) in log do
      let viewJ := (match vq with | .arr #[x, _] => x | _ => .null)
      let q := (match vq with | .arr #[_, y] => y | _ => .null)
      let spec := (viewOfJ viewJ).toOption.getD {}
      let st := sts[basis.toNatClampNeg]!
      let want := Refine.outJ id (Model.query st spec (readProg ((q.getStr? "op").getD "") q))
      checked := checked + 1
      if want.compress != got.compress then
        bad := bad + 1
        if bad ≤ 3 then
          check s!"oracle seed {seed} read at basis {basis} {vq.compress}" false s!"got {got.compress}, model {want.compress}"
  check s!"oracle seed {seed}: {checked} reads" (bad == 0 && checked > 0)
  note s!"concurrency oracle seed {seed}: {checked} reads at {sts.size - 1} transactions checked against the model"
  db.close

def main (args : List String) : IO UInt32 := do
  let seeds := Refine.flagNat args "--seeds" 3
  let (_, r) ← (do
    manyWriters
    concurrentUpsert
    twoHandles
    readDuringWrite
    poolExhaustion
    stableView
    failedIntern
    readersDuringSpeculation
    for s in [1:seeds + 1] do oracle s 4 150 : TestM Unit).run {}
  finish "concurrency" r

end Test.Store.Concurrency
