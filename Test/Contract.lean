/-
Store-contract scenario tests. Each scenario is written once against the store interface and
runs unchanged on `ModelStore` and on `SqliteStore` ("Same code on both stores").
SQLite-only scenarios (close during a transaction, readers cannot write, trigger aborts,
storage errors) follow.
-/
import Test.Util

namespace Test.Contract

open Test Tiramemsu.Store Tiramemsu.Sqlite

--# @lat: [[verification#Tested Store Properties]]

section Generic

variable {m : Type → Type} {snap : Type} {r : Type → Type}
variable [Monad m] [MonadExceptOf StoreError m] [WriteStore m] [SnapshotStore m snap r]
variable [Monad r] [MonadExceptOf StoreError r] [ReadStore r]

/-- A scenario result: `none` passes, `some detail` fails. -/
abbrev Outcome := Option String

def attempt {n : Type → Type} [Monad n] [MonadExceptOf StoreError n] {α : Type} (x : n α) :
    n (Except StoreError α) :=
  tryCatchThe StoreError (Except.ok <$> x) (fun e => pure (.error e))

/-- Every row of a scan, in delivery order. -/
def rowsOf {n : Type → Type} [Monad n] [ReadStore n] (sp : ScanSpec) : n (List TripleRow) := do
  let acc ← ReadStore.scan sp (#[] : Array TripleRow) fun acc r => pure (.yield (acc.push r))
  pure acc.toList

def row (eid s p o tAdd : Int64) : TripleRow := { eid, s, p, o, tAdd }

def expectEq {α : Type} [BEq α] [Repr α] (what : String) (got want : α) : Outcome :=
  if got == want then none else some s!"{what}: got {reprStr got}, want {reprStr want}"

def all (os : List Outcome) : Outcome := os.findSome? id

/-- Inserts rows in one committed transaction. -/
def seed (rows : List TripleRow) : m Unit := do
  WriteStore.begin
  for x in rows do WriteStore.insertTriple x
  WriteStore.commit

def isMisuse {α : Type} : Except StoreError α → Bool
  | .error (.misuse _) => true
  | _ => false

def errIs {α : Type} (e : StoreError) : Except StoreError α → Bool
  | .error e' => e == e'
  | _ => false

def eids (xs : List TripleRow) : List Int64 := xs.map (·.eid)

def signedOrder : m Outcome := do
  seed [row 1 (2 ^ 62) 5 5 1, row 2 0 5 5 1, row 3 (-1) 5 5 1]
  let xs ← rowsOf (n := m) { family := .liveSpo }
  pure (expectEq "subjects" (xs.map (·.s)) [-1, 0, 2 ^ 62])

def historyNewestFirst : m Outcome := do
  seed [row 1 1 2 3 3, row 2 1 2 3 7, row 3 1 2 3 5]
  let xs ← rowsOf (n := m) { family := .histSpo, pre := #[1, 2, 3], view := { tx := .history } }
  pure (expectEq "t_add" (xs.map (·.tAdd)) [7, 5, 3])

def absentFirst : m Outcome := do
  seed [{ row 1 1 9 1 1 with vFrom := some 10 }, row 2 2 9 2 1]
  let xs ← rowsOf (n := m) { family := .validP, pre := #[9] }
  pure (expectEq "v_from" (xs.map (·.vFrom)) [none, some 10])

def seekLowerBound : m Outcome := do
  seed [row 1 1 7 90 1, row 2 2 7 10 1, row 3 3 7 40 1]
  let xs ← rowsOf (n := m) { family := .livePos, pre := #[7], lo := some (.incl 40) }
  pure (expectEq "o" (xs.map (·.o)) [40, 90])

def earlyStop : m Outcome := do
  seed ((List.range 1000).map fun i => row (i + 1).toInt64 (1000 - i).toInt64 1 1 1)
  let got ← ReadStore.scan { family := .liveSpo } (#[] : Array Int64) fun acc r =>
    let acc := acc.push r.s
    pure (if acc.size == 3 then .done acc else .yield acc)
  pure (expectEq "first three subjects" got.toList [1, 2, 3])

def invalidScans : m Outcome := do
  let a ← attempt (rowsOf (n := m) { family := .liveSpo, view := { tx := .asOf 5 } })
  let b ← attempt (rowsOf (n := m) { family := .validP, pre := #[1, 2] })
  let c ← attempt (rowsOf (n := m) { family := .logAdd, pre := #[1] })
  let d ← attempt (rowsOf (n := m) { family := .histSpo, view := { tx := .asOf 5 } })
  pure (all [ if errIs .invalidScan a then none else some "live spo under as-of",
              if errIs .invalidScan b then none else some "valid prefix of two",
              if errIs .invalidScan c then none else some "log with a prefix",
              if d matches .ok _ then none else some "history under as-of must be valid" ])

def retractedBetween : m Outcome := do
  seed [{ row 1 1 2 3 5 with tRet := some 9, retKind := some 0 }]
  let asOf (t : Int64) := rowsOf (n := m) { family := .histSpo, view := { tx := .asOf t } }
  let a ← asOf 8; let b ← asOf 9; let c ← asOf 4
  pure (expectEq "visible under as-of 8, 9, 4" [a.length, b.length, c.length] [1, 0, 0])

def halfOpenValid : m Outcome := do
  seed [{ row 1 1 2 3 1 with vFrom := some 100, vTo := some 200 }]
  let validAt (d : Int64) := rowsOf (n := m) { family := .liveSpo, view := { valid := .at d } }
  let a ← validAt 100; let b ← validAt 199; let c ← validAt 200
  pure (expectEq "visible at 100, 199, 200" [a.length, b.length, c.length] [1, 1, 0])

def pointReads : m Outcome := do
  WriteStore.begin
  for (t, i) in [(1, 100), (2, 200), (3, 300)] do WriteStore.insertTx { t, instant := i }
  WriteStore.insertTerm { id := 1, tag := 1, lex := "x" }
  WriteStore.insertTriple (row 5 1 2 3 1)
  WriteStore.setCounter "next_stmt" 6
  WriteStore.addPredMulti 2
  WriteStore.addPredMulti 2
  WriteStore.commit
  let tx ← ReadStore.txAtOrBefore (m := m) 250
  let early ← ReadStore.txAtOrBefore (m := m) 50
  let withDt ← ReadStore.termByKey (m := m) 1 "x" (some 7) none
  let noDt ← ReadStore.termByKey (m := m) 1 "x" none none
  let missingTriple ← ReadStore.triple (m := m) 99
  let missingTerm ← ReadStore.termById (m := m) 99
  let missingTx ← ReadStore.txByT (m := m) 99
  let counter ← ReadStore.counter (m := m) "next_stmt"
  let noCounter ← ReadStore.counter (m := m) "nope"
  let pm ← ReadStore.predMulti (m := m) 2
  let notPm ← ReadStore.predMulti (m := m) 3
  pure (all [expectEq "tx at or before 250" tx (some { t := 2, instant := 200 }),
             expectEq "tx before the first" early none,
             expectEq "term key with datatype 7" withDt none,
             expectEq "term key without datatype" noDt (some 1),
             expectEq "missing rows are absent" (missingTriple.isNone, missingTerm.isNone, missingTx.isNone) (true, true, true),
             expectEq "counter" (counter, noCounter) (some 6, none),
             expectEq "pred_multi" (pm, notPm) (true, false)])

def reusedId : m Outcome := do
  seed [{ row 1 1 2 3 1 with tRet := some 2, retKind := some 0 }]
  WriteStore.begin
  let e ← attempt (WriteStore.insertTriple (m := m) (row 1 9 9 9 3))
  WriteStore.commit
  let r ← ReadStore.triple (m := m) 1
  pure (all [if errIs (.violation .idReused) e then none else some "expected idReused",
             expectEq "existing row" (r.map (·.s)) (some 1)])

def numericNormalization : m Outcome := do
  WriteStore.begin
  WriteStore.insertTerm { id := 1, tag := 5, lex := "-0", num := some 0x8000000000000000 }
  WriteStore.insertTerm { id := 2, tag := 5, lex := "NaN", num := some 0x7FF8000000000000 }
  WriteStore.commit
  let a ← ReadStore.termById (m := m) 1
  let b ← ReadStore.termById (m := m) 2
  pure (expectEq "num" (a.map (·.num), b.map (·.num)) (some (some 0), some none))

def termViolations : m Outcome := do
  WriteStore.begin
  WriteStore.insertTerm { id := 1, tag := 1, lex := "a\x00b", dt := none, lang := none }
  let sameId ← attempt (WriteStore.insertTerm (m := m) { id := 1, tag := 2, lex := "z" })
  let sameKey ← attempt (WriteStore.insertTerm (m := m) { id := 2, tag := 1, lex := "a\x00b", dt := some 0 })
  WriteStore.insertTx { t := 1, instant := 10 }
  let sameT ← attempt (WriteStore.insertTx (m := m) { t := 1, instant := 11 })
  let sameInstant ← attempt (WriteStore.insertTx (m := m) { t := 2, instant := 10 })
  WriteStore.commit
  let back ← ReadStore.termById (m := m) 1
  pure (all [if errIs (.violation .idReused) sameId then none else some "term id reused",
             if errIs (.violation .termKeyTaken) sameKey then none else some "term key taken",
             if errIs (.violation .idReused) sameT then none else some "tx number reused",
             if errIs (.violation .instantTaken) sameInstant then none else some "instant taken",
             expectEq "text with NUL round-trips" (back.map (·.lex)) (some "a\x00b")])

def retractLive : m Outcome := do
  seed [{ row 1 1 2 3 1 with vFrom := some 4 }, row 2 1 2 4 1]
  WriteStore.begin
  WriteStore.retract 1 9 2
  WriteStore.commit
  let a ← ReadStore.triple (m := m) 1
  let b ← ReadStore.triple (m := m) 2
  pure (all [expectEq "retracted row" a (some { row 1 1 2 3 1 with vFrom := some 4, tRet := some 9, retKind := some 2 }),
             expectEq "other row" b (some (row 2 1 2 4 1))])

def retractTwice : m Outcome := do
  seed [row 1 1 2 3 1]
  WriteStore.begin
  WriteStore.retract 1 4 0
  let e ← attempt (WriteStore.retract (m := m) 1 5 1)
  let nf ← attempt (WriteStore.retract (m := m) 77 5 1)
  WriteStore.commit
  let a ← ReadStore.triple (m := m) 1
  pure (all [if errIs (.violation .retractOnce) e then none else some "retract once",
             if errIs .notFound nf then none else some "not found",
             expectEq "first t_ret kept" (a.bind (·.tRet)) (some 4)])

def volatileUpsert : m Outcome := do
  WriteStore.begin
  WriteStore.volatilePut { s := 1, key := 2, value := 1, updatedAt := 10 }
  WriteStore.volatilePut { s := 1, key := 2, value := 2, updatedAt := 11 }
  WriteStore.volatilePut { s := 1, key := 1, value := 5, updatedAt := 12 }
  WriteStore.volatilePut { s := 2, key := 0, value := 7, updatedAt := 13 }
  WriteStore.volatileDel 2 0
  WriteStore.commit
  let v ← ReadStore.volatileGet (m := m) 1 2
  let all1 ← ReadStore.volatileOf (m := m) 1
  let gone ← ReadStore.volatileGet (m := m) 2 0
  pure (all [expectEq "value" (v.map (·.value)) (some 2),
             expectEq "rows of s=1 by key" (all1.toList.map (·.key)) [1, 2],
             expectEq "deleted" gone none])

def failedWriteInTx : m Outcome := do
  WriteStore.begin
  WriteStore.insertTriple (row 1 1 2 3 1)
  let e ← attempt (WriteStore.insertTriple (m := m) (row 1 4 5 6 1))
  let c ← attempt (WriteStore.commit (m := m))
  let a ← ReadStore.triple (m := m) 1
  pure (all [if errIs (.violation .idReused) e then none else some "second append",
             if c matches .ok _ then none else some "commit",
             expectEq "e1 stored" (a.map (·.s)) (some 1)])

def rollbackToSavepoint : m Outcome := do
  WriteStore.begin
  WriteStore.insertTriple (row 1 1 1 1 1)
  WriteStore.savepoint "s"
  WriteStore.insertTriple (row 2 2 2 2 1)
  WriteStore.rollbackTo "s"
  WriteStore.insertTriple (row 3 3 3 3 1)
  WriteStore.release "s"
  WriteStore.commit
  let xs ← rowsOf (n := m) { family := .logAdd, view := { tx := .history } }
  pure (expectEq "stored" (eids xs) [1, 3])

def rollbackRestores : m Outcome := do
  seed [row 1 1 1 1 1]
  WriteStore.begin
  WriteStore.insertTriple (row 2 2 2 2 2)
  WriteStore.retract 1 2 0
  WriteStore.rollback
  let xs ← rowsOf (n := m) { family := .liveSpo }
  pure (expectEq "after rollback" xs [row 1 1 1 1 1])

def writeWithoutTx : m Outcome := do
  let e ← attempt (WriteStore.insertTriple (m := m) (row 1 1 2 3 1))
  let xs ← rowsOf (n := m) { family := .logAdd, view := { tx := .history } }
  pure (all [if isMisuse e then none else some "expected misuse", expectEq "nothing stored" xs []])

def misuse : m Outcome := do
  let c ← attempt (WriteStore.commit (m := m))
  let r ← attempt (WriteStore.rollback (m := m))
  let s ← attempt (WriteStore.savepoint (m := m) "x")
  WriteStore.begin
  let nested ← attempt (WriteStore.begin (m := m))
  let unknown ← attempt (WriteStore.rollbackTo (m := m) "nope")
  let unknownRelease ← attempt (WriteStore.release (m := m) "nope")
  WriteStore.savepoint "a"
  WriteStore.savepoint "b"
  WriteStore.release "a"
  let closed ← attempt (WriteStore.rollbackTo (m := m) "b")
  WriteStore.commit
  pure (all [if isMisuse c then none else some "commit without tx",
             if isMisuse r then none else some "rollback without tx",
             if isMisuse s then none else some "savepoint outside tx",
             if isMisuse nested then none else some "nested begin",
             if isMisuse unknown then none else some "unknown savepoint",
             if isMisuse unknownRelease then none else some "release unknown savepoint",
             if isMisuse closed then none else some "savepoint released with an older one"])

def snapshotAfterCommit : m Outcome := do
  seed [row 1 1 1 1 1]
  let rd ← SnapshotStore.beginRead (m := m)
  seed [row 2 2 2 2 2]
  let old ← SnapshotStore.withSnapshot rd (rowsOf (n := r) { family := .liveSpo })
  SnapshotStore.endRead rd
  let rd2 ← SnapshotStore.beginRead (m := m)
  let new ← SnapshotStore.withSnapshot rd2 (rowsOf (n := r) { family := .liveSpo })
  SnapshotStore.endRead rd2
  pure (all [expectEq "old reader" (eids old) [1], expectEq "new reader" (eids new) [1, 2]])

def uncommittedInvisible : m Outcome := do
  WriteStore.begin
  WriteStore.insertTriple (row 1 1 1 1 1)
  let rd ← SnapshotStore.beginRead (m := m)
  let seen ← SnapshotStore.withSnapshot rd (rowsOf (n := r) { family := .liveSpo })
  let own ← rowsOf (n := m) { family := .liveSpo }
  SnapshotStore.endRead rd
  WriteStore.commit
  pure (all [expectEq "reader" seen [], expectEq "writer sees its own write" (eids own) [1]])

def twoReaders : m Outcome := do
  let r1 ← SnapshotStore.beginRead (m := m)
  seed [row 1 1 1 1 1]
  let r2 ← SnapshotStore.beginRead (m := m)
  seed [row 2 2 2 2 2]
  let a ← SnapshotStore.withSnapshot r1 (rowsOf (n := r) { family := .liveSpo })
  let b ← SnapshotStore.withSnapshot r2 (rowsOf (n := r) { family := .liveSpo })
  SnapshotStore.endRead r1
  SnapshotStore.endRead r2
  pure (all [expectEq "first reader" (eids a) [], expectEq "second reader" (eids b) [1]])

/-- Every generic scenario. -/
def scenarios : List (String × m Outcome) := [
  ("signed comparison", signedOrder), ("history newest first", historyNewestFirst),
  ("absent sorts first", absentFirst), ("seek with a lower bound", seekLowerBound),
  ("early stop", earlyStop), ("invalid scans", invalidScans),
  ("retracted between", retractedBetween), ("half-open valid interval", halfOpenValid),
  ("point reads", pointReads), ("reused statement id", reusedId),
  ("numeric normalization", numericNormalization), ("term and tx violations", termViolations),
  ("retract a live row", retractLive), ("retract twice", retractTwice),
  ("volatile upsert", volatileUpsert), ("failed write inside a transaction", failedWriteInTx),
  ("rollback to savepoint", rollbackToSavepoint), ("rollback restores", rollbackRestores),
  ("write without a transaction", writeWithoutTx), ("misuse", misuse),
  ("commit after a reader began", snapshotAfterCommit),
  ("uncommitted writes invisible", uncommittedInvisible), ("independent readers", twoReaders)]

end Generic

/-- Runs every scenario on a fresh store from `fresh`. -/
def runAll {m : Type → Type} (label : String) (scs : List (String × m Outcome))
    (fresh : String → m Outcome → IO (Except StoreError Outcome)) : TestM Unit := do
  for (name, sc) in scs do
    match ← fresh name sc with
    | .ok none => check s!"{label}: {name}" true
    | .ok (some d) => check s!"{label}: {name}" false d
    | .error e => check s!"{label}: {name}" false s!"store error {e}"

def onModel (_ : String) (x : ModelM Outcome) : IO (Except StoreError Outcome) :=
  pure ((x.run {}).map Prod.fst)

def onSqlite (name : String) (x : SqliteM Outcome) : IO (Except StoreError Outcome) := do
  let p ← freshFormat1 ("contract-" ++ name.replace " " "-")
  match ← (Store.open p).run with
  | .error e => pure (.error e)
  | .ok st =>
    let res ← (x st).run
    st.close
    pure res

/-! ## SQLite-only scenarios -/

def sqliteOnly : TestM Unit := do
  -- close during a write transaction, then reopen: only committed writes are present
  let p ← freshFormat1 "contract-close-in-tx"
  let r ← (do
    let st ← Store.open p
    seed (m := SqliteM) [row 1 1 1 1 1] st
    (WriteStore.begin : SqliteM Unit) st
    (WriteStore.insertTriple (row 2 2 2 2 2) : SqliteM Unit) st
    st.close
    let st2 ← Store.open p
    (WriteStore.begin : SqliteM Unit) st2   -- the old connection no longer holds the lock
    (WriteStore.rollback : SqliteM Unit) st2
    let xs ← (rowsOf { family := .logAdd, view := { tx := .history } } : SqliteM _) st2
    st2.close
    pure (eids xs) : SqlM _).run
  check "sqlite: close during a transaction" (match r with | .ok [1] => true | _ => false) (reprStr r)
  -- readers cannot write
  let p ← freshFormat1 "contract-reader-write"
  let r ← (do
    let rd ← openReader p
    let e ← tryCatch (do rd.run "INSERT INTO tx(t, instant) VALUES (1, 1)"; pure none)
      (fun e => pure (some e))
    rd.clearCache
    let c ← openReader p
    let n ← c.queryOne "SELECT count(*) FROM tx" #[] (colInt! · 0)
    c.clearCache
    pure (e, n) : SqlM _).run
  check "sqlite: readers cannot write" (match r with
    | .ok (some (.sqlite 8 _ _), some 0) => true   -- SQLITE_READONLY
    | _ => false) (reprStr r)
  -- a trigger abort carries the constraint code and the trigger's message
  let p ← freshFormat1 "contract-trigger"
  let r ← (do
    let st ← Store.open p
    seed (m := SqliteM) [row 1 1 1 1 1] st
    let c ← st.conn
    let e ← tryCatch (do c.run "DELETE FROM triple WHERE eid = 1"; pure none) (fun e => pure (some e))
    let still ← tripleOn c 1
    st.close
    pure (e, still.isSome) : SqlM _).run
  check "sqlite: trigger abort on delete" (match r with
    | .ok (some (.sqlite 19 1811 msg), true) => (msg.splitOn "never deleted").length > 1
    | _ => false) (reprStr r)
  -- a busy database: begin fails with the busy code while another writer holds the lock
  let p ← freshFormat1 "contract-busy"
  let r ← (do
    let other ← openWriter p
    other.beginImmediate
    let st ← Store.open p { busyTimeoutMs := 50 }
    let e ← tryCatch (do (WriteStore.begin : SqliteM Unit) st; pure none) (fun e => pure (some e))
    let inTx := (← st.txState.get).inTx
    other.rollback
    other.clearCache
    st.close
    pure (e, inTx) : SqlM _).run
  check "sqlite: busy error carries the busy code" (match r with
    | .ok (some (.sqlite 5 _ _), false) => true
    | _ => false) (reprStr r)
  -- a storage error inside a write transaction rolls the transaction back
  let p ← freshFormat1 "contract-storage-error"
  let r ← (do
    let st ← Store.open p
    seed (m := SqliteM) [row 1 1 1 1 1] st
    let c ← st.conn
    let pages ← c.queryOne "SELECT page_count FROM pragma_page_count" #[] (colInt! · 0)
    c.exec s!"PRAGMA max_page_count = {(pages.getD 1) + 1}"
    (WriteStore.begin : SqliteM Unit) st
    (WriteStore.insertTriple (row 2 2 2 2 2) : SqliteM Unit) st
    let big := String.ofList (List.replicate 100000 'x')
    let e ← tryCatch (do
        for i in [0:50] do
          (WriteStore.insertTerm { id := (i + 1).toInt64, tag := 1, lex := big ++ toString i } :
            SqliteM Unit) st
        pure none) (fun e => pure (some e))
    let ts ← st.txState.get
    let xs ← (rowsOf { family := .logAdd, view := { tx := .history } } : SqliteM _) st
    st.close
    pure (e, ts.inTx, eids xs) : SqlM _).run
  check "sqlite: storage error rolls the transaction back" (match r with
    | .ok (some (.sqlite 13 _ _), false, [1]) => true   -- SQLITE_FULL
    | _ => false) (reprStr r)

def main (_ : List String) : IO UInt32 := do
  let run : TestM Unit := do
    runAll "model" (scenarios (m := ModelM)) onModel
    runAll "sqlite" (scenarios (m := SqliteM)) onSqlite
    sqliteOnly
  let ((), rep) ← run.run {}
  finish "contract" rep

end Test.Contract
