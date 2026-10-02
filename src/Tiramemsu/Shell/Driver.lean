/-
The Lean side of the oracle driver protocol: one JSON request per line on stdin, one JSON
response per line on stdout. Requests are `{"id": n, "op": name, "args": {...}}`; responses
are `{"id": n, "ok": result}` or `{"id": n, "err": {"code": c, "message": m}}`.
M0 implements `open` (the format-1 open path since M1), `close`, `rawDump` and `sqlPrepare`;
M1 adds `termIntern` (intern values into a file in one transaction) and `decodeFile` (decode
every term row and triple id). Every other operation answers `Unsupported` until the milestone
that owns it. Shell module (unverified).
-/
import Tiramemsu.Sqlite.Store
import Tiramemsu.Shell.Json
import Tiramemsu.Shell.ValueJson
import Tiramemsu.Storage.Open
import Tiramemsu.Term.Cache
import Tiramemsu.Shell.Db
import Tiramemsu.Shell.Bridge
import Tiramemsu.Shell.DriverM3

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.Sqlite Tiramemsu.Store Tiramemsu.Storage Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[verification#Differential Oracle#Driver Protocol]]

def optJ : Option Int64 → Json
  | some v => .int v.toInt
  | none => .null

def tripleJ (r : TripleRow) : Json :=
  .arr #[.int r.eid.toInt, .int r.s.toInt, .int r.p.toInt, .int r.o.toInt, .int r.tAdd.toInt,
    optJ r.tRet, optJ r.vFrom, optJ r.vTo, optJ r.retKind]

def termJ (r : TermRow) : Json :=
  .arr #[.int r.id.toInt, .int r.tag.toInt, .str r.lex, optJ r.dt,
    (match r.lang with | some l => .str l | none => .null),
    (match r.num with | some b => .int b.toNat | none => .null)]

/-- Every row of the six format-1 tables in primary-key order; REAL values as IEEE bits. -/
def rawDump (c : Conn) : SqlM Json := do
  let metaRows ← dumpMeta c
  let terms ← dumpTerms c
  let txs ← dumpTxs c
  let triples ← dumpTriples c
  let vol ← dumpVolatile c
  let pm ← dumpPredMulti c
  pure <| .obj #[
    ("meta", .arr (metaRows.map fun (k, v) => .arr #[.str k, .int v.toInt])),
    ("term", .arr (terms.map termJ)),
    ("tx", .arr (txs.map fun r => .arr #[.int r.t.toInt, .int r.instant.toInt])),
    ("triple", .arr (triples.map tripleJ)),
    ("volatile", .arr (vol.map fun r =>
      .arr #[.int r.s.toInt, .int r.key.toInt, .int r.value.toInt, .int r.updatedAt.toInt])),
    ("pred_multi", .arr (pm.map fun p => .int p.toInt))]

def errJ (code msg : String) : Json := .obj #[("code", .str code), ("message", .str msg)]

def storeErrJ (e : StoreError) : Json :=
  match e with
  | .sqlite c x m => .obj #[("code", .str "Sqlite"), ("message", .str m),
      ("sqlite", .arr #[.int c.toNat, .int x.toNat])]
  | e => errJ "Store" (toString e)

def openErrJ (e : OpenError) : Json := errJ e.code (toString e)

/-- Interns values into a file in one transaction (as the writer does); returns raw ids. -/
def termIntern (path : String) (values : Array Json) : IO (Except Json Json) := do
  match ← openFile path with
  | .error e => pure (.error (openErrJ e))
  | .ok st =>
    let cache ← WriterCache.new none
    let r ← (do
      Store.begin st
      let mut out := #[]
      for v in values do
        match valueOfJ? v with
        | none => out := out.push (errJ "InvalidArgument" "bad value")
        | some v =>
          match ← (intern v : CachedM SqliteM _) cache st with
          | .ok x => out := out.push (.int x.raw.toInt)
          | .error e => out := out.push (codecErrJ e)
      Store.commit st
      pure (Json.arr out) : SqlM Json).run
    st.close
    pure (match r with | .ok j => .ok j | .error e => .error (storeErrJ e))

/-- Decodes every term row and every triple id of a file. -/
def decodeFile (path : String) : IO (Except Json Json) := do
  match ← openFile path with
  | .error e => pure (.error (openErrJ e))
  | .ok st =>
    let cache ← WriterCache.new (some 0)
    let r ← (do
      let c ← st.conn
      let terms ← dumpTerms c
      let triples ← dumpTriples c
      let dec (raw : Int64) : SqlM Json := do
        match ← (decode ⟨raw⟩ : CachedM SqliteM _) cache st with
        | .ok v => pure (valueJ v)
        | .error e => pure (codecErrJ e)
      let mut ts := #[]
      for t in terms do
        ts := ts.push (.arr #[.int t.id.toInt, .int t.tag.toInt, ← dec ((t.id <<< 4) ||| t.tag)])
      let mut tr := #[]
      for t in triples do
        tr := tr.push (.arr #[.int t.eid.toInt, ← dec t.eid, ← dec t.s, ← dec t.p, ← dec t.o])
      pure (Json.obj #[("terms", .arr ts), ("triples", .arr tr)]) : SqlM Json).run
    st.close
    pure (match r with | .ok j => .ok j | .error e => .error (storeErrJ e))

/-- An M2 database: a handle with a manual clock. -/
structure M2 where
  db : Db
  clock : ManualClock

/-- The M2 operations (`m2.open`, `m2.close`, `m2.setClock`, `m2.transact`, `m2.with`,
`m2.read`): the bridge's transaction, speculation and read operations on a database opened with
a manual clock, as the Rust driver's `m2.rs`. -/
def handleM2 (cur : IO.Ref (Option M2)) (op : String) (args : Json) : IO (Except Json Json) := do
  let argErr (m : String) : Except Json Json := .error (errJ "InvalidArgument" m)
  match op with
  | "m2.open" =>
    match args.getStr? "path" with
    | none => pure (argErr "`path` is required")
    | some path =>
      if let some m ← cur.get then m.db.close
      cur.set none
      let clock ← ManualClock.new ((args.getInt? "clock").getD 0)
      match ← Db.open path {} clock.clock with
      | .ok db => cur.set (some { db, clock }); pure (.ok .null)
      | .error e => pure (.error (openErrJ e))
  | "m2.close" =>
    if let some m ← cur.get then m.db.close
    cur.set none
    pure (.ok .null)
  | _ =>
    match ← cur.get with
    | none => pure (argErr "no m2 database is open")
    | some m =>
      match op with
      | "m2.setClock" =>
        match args.getInt? "ms" with
        | some ms => m.clock.set ms; pure (.ok .null)
        | none => pure (argErr "`ms` is required")
      | "m2.transact" =>
        match args.getArr? "ops", txOptionsOf ((args.get? "options").getD .null) with
        | none, _ => pure (argErr "`ops` must be a list")
        | _, .error e => pure (argErr e)
        | some ops, .ok opts =>
          match ← m.db.transact opts (opsProg ops) with
          | .ok (results, r) =>
            match reportJ r with
            | .obj kvs => pure (.ok (.obj (kvs.push ("results", .arr results))))
            | j => pure (.ok j)
          | .error e => pure (.error (errorJ e))
      | "m2.with" =>
        match args.getArr? "ops", args.getArr? "queries" with
        | none, _ => pure (argErr "`ops` must be a list")
        | _, none => pure (argErr "`queries` must be a list")
        | some ops, some qs =>
          let validAt := match args.get? "validAt" with
            | none | some .null => Except.ok none
            | some j => timeOfJ j
          match validAt with
          | .error e => pure (argErr e)
          | .ok d =>
            match ← m.db.speculate (opsProg ops) d (queriesProg qs) with
            | .ok r => pure (.ok (.obj #[("results", r)]))
            | .error e => pure (.error (errorJ e))
      | "m2.read" =>
        match viewOfJ ((args.get? "view").getD .null), args.getStr? "op" with
        | .error e, _ => pure (argErr e)
        | _, none => pure (argErr "`op` is required")
        | .ok v, some rop =>
          m.db.withView v fun pv => do
            match ← pv.run (readProg rop args) with
            | .ok r => pure (.ok r)
            | .error e => pure (.error (errorJ e))
      | other => pure (argErr s!"unknown operation {other.quote}")

/-- `bench` (`op`, `args`, `reps`): repeats a bridge write (`transact`) or read (`triples`,
`values`, `dependents`, `events`, `graphs`, `graphMembers`) on the open file through a database
handle, and reports the elapsed nanoseconds and the last result. Other operations are
`Unsupported` (later milestones). -/
def benchOp (cur : IO.Ref (Option Store)) (m2 : IO.Ref (Option M2)) (args : Json) :
    IO (Except Json Json) := do
  let some inner := args.getStr? "op" | pure (.error (errJ "InvalidArgument" "`op` is required"))
  let a := (args.get? "args").getD .null
  let reps := ((args.getInt? "reps").getD 1).toNat.max 1
  let req : Option (String × Json) := match inner with
    | "transact" => some ("m2.transact", a)
    | "triples" | "values" | "dependents" | "events" | "graphs" | "graphMembers" =>
      some ("m2.read", match a with
        | .obj kvs => .obj (kvs.push ("op", .str inner))
        | _ => .obj #[("op", .str inner)])
    | _ => none
  let some (op, a) := req
    | pure (.error (errJ "Unsupported" s!"operation {inner} is not implemented by this build yet"))
  -- the bench runs on a database handle over the file the raw store has open
  if (← m2.get).isNone then
    match ← cur.get with
    | none => return .error (errJ "InvalidArgument" "no database is open")
    | some st =>
      st.close
      cur.set none
      match ← Db.open st.path with
      | .ok db => m2.set (some { db, clock := ← ManualClock.new 0 })
      | .error e => return .error (openErrJ e)
  let t0 ← IO.monoNanosNow
  let mut last : Except Json Json := .ok .null
  for _ in [0:reps] do
    last ← handleM2 m2 op a
    if let .error _ := last then break
  let ns := (← IO.monoNanosNow) - t0
  match last with
  | .ok r => pure (.ok (.obj #[("elapsedNs", .int ns), ("reps", .int reps), ("result", r)]))
  | .error e => pure (.error e)

/-- Handles one request; the store is the currently open database, if any. -/
def handle (cur : IO.Ref (Option Store)) (op : String) (args : Json) : IO (Except Json Json) := do
  let run {α : Type} (x : SqlM α) : IO (Except Json α) := do
    match ← x.run with
    | .ok a => pure (.ok a)
    | .error e => pure (.error (storeErrJ e))
  match op with
  | "open" =>
    match args.getStr? "path" with
    | none => pure (.error (errJ "InvalidArgument" "`path` is required"))
    | some path =>
      if let some st ← cur.get then st.close
      match ← openFile path with
      | .ok st => cur.set (some st); pure (.ok .null)
      | .error e => pure (.error (openErrJ e))
  | "close" =>
    if let some st ← cur.get then st.close
    cur.set none
    pure (.ok .null)
  | "rawDump" | "sqlPrepare" =>
    match ← cur.get with
    | none => pure (.error (errJ "InvalidArgument" "no database is open"))
    | some st =>
      if op == "rawDump" then run (do rawDump (← st.conn))
      else
        match args.getStr? "sql" with
        | none => pure (.error (errJ "InvalidArgument" "`sql` is required"))
        | some sql => run (do let c ← st.conn; let _ ← lift (c.db.prepare sql); pure (.bool true))
  | "termIntern" =>
    match args.getStr? "path", args.getArr? "values" with
    | some p, some vs => termIntern p vs
    | _, _ => pure (.error (errJ "InvalidArgument" "`path` and `values` are required"))
  | "decodeFile" =>
    match args.getStr? "path" with
    | some p => decodeFile p
    | none => pure (.error (errJ "InvalidArgument" "`path` is required"))
  | other => pure (.error (errJ "Unsupported" s!"operation {other} is not implemented by this build yet"))

/-- The driver loop. -/
partial def driverMain : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let cur ← IO.mkRef (none : Option Store)
  let m2 ← IO.mkRef (none : Option M2)
  let m3 ← IO.mkRef (none : Option Api.Db)
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    let line := (line.trimAsciiEnd).toString
    if line.isEmpty then loop else
    let resp ← match Json.parse line with
      | .error e => pure (Json.obj #[("id", .null), ("err", errJ "InvalidArgument" s!"bad JSON: {e}")])
      | .ok req =>
        let id := (req.get? "id").getD .null
        let op := (req.getStr? "op").getD ""
        let args := (req.get? "args").getD .null
        let res ← if op.startsWith "m3." then handleM3 m3 op args
          else if op.startsWith "m2." then handleM2 m2 op args
          else if op == "bench" then benchOp cur m2 args
          else if op == "rawDump" && (← m2.get).isSome then do
            match ← m2.get with
            | some m => match ← (do rawDump (← m.db.store.conn)).run with
              | .ok j => pure (.ok j)
              | .error e => pure (.error (storeErrJ e))
            | none => pure (.error (errJ "InvalidArgument" "no database is open"))
          else do
            if op == "open" || op == "close" then
              if let some m ← m2.get then m.db.close
              m2.set none
            handle cur op args
        match res with
        | .ok r => pure (Json.obj #[("id", id), ("ok", r)])
        | .error e => pure (Json.obj #[("id", id), ("err", e)])
    stdout.putStrLn resp.compress
    stdout.flush
    loop
  loop
  if let some st ← cur.get then st.close
  if let some m ← m2.get then m.db.close
  if let some d ← m3.get then d.close
  return 0

end Tiramemsu.Shell
