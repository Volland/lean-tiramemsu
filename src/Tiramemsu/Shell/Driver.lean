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
        match ← handle cur op args with
        | .ok r => pure (Json.obj #[("id", id), ("ok", r)])
        | .error e => pure (Json.obj #[("id", id), ("err", e)])
    stdout.putStrLn resp.compress
    stdout.flush
    loop
  loop
  if let some st ← cur.get then st.close
  return 0

end Tiramemsu.Shell
