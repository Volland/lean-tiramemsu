/-
The Lean side of the oracle driver protocol: one JSON request per line on stdin, one JSON
response per line on stdout. Requests are `{"id": n, "op": name, "args": {...}}`; responses
are `{"id": n, "ok": result}` or `{"id": n, "err": {"code": c, "message": m}}`.
M0 implements `open`, `close`, `rawDump` and `sqlPrepare`; every other operation answers
`Unsupported` until the milestone that owns it. Shell module (unverified).
-/
import Tiramemsu.Sqlite.Store
import Tiramemsu.Shell.Json

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.Sqlite Tiramemsu.Store

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
      match ← run (Store.open path) with
      | .ok st => cur.set (some st); pure (.ok .null)
      | .error e => pure (.error e)
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
