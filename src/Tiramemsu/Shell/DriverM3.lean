/-
The M3 operations of the Lean oracle driver, mirrored by the Rust driver's `m3.rs`:
`m3.open` (`path`, `options`), `m3.close`, `m3.execute` (`query`, `params`, `view`), `m3.path`
(`start`, `text`, `mode`, `maxHops`, `graphs`, `timeRespecting`, `view`), `m3.bundle` (`root`,
`view`), `m3.importBundle` (`json`) and `m3.sortKey` (`values`). Values use the one-key form;
path rows report raw ids. Shell module (unverified; oracle tooling).
-/
import Tiramemsu.Api.Api
import Tiramemsu.Shell.IrJson

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.IR Tiramemsu.Codec Tiramemsu.Api

--# @lat: [[query#Differential Query Oracle]]

def m3Err (code msg : String) : Json := .obj #[("code", .str code), ("message", .str msg)]

def apiErrJ (e : ApiError) : Json := m3Err e.code e.message

def viewOf (db : Api.Db) (args : Json) : Except Json Api.View :=
  match args.get? "view" with
  | none | some .null => .ok db.now
  | some j => match irViewOfJ j with
    | .ok spec => .ok { db, spec }
    | .error m => .error (m3Err "InvalidArgument" m)

def hexBytes (bs : List UInt8) : String :=
  let d := "0123456789abcdef".toList
  String.ofList (bs.flatMap fun b => [d.getD (b.toNat / 16) '0', d.getD (b.toNat % 16) '0'])

def cellJ : Option Value → Json
  | some v => valueJ v
  | none => .null

def pathRowJ (r : Path.PathRow) : Json :=
  .obj (#[("start", .int r.start.toInt), ("end", .int r.end.toInt), ("hops", .int r.hops)] ++
    (match r.path with
     | some p => #[("path", .obj #[("nodes", .arr (p.nodes.map fun n => Json.int n.toInt).toArray),
        ("hops", .arr (p.hops.map fun h => Json.obj #[("eid", .int h.eid.toInt), ("pred", .int h.pred.toInt),
          ("dir", .str (if h.dir == .out then "out" else "in")), ("kind", .int h.kind)]).toArray)])]
     | none => #[]) ++
    (match r.arrival with | some a => #[("arrival", .int a)] | none => #[]))

def m3Lift {α : Type} (x : Except ApiError α) : Except Json α := x.mapError apiErrJ

def handleM3 (cur : IO.Ref (Option Api.Db)) (op : String) (args : Json) : IO (Except Json Json) := do
  match op with
  | "m3.open" =>
    if let some d ← cur.get then d.close
    cur.set none
    let some path := args.getStr? "path" | return .error (m3Err "InvalidArgument" "`path` is required")
    let states := ((args.get? "options").bind (·.getInt? "pathMaxStates")).map Int.toNat |>.getD 1000000
    match ← Api.Db.open path { pathMaxStates := states } with
    | .ok d => cur.set (some d); return .ok .null
    | .error e => return .error (apiErrJ e)
  | "m3.close" =>
    if let some d ← cur.get then d.close
    cur.set none
    return .ok .null
  | "m3.sortKey" =>
    let vs := (args.getArr? "values").getD #[]
    return .ok (.arr (vs.map fun j => match valueOfJ? j with
      | some v => Json.str (hexBytes (Sem.sortKey v))
      | none => Json.null))
  | _ =>
    let some db ← cur.get | return .error (m3Err "InvalidArgument" "no m3 database is open")
    match viewOf db args with
    | .error e => return .error e
    | .ok v =>
    match op with
    | "m3.execute" =>
      let some qj := args.get? "query" | return .error (m3Err "InvalidArgument" "`query` is required")
      match irQueryOfJ qj with
      | .error m => return .error (m3Err "InvalidArgument" m)
      | .ok q =>
        let ps : Params := ((args.getArr? "params").getD #[]).toList.filterMap fun p => match p with
          | .arr #[.str n, x] => (valueOfJ? x).map (n, ·)
          | _ => none
        match ← v.execute q ps with
        | .ok res => return .ok (.obj #[("columns", .arr (res.columns.map Json.str).toArray),
            ("rows", .arr (res.rows.map fun r => Json.arr (r.map cellJ).toArray).toArray)])
        | .error e => return .error (apiErrJ e)
    | "m3.path" =>
      let some sj := args.get? "start" | return .error (m3Err "InvalidArgument" "`start` is required")
      let some sv := valueOfJ? sj | return .error (m3Err "InvalidArgument" "bad start")
      let text := (args.getStr? "text").getD ""
      let some mode := PathMode.parse? ((args.getStr? "mode").getD "REACH")
        | return .error (m3Err "Unsupported" "path mode")
      match ← v.encode sv with
      | .error e => return .error (apiErrJ e)
      | .ok none => return .ok (.arr #[])
      | .ok (some s) =>
        let graphs ← match args.getArr? "graphs" with
          | none => pure none
          | some gs => do
            let ids ← gs.toList.filterMapM fun g => do
              match valueOfJ? g with
              | some gv => match ← v.encode gv with
                | .ok x => pure x
                | .error _ => pure none
              | none => pure none
            pure (some ids)
        let timed := match args.get? "timeRespecting" with
          | some (.obj kvs) => some ((Json.obj kvs).getInt? "after" |>.map Int64.ofInt)
          | _ => none
        let maxHops := (args.getInt? "maxHops").map Int.toNat
        match ← v.pathWith s text { mode, maxHops, graphs, timeRespecting := timed } with
        | .ok rows => return .ok (.arr (rows.map pathRowJ).toArray)
        | .error e => return .error (apiErrJ e)
    | "m3.bundle" =>
      let some n := args.getInt? "root" | return .error (m3Err "InvalidArgument" "`root` is required")
      match ← v.bundle (mkAlloc .stmt 0 n.toNat.toUInt64) with
      | .ok b => return .ok (.obj #[("json", .str b.toJson)])
      | .error e => return .error (apiErrJ e)
    | "m3.importBundle" =>
      let some text := args.getStr? "json" | return .error (m3Err "InvalidArgument" "`json` is required")
      match Bundle.Bundle.fromJson text with
      | .error e => return .error (m3Err e.code (toString e))
      | .ok b =>
        match ← db.transact (Tx.importBundle b) with
        | .ok (rep, _) => return .ok (.obj #[("root", .int rep.root.raw.toInt),
            ("statements", .arr (rep.statements.map fun s => Json.arr #[.int s.local_, .int s.eid.raw.toInt, .bool s.new]).toArray)])
        | .error e => return .error (apiErrJ e)
    | other => return .error (m3Err "Unsupported" s!"operation {other} is not implemented")

end Tiramemsu.Shell
