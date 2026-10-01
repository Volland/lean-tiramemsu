//! M2 operations: the JSON bridge's transaction, speculation and read operations on a
//! database opened with a manual clock, so that instants (and as-of-instant views) are
//! deterministic and equal between the builds.
//!
//! The bridge (`tiramemsu-json`) opens with the system clock and keeps its `Db` private, so
//! these operations repeat its `transact`/`with`/read code on a `Db` of their own (the JSON
//! forms are the bridge's: `tiramemsu_json::value`), and add the volatile and blank-node
//! verbs the bridge does not expose.
//!
//! Operations: `m2.open` (`path`, `clock`), `m2.close`, `m2.setClock` (`ms`),
//! `m2.transact` (`ops`, `options`), `m2.with` (`ops`, `queries`, `validAt`), `m2.read`
//! (`op`, `view`, ... as a bridge read).

use std::collections::HashMap;
use std::sync::Arc;

use serde_json::{json, Value as J};
use tiramemsu::{
    AssertOpts, Asserted, Db, Eid, Error, Event, ManualClock, ObjectId, OnExisting, Op, OpenOptions,
    Patch, PatchField, TimeRef, Triple, Tx, TxReport, Valid, View,
};
use tiramemsu_json::value::{eid_from_json, time_from_json, value_from_json, value_to_json};
use tiramemsu_json::BindError;

pub struct M2 {
    pub db: Db,
    pub clock: Arc<ManualClock>,
}

fn arg(msg: impl Into<String>) -> J {
    json!({ "code": "InvalidArgument", "message": msg.into() })
}

fn db_err(e: Error) -> J {
    BindError::Db(e).to_json()
}

/// A bridge argument error carried through a transaction body.
#[derive(Debug)]
struct ArgError(String);
impl std::fmt::Display for ArgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ArgError {}

fn targ(msg: impl Into<String>) -> Error {
    Error::custom(ArgError(msg.into()))
}

fn to_core(e: J) -> Error {
    targ(e["message"].as_str().unwrap_or("").to_string())
}

fn from_core(e: Error) -> J {
    if let Error::Custom(inner) = &e {
        if let Some(a) = inner.downcast_ref::<ArgError>() {
            return arg(a.0.clone());
        }
    }
    db_err(e)
}

type Res<T> = Result<T, J>;

pub fn open(args: &J) -> Res<M2> {
    let path = args
        .get("path")
        .and_then(J::as_str)
        .ok_or_else(|| arg("`path` is required"))?;
    let ms = args.get("clock").and_then(J::as_i64).unwrap_or(0);
    let clock = Arc::new(ManualClock::new(ms));
    let opts = OpenOptions {
        clock: clock.clone(),
        ..OpenOptions::default()
    };
    let db = Db::open(path, opts).map_err(db_err)?;
    Ok(M2 { db, clock })
}

pub fn handle(m: &M2, op: &str, args: &J) -> Res<J> {
    match op {
        "m2.setClock" => {
            let ms = args
                .get("ms")
                .and_then(J::as_i64)
                .ok_or_else(|| arg("`ms` is required"))?;
            m.clock.set(ms);
            Ok(J::Null)
        }
        "m2.transact" => transact(&m.db, args),
        "m2.with" => with(&m.db, args),
        "m2.read" => {
            let view = view_from_json(&m.db, args.get("view").unwrap_or(&J::Null))?;
            let op = args
                .get("op")
                .and_then(J::as_str)
                .ok_or_else(|| arg("`op` is required"))?;
            run(&view, op, args)
        }
        other => Err(arg(format!("unknown operation {other:?}"))),
    }
}

fn tx_options(j: &J) -> Res<tiramemsu::TxOptions> {
    let mut o = tiramemsu::TxOptions::default();
    if let Some(m) = j.as_object() {
        for (k, v) in m {
            match k.as_str() {
                "dryRun" => o.dry_run = v.as_bool().ok_or_else(|| arg("dryRun must be a boolean"))?,
                "maxCascade" => {
                    o.max_cascade = v.as_u64().ok_or_else(|| arg("maxCascade must be an integer"))? as usize
                }
                other => return Err(arg(format!("unknown transaction option {other:?}"))),
            }
        }
    }
    Ok(o)
}

fn transact(db: &Db, args: &J) -> Res<J> {
    let ops = args
        .get("ops")
        .and_then(J::as_array)
        .ok_or_else(|| arg("`ops` must be a list"))?;
    let options = tx_options(args.get("options").unwrap_or(&J::Null))?;
    let mut results = Vec::new();
    let report = db
        .transact(options, |tx| {
            results = apply(tx, ops)?;
            Ok(())
        })
        .map_err(from_core)?;
    let mut out = report_json(&report);
    out["results"] = J::Array(results);
    Ok(out)
}

fn with(db: &Db, args: &J) -> Res<J> {
    let ops = args
        .get("ops")
        .and_then(J::as_array)
        .ok_or_else(|| arg("`ops` must be a list"))?;
    let queries = args
        .get("queries")
        .and_then(J::as_array)
        .ok_or_else(|| arg("`queries` must be a list"))?;
    let valid_at = match args.get("validAt") {
        None | Some(J::Null) => None,
        Some(v) => time_from_json(v).map_err(|e| arg(e.to_string()))?,
    };
    let results = db
        .with(
            |tx| apply(tx, ops).map(|_| ()),
            |view| {
                let view = match valid_at {
                    Some(d) => view.clone().valid_at(d),
                    None => view.clone(),
                };
                queries
                    .iter()
                    .map(|q| {
                        let op = q.get("op").and_then(J::as_str).ok_or_else(|| arg("a query needs an `op`"))?;
                        run(&view, op, q)
                    })
                    .collect::<Res<Vec<_>>>()
                    .map_err(to_core)
            },
        )
        .map_err(from_core)?;
    Ok(json!({ "results": results }))
}

type TRes<T> = Result<T, Error>;

fn valid(op: &J) -> TRes<Valid> {
    let bound = |k: &str| op.get(k).map_or(Ok(None), |v| time_from_json(v).map_err(|e| targ(e.to_string())));
    Ok(Valid {
        from: bound("validFrom")?,
        to: bound("validTo")?,
    })
}

fn value(j: &J) -> TRes<tiramemsu::Value> {
    value_from_json(j).map_err(|e| targ(e.to_string()))
}

fn eid_of(j: &J) -> TRes<Eid> {
    eid_from_json(j, &HashMap::new()).map_err(|e| targ(e.to_string()))
}

fn term(tx: &mut Tx<'_>, op: &J, key: &str) -> TRes<ObjectId> {
    let j = op.get(key).ok_or_else(|| targ(format!("`{key}` is required")))?;
    tx.encode(value(j)?)
}

fn pattern(tx: &mut Tx<'_>, op: &J, key: &str) -> TRes<Option<Option<ObjectId>>> {
    match op.get(key) {
        None | Some(J::Null) => Ok(Some(None)),
        Some(j) => Ok(tx.lookup(&value(j)?)?.map(Some)),
    }
}

fn eid(op: &J, key: &str) -> TRes<Eid> {
    eid_of(op.get(key).ok_or_else(|| targ(format!("`{key}` is required")))?)
}

fn assert_opts(op: &J) -> TRes<AssertOpts> {
    let on_existing = match op.get("onExisting").and_then(J::as_str).unwrap_or("return") {
        "return" => OnExisting::Return,
        "confirm" => OnExisting::Confirm,
        other => return Err(targ(format!("unknown onExisting {other:?}"))),
    };
    Ok(AssertOpts {
        valid: valid(op)?,
        on_existing,
    })
}

fn patch(j: &J) -> TRes<Patch> {
    let obj = j.as_object().ok_or_else(|| targ("`patch` must be an object"))?;
    let mut fields = Vec::new();
    for (k, v) in obj {
        let name = match k.as_str() {
            "o" => "o",
            "validFrom" => "v_from",
            "validTo" => "v_to",
            other => other,
        };
        let field = if name == "v_from" || name == "v_to" {
            PatchField::Time(time_from_json(v).map_err(|e| targ(e.to_string()))?)
        } else {
            PatchField::Value(value(v)?)
        };
        fields.push((name, field));
    }
    Patch::from_fields(fields)
}

fn id_json(tx: &mut Tx<'_>, id: ObjectId) -> TRes<J> {
    Ok(value_to_json(&tx.decode(id)?))
}

fn apply(tx: &mut Tx<'_>, ops: &[J]) -> TRes<Vec<J>> {
    let mut results = Vec::with_capacity(ops.len());
    for op in ops {
        let name = op.get("op").and_then(J::as_str).ok_or_else(|| targ("an operation needs an `op`"))?;
        let result = match name {
            "assert" => {
                let (s, p, o) = (term(tx, op, "s")?, term(tx, op, "p")?, term(tx, op, "o")?);
                let a = tx.assert_with(s, p, o, assert_opts(op)?)?;
                json!({ "eid": a.eid().n(), "new": matches!(a, Asserted::New(_)) })
            }
            "create" => {
                let (s, p, o) = (term(tx, op, "s")?, term(tx, op, "p")?, term(tx, op, "o")?);
                let e = tx.create(s, p, o, valid(op)?)?;
                json!({ "eid": e.n(), "new": true })
            }
            "retract" => json!(tx.retract(eid(op, "eid")?)?),
            "retractMatching" => {
                let (s, p, o) = (pattern(tx, op, "s")?, pattern(tx, op, "p")?, pattern(tx, op, "o")?);
                match (s, p, o) {
                    (Some(s), Some(p), Some(o)) => json!(tx
                        .retract_matching(s, p, o)
                        ?
                        .iter()
                        .map(|e| e.n())
                        .collect::<Vec<_>>()),
                    _ => json!([]),
                }
            }
            "supersede" => {
                let root = eid(op, "eid")?;
                let p = patch(op.get("patch").ok_or_else(|| targ("`patch` is required"))?)?;
                json!({ "eid": tx.supersede(root, p)?.n() })
            }
            "confirm" => json!({ "eid": tx.confirm(eid(op, "eid")?)?.n() }),
            "meta" => {
                let (p, o) = (term(tx, op, "p")?, term(tx, op, "o")?);
                json!({ "eid": tx.meta(p, o)?.n() })
            }
            "upsert" => {
                let (p, o) = (term(tx, op, "p")?, term(tx, op, "o")?);
                let id = tx.upsert(p, o)?;
                id_json(tx, id)?
            }
            "newNode" => {
                let id = tx.new_node()?;
                id_json(tx, id)?
            }
            "newBNode" => {
                let id = tx.new_bnode()?;
                id_json(tx, id)?
            }
            "setVolatile" => {
                let (s, k, v) = (term(tx, op, "s")?, term(tx, op, "key")?, term(tx, op, "value")?);
                tx.set_volatile(s, k, v)?;
                J::Null
            }
            "clearVolatile" => {
                let (s, k) = (term(tx, op, "s")?, term(tx, op, "key")?);
                tx.clear_volatile(s, k)?;
                J::Null
            }
            "addToGraph" => {
                let e = eid(op, "eid")?;
                let g = term(tx, op, "graph")?;
                let (m, added) = tx.add_to_graph(e, g, assert_opts(op)?)?;
                json!({ "eid": m.n(), "new": added })
            }
            "removeFromGraph" => {
                let e = eid(op, "eid")?;
                let g = term(tx, op, "graph")?;
                json!(tx.remove_from_graph(e, g)?)
            }
            "clearGraph" => {
                let g = term(tx, op, "graph")?;
                json!(tx.clear_graph(g)?.iter().map(|e| e.n()).collect::<Vec<_>>())
            }
            "createGraph" => {
                let g = term(tx, op, "graph")?;
                json!({ "eid": tx.create_graph(g)?.eid().n() })
            }
            "dropGraph" => {
                let g = term(tx, op, "graph")?;
                json!(tx.drop_graph(g)?.iter().map(|e| e.n()).collect::<Vec<_>>())
            }
            "fail" => return Err(Error::custom("body aborted")),
            other => return Err(targ(format!("unknown transaction operation {other:?}"))),
        };
        results.push(result);
    }
    Ok(results)
}

fn view_from_json<'a>(db: &'a Db, j: &J) -> Res<View<'a>> {
    let get = |k: &str| j.get(k).filter(|v| !v.is_null());
    let kind = j.get("kind").and_then(J::as_str).unwrap_or("now");
    let view = match kind {
        "now" => db.now(),
        "history" => db.history(),
        "asOf" => match (get("tx"), get("instant")) {
            (Some(t), None) => db.as_of(TimeRef::Tx(t.as_u64().ok_or_else(|| arg("tx must be a non-negative integer"))?)),
            (None, Some(i)) => db.as_of(TimeRef::Instant(
                time_from_json(i).map_err(|e| arg(e.to_string()))?.ok_or_else(|| arg("a time is required"))?,
            )),
            _ => return Err(arg("an asOf view needs exactly one of tx and instant")),
        },
        other => return Err(arg(format!("unknown view kind {other:?}"))),
    };
    Ok(match get("validAt") {
        Some(v) => view.valid_at(time_from_json(v).map_err(|e| arg(e.to_string()))?.ok_or_else(|| arg("a time is required"))?),
        None => view,
    })
}

enum Lookup {
    Absent,
    Missing,
    Found(ObjectId),
}

fn opt_id(view: &View<'_>, args: &J, key: &str) -> Res<Lookup> {
    match args.get(key) {
        None | Some(J::Null) => Ok(Lookup::Absent),
        Some(j) => Ok(match view.encode(&rvalue(j)?).map_err(db_err)? {
            Some(id) => Lookup::Found(id),
            None => Lookup::Missing,
        }),
    }
}

fn rvalue(j: &J) -> Res<tiramemsu::Value> {
    value_from_json(j).map_err(|e| arg(e.to_string()))
}

fn reid(j: &J) -> Res<Eid> {
    eid_from_json(j, &HashMap::new()).map_err(|e| arg(e.to_string()))
}

fn required_id(view: &View<'_>, args: &J, key: &str) -> Res<Option<ObjectId>> {
    match args.get(key) {
        None | Some(J::Null) => Err(arg(format!("`{key}` is required"))),
        Some(j) => view.encode(&rvalue(j)?).map_err(db_err),
    }
}

fn run(view: &View<'_>, op: &str, args: &J) -> Res<J> {
    match op {
        "triples" => {
            let ids = [opt_id(view, args, "s")?, opt_id(view, args, "p")?, opt_id(view, args, "o")?];
            if ids.iter().any(|i| matches!(i, Lookup::Missing)) {
                return Ok(json!([]));
            }
            let [s, p, o] = ids.map(|l| match l {
                Lookup::Found(i) => Some(i),
                _ => None,
            });
            let rows = view.triples(s, p, o).map_err(db_err)?;
            Ok(J::Array(rows.iter().map(|t| triple_json(view, t)).collect::<Res<_>>()?))
        }
        "events" => {
            let since = args.get("since").and_then(J::as_u64).unwrap_or(0);
            Ok(J::Array(view.events_since(since).map_err(db_err)?.iter().map(event_json).collect()))
        }
        "graphs" => Ok(J::Array(
            view.graphs()
                .map_err(db_err)?
                .into_iter()
                .map(|g| Ok(value_to_json(&view.decode(g).map_err(db_err)?)))
                .collect::<Res<_>>()?,
        )),
        "graphMembers" => match required_id(view, args, "graph")? {
            Some(g) => Ok(json!(view.graph_members(g).map_err(db_err)?.iter().map(|e| e.n()).collect::<Vec<_>>())),
            None => Ok(json!([])),
        },
        "values" => match (required_id(view, args, "s")?, required_id(view, args, "key")?) {
            (Some(s), Some(k)) => Ok(J::Array(
                view.values(s, k)
                    .map_err(db_err)?
                    .into_iter()
                    .map(|o| Ok(value_to_json(&view.decode(o).map_err(db_err)?)))
                    .collect::<Res<_>>()?,
            )),
            _ => Ok(json!([])),
        },
        "dependents" => {
            let e = reid(args.get("eid").filter(|j| !j.is_null()).ok_or_else(|| arg("`eid` is required"))?)?;
            Ok(json!(view.dependents(e).map_err(db_err)?.iter().map(|e| e.n()).collect::<Vec<_>>()))
        }
        other => Err(arg(format!("unknown read operation {other:?}"))),
    }
}

fn ret_kind(k: tiramemsu::RetKind) -> &'static str {
    match k {
        tiramemsu::RetKind::Explicit => "explicit",
        tiramemsu::RetKind::Cascade => "cascade",
        tiramemsu::RetKind::Supersede => "supersede",
        tiramemsu::RetKind::Cardinality => "cardinality",
    }
}

fn triple_json(view: &View<'_>, t: &Triple) -> Res<J> {
    let ms = |o: Option<i64>| o.map_or(J::Null, |v| json!(v));
    Ok(json!({
        "eid": t.eid.n(),
        "s": value_to_json(&view.decode(t.s).map_err(db_err)?),
        "p": value_to_json(&view.decode(t.p).map_err(db_err)?),
        "o": value_to_json(&view.decode(t.o).map_err(db_err)?),
        "tAdd": t.t_add.0,
        "tRet": t.t_ret.map_or(J::Null, |x| json!(x.0)),
        "validFrom": ms(t.v_from),
        "validTo": ms(t.v_to),
        "retKind": t.ret_kind.map_or(J::Null, |k| json!(ret_kind(k))),
    }))
}

fn event_json(e: &Event) -> J {
    json!({
        "t": e.t.0,
        "eid": e.eid.n(),
        "op": if e.op == Op::Assert { "assert" } else { "retract" },
        "kind": e.kind.map_or(J::Null, |k| json!(ret_kind(k))),
    })
}

fn report_json(r: &TxReport) -> J {
    let kinds = |v: &[(Eid, tiramemsu::RetKind)]| {
        v.iter().map(|(e, k)| json!({ "eid": e.n(), "kind": ret_kind(*k) })).collect::<Vec<_>>()
    };
    let ids = |v: &[Eid]| v.iter().map(|e| e.n()).collect::<Vec<_>>();
    json!({
        "t": r.t.0,
        "instant": r.instant,
        "asserted": ids(&r.asserted),
        "existing": ids(&r.existing),
        "retracted": kinds(&r.retracted),
        "superseded": r.superseded.iter().map(|(o, n)| json!({ "old": o.n(), "new": n.n() })).collect::<Vec<_>>(),
        "memberships": ids(&r.memberships),
        "membershipsRetracted": kinds(&r.memberships_retracted),
    })
}
