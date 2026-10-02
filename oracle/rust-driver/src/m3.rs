//! M3 operations: the query core of the pinned Rust build on a database file, mirrored by the
//! Lean driver's `Tiramemsu.Shell.DriverM3`.
//!
//! `m3.open` (`path`, `options.pathMaxStates`), `m3.close`, `m3.execute` (`query`, `params`,
//! `view`), `m3.path` (`start`, `text`, `mode`, `maxHops`, `graphs`, `timeRespecting`, `view`),
//! `m3.bundle` (`root`, `view`), `m3.importBundle` (`json`) and `m3.sortKey` (`values`).
//! IR queries come as JSON (see `Tiramemsu.Shell.IrJson`); values use the codec's one-key form.

use std::collections::BTreeMap;

use serde_json::{json, Value as J};
use tiramemsu::ir::{
    Agg, AggFunc, ArithOp, CmpOp, Expr, Func, GraphSel, IrQuery, Key, Op, PathPattern, TermOrVar,
    TriplePattern, Var,
};
use tiramemsu::ir::{GraphSet, MatchMode, Missing, Semantics};
use tiramemsu::{
    BundleFormat, Db, Eid, Error, ObjectId, OpenOptions, PathArgs, PathMode, ResultValue,
    TimeRef, TimeRespecting, TxOptions, TxSel, ValidSel, Value, View,
};

use crate::codec::{value_from_json, value_to_json};

pub struct M3 {
    pub db: Db,
}

type Res<T> = Result<T, J>;

fn arg(msg: impl Into<String>) -> J {
    json!({ "code": "InvalidArgument", "message": msg.into() })
}

fn db_err(e: Error) -> J {
    tiramemsu_json::BindError::Db(e).to_json()
}

pub fn open(args: &J) -> Res<M3> {
    let path = args
        .get("path")
        .and_then(J::as_str)
        .ok_or_else(|| arg("`path` is required"))?;
    let mut opts = OpenOptions::default();
    if let Some(n) = args
        .get("options")
        .and_then(|o| o.get("pathMaxStates"))
        .and_then(J::as_u64)
    {
        opts.path_max_states = n as usize;
    }
    let db = Db::open(path, opts).map_err(db_err)?;
    Ok(M3 { db })
}

fn view_of<'a>(db: &'a Db, j: Option<&J>) -> Res<View<'a>> {
    let Some(j) = j.filter(|j| !j.is_null()) else {
        return Ok(db.now());
    };
    let v = match j.get("tx") {
        None => db.now(),
        Some(J::String(s)) if s == "now" => db.now(),
        Some(J::String(s)) if s == "history" => db.history(),
        Some(t) => {
            if let Some(x) = t.get("asOfTx").and_then(J::as_u64) {
                db.as_of(TimeRef::Tx(x))
            } else if let Some(x) = t.get("asOfInstant").and_then(J::as_i64) {
                db.as_of(TimeRef::Instant(x))
            } else {
                return Err(arg("bad view"));
            }
        }
    };
    Ok(match j.get("validAt").and_then(J::as_i64) {
        Some(d) => v.valid_at(d),
        None => v,
    })
}

fn ir_view(j: Option<&J>) -> Res<tiramemsu::ir::View> {
    let Some(j) = j.filter(|j| !j.is_null()) else {
        return Ok(tiramemsu::ir::View::NOW);
    };
    let tx = match j.get("tx") {
        None => TxSel::Now,
        Some(J::String(s)) if s == "now" => TxSel::Now,
        Some(J::String(s)) if s == "history" => TxSel::History,
        Some(t) => {
            if let Some(x) = t.get("asOfTx").and_then(J::as_u64) {
                TxSel::AsOf(TimeRef::Tx(x))
            } else if let Some(x) = t.get("asOfInstant").and_then(J::as_i64) {
                TxSel::AsOf(TimeRef::Instant(x))
            } else {
                return Err(arg("bad view"));
            }
        }
    };
    let valid = match j.get("validAt").and_then(J::as_i64) {
        Some(d) => ValidSel::At(d),
        None => ValidSel::Unfiltered,
    };
    Ok(tiramemsu::ir::View { tx, valid })
}

fn one(j: &J) -> Res<(&str, &J)> {
    match j.as_object() {
        Some(m) if m.len() == 1 => {
            let (k, v) = m.iter().next().unwrap();
            Ok((k.as_str(), v))
        }
        _ => Err(arg(format!("expected a one-key object, got {j}"))),
    }
}

fn s(j: &J) -> Res<String> {
    j.as_str().map(str::to_string).ok_or_else(|| arg(format!("expected a string, got {j}")))
}

fn term(j: &J) -> Res<TermOrVar> {
    let (k, v) = one(j)?;
    Ok(match k {
        "var" => TermOrVar::Var(Var::new(s(v)?)),
        "const" => TermOrVar::Const(value_from_json(v)?),
        "id" => TermOrVar::Id(ObjectId::from_raw(v.as_i64().ok_or_else(|| arg("bad id"))?)),
        "param" => TermOrVar::Param(s(v)?),
        other => return Err(arg(format!("bad term {other}"))),
    })
}

fn graph(j: Option<&J>) -> Res<GraphSel> {
    match j {
        None => Ok(GraphSel::Any),
        Some(J::String(a)) if a == "any" => Ok(GraphSel::Any),
        Some(j) => {
            let (k, v) = one(j)?;
            match k {
                "set" => Ok(GraphSel::Set(
                    v.as_array().ok_or_else(|| arg("bad set"))?.iter().map(term).collect::<Res<_>>()?,
                )),
                "var" => Ok(GraphSel::Var(Var::new(s(v)?))),
                other => Err(arg(format!("bad graph {other}"))),
            }
        }
    }
}

const FUNCS: [Func; 43] = [
    Func::Str, Func::Lang, Func::Datatype, Func::IsIri, Func::IsLiteral, Func::IsNumeric, Func::StrLen,
    Func::UCase, Func::LCase, Func::Contains, Func::StrStarts, Func::StrEnds, Func::Regex, Func::IsBlank,
    Func::LangMatches, Func::Iri, Func::StrDt, Func::StrLang, Func::Substr, Func::StrBefore, Func::StrAfter,
    Func::Concat, Func::EncodeForUri, Func::Replace, Func::Abs, Func::Ceil, Func::Floor, Func::Round,
    Func::Year, Func::Month, Func::Day, Func::Hours, Func::Minutes, Func::Seconds, Func::Timezone, Func::Tz,
    Func::CastString, Func::CastInteger, Func::CastDecimal, Func::CastDouble, Func::CastBoolean,
    Func::CastDate, Func::CastDateTime,
];

fn exprs(j: &J) -> Res<Vec<Expr>> {
    j.as_array().ok_or_else(|| arg("expected a list"))?.iter().map(expr).collect()
}

fn expr(j: &J) -> Res<Expr> {
    let (k, v) = one(j)?;
    let a = |i: usize| -> Res<Box<Expr>> { Ok(Box::new(expr(&v[i])?)) };
    Ok(match k {
        "var" => Expr::Var(Var::new(s(v)?)),
        "const" => Expr::Const(value_from_json(v)?),
        "param" => Expr::Param(s(v)?),
        "cmp" => {
            let op = match v[0].as_str().unwrap_or("") {
                "=" => CmpOp::Eq, "!=" => CmpOp::Ne, "<" => CmpOp::Lt, "<=" => CmpOp::Le,
                ">" => CmpOp::Gt, ">=" => CmpOp::Ge, o => return Err(arg(format!("bad cmp {o}"))),
            };
            Expr::Cmp(op, a(1)?, a(2)?)
        }
        "sameTerm" => Expr::SameTerm(a(0)?, a(1)?),
        "and" => Expr::And(exprs(v)?),
        "or" => Expr::Or(exprs(v)?),
        "not" => Expr::Not(Box::new(expr(v)?)),
        "bound" => Expr::Bound(Var::new(s(v)?)),
        "in" => Expr::In(a(0)?, exprs(&v[1])?, v[2].as_bool().unwrap_or(false)),
        "arith" => {
            let op = match v[0].as_str().unwrap_or("") {
                "+" => ArithOp::Add, "-" => ArithOp::Sub, "*" => ArithOp::Mul, "/" => ArithOp::Div,
                o => return Err(arg(format!("bad arith {o}"))),
            };
            Expr::Arith(op, a(1)?, a(2)?)
        }
        "neg" => Expr::Neg(Box::new(expr(v)?)),
        "coalesce" => Expr::Coalesce(exprs(v)?),
        "if" => Expr::If(a(0)?, a(1)?, a(2)?),
        "func" => {
            let n = s(&v[0])?;
            let f = FUNCS.iter().copied().find(|f| f.name() == n).ok_or_else(|| arg(format!("bad func {n}")))?;
            Expr::Func(f, exprs(&v[1])?)
        }
        "exists" => Expr::Exists(Box::new(op(&v[0])?), v[1].as_bool().unwrap_or(false)),
        other => return Err(arg(format!("bad expression {other}"))),
    })
}

fn vars(j: &J) -> Res<Vec<Var>> {
    j.as_array().ok_or_else(|| arg("expected variables"))?.iter().map(|v| Ok(Var::new(s(v)?))).collect()
}

fn op(j: &J) -> Res<Op> {
    let (k, v) = one(j)?;
    let field = |f: &str| v.get(f).ok_or_else(|| arg(format!("missing {f}")));
    let input = || -> Res<Box<Op>> { Ok(Box::new(op(field("input")?)?)) };
    let ops = |x: &J| -> Res<Vec<Op>> { x.as_array().ok_or_else(|| arg("expected a list"))?.iter().map(op).collect() };
    Ok(match k {
        "triple" => Op::Triple(TriplePattern {
            s: term(field("s")?)?,
            p: term(field("p")?)?,
            o: term(field("o")?)?,
            eid: v.get("eid").and_then(J::as_str).map(Var::new),
            view: ir_view(v.get("view"))?,
            iso_group: v.get("group").and_then(J::as_u64).map(|g| g as u32),
            include_volatile: false,
            graph: graph(v.get("graph"))?,
        }),
        "path" => {
            let text = s(field("path")?)?;
            let path = tm_exec::path::syntax::parse(&text, &mut tm_core::Vocab::default()).map_err(db_err)?;
            Op::Path(PathPattern {
                start: term(field("start")?)?,
                end: term(field("end")?)?,
                path,
                mode: v.get("mode").and_then(J::as_str).unwrap_or("REACH").parse::<PathMode>().map_err(arg)?,
                max_hops: v.get("maxHops").and_then(J::as_u64).map(|h| h as u32),
                bind_path: v.get("bind").and_then(J::as_str).map(Var::new),
                view: ir_view(v.get("view"))?,
                graph: graph(v.get("graph"))?,
            })
        }
        "values" => Op::Values(tiramemsu::ir::Values {
            vars: vars(field("vars")?)?,
            rows: field("rows")?
                .as_array()
                .ok_or_else(|| arg("bad rows"))?
                .iter()
                .map(|r| {
                    r.as_array()
                        .ok_or_else(|| arg("bad row"))?
                        .iter()
                        .map(|c| if c.is_null() { Ok(None) } else { term(c).map(Some) })
                        .collect()
                })
                .collect::<Res<_>>()?,
        }),
        "join" => Op::join(ops(v)?),
        "union" => Op::union(ops(v)?),
        "leftJoin" => Op::left_join(
            op(field("l")?)?,
            op(field("r")?)?,
            match v.get("cond") {
                Some(c) => Some(expr(c)?),
                None => None,
            },
        ),
        "filter" => Op::Filter(tiramemsu::ir::Filter { input: input()?, cond: expr(field("cond")?)? }),
        "extend" => Op::Extend(tiramemsu::ir::Extend {
            input: input()?,
            var: Var::new(s(field("var")?)?),
            expr: expr(field("expr")?)?,
        }),
        "aggregate" => Op::Aggregate(tiramemsu::ir::Aggregate {
            input: input()?,
            group: vars(field("group")?)?,
            aggs: field("aggs")?
                .as_array()
                .ok_or_else(|| arg("bad aggs"))?
                .iter()
                .map(|a| {
                    let f = match a.get("func").and_then(J::as_str).unwrap_or("") {
                        "count" => AggFunc::Count, "sum" => AggFunc::Sum, "avg" => AggFunc::Avg,
                        "min" => AggFunc::Min, "max" => AggFunc::Max, "sample" => AggFunc::Sample,
                        "group_concat" => AggFunc::GroupConcat {
                            sep: a.get("sep").and_then(J::as_str).unwrap_or(" ").to_string(),
                        },
                        o => return Err(arg(format!("bad aggregate {o}"))),
                    };
                    Ok(Agg {
                        var: Var::new(s(&a["var"])?),
                        func: f,
                        arg: match a.get("arg") {
                            Some(e) => Some(expr(e)?),
                            None => None,
                        },
                        distinct: a.get("distinct").and_then(J::as_bool).unwrap_or(false),
                    })
                })
                .collect::<Res<_>>()?,
        }),
        "project" => Op::Project(tiramemsu::ir::Project {
            input: input()?,
            vars: vars(field("vars")?)?,
            distinct: v.get("distinct").and_then(J::as_bool).unwrap_or(false),
        }),
        "orderLimit" => Op::OrderLimit(tiramemsu::ir::OrderLimit {
            input: input()?,
            keys: field("keys")?
                .as_array()
                .ok_or_else(|| arg("bad keys"))?
                .iter()
                .map(|k| {
                    Ok(Key {
                        expr: expr(&k["expr"])?,
                        descending: k.get("desc").and_then(J::as_bool).unwrap_or(false),
                    })
                })
                .collect::<Res<_>>()?,
            skip: match v.get("skip") {
                Some(t) => Some(term(t)?),
                None => None,
            },
            limit: match v.get("limit") {
                Some(t) => Some(term(t)?),
                None => None,
            },
        }),
        other => return Err(arg(format!("unknown operator {other}"))),
    })
}

fn semantics(j: Option<&J>) -> Semantics {
    let get = |k: &str| j.and_then(|j| j.get(k)).and_then(J::as_str).unwrap_or("");
    Semantics {
        match_mode: if get("matchMode") == "RelIsomorphism" { MatchMode::RelIsomorphism } else { MatchMode::Homomorphism },
        missing: if get("missing") == "Null3VL" { Missing::Null3VL } else { Missing::Unbound },
        graph_set: if get("graphSet") == "BagOfEids" { GraphSet::BagOfEids } else { GraphSet::SetOfTriples },
    }
}

fn cell(c: &Option<ResultValue>) -> J {
    match c {
        Some(ResultValue::Term(v)) => value_to_json(v),
        Some(_) => json!({ "list": null }),
        None => J::Null,
    }
}

fn hex(bs: &[u8]) -> String {
    bs.iter().map(|b| format!("{b:02x}")).collect()
}

pub fn handle(m: &M3, opn: &str, args: &J) -> Res<J> {
    let db = &m.db;
    match opn {
        "m3.execute" => {
            let qj = args.get("query").ok_or_else(|| arg("`query` is required"))?;
            let root = op(qj.get("root").ok_or_else(|| arg("missing root"))?)?;
            let q = IrQuery::new(root, semantics(qj.get("semantics")));
            let mut ps: BTreeMap<String, Value> = BTreeMap::new();
            if let Some(list) = args.get("params").and_then(J::as_array) {
                for p in list {
                    ps.insert(s(&p[0])?, value_from_json(&p[1])?);
                }
            }
            let v = view_of(db, args.get("view"))?;
            let res = v.execute_ir(&q, &ps).map_err(db_err)?;
            Ok(json!({
                "columns": res.columns.iter().map(|c| c.name().to_string()).collect::<Vec<_>>(),
                "rows": res.rows.iter().map(|r| r.iter().map(cell).collect::<Vec<_>>()).collect::<Vec<_>>(),
            }))
        }
        "m3.path" => {
            let v = view_of(db, args.get("view"))?;
            let start = value_from_json(args.get("start").ok_or_else(|| arg("`start` is required"))?)?;
            let Some(sid) = v.encode(&start).map_err(db_err)? else {
                return Ok(json!([]));
            };
            let mode = args.get("mode").and_then(J::as_str).unwrap_or("REACH").parse::<PathMode>().map_err(arg)?;
            let graphs = match args.get("graphs").and_then(J::as_array) {
                None => None,
                Some(gs) => {
                    let mut ids = Vec::new();
                    for g in gs {
                        if let Some(id) = v.encode(&value_from_json(g)?).map_err(db_err)? {
                            ids.push(id);
                        }
                    }
                    Some(ids)
                }
            };
            let time_respecting = args
                .get("timeRespecting")
                .filter(|t| t.is_object())
                .map(|t| TimeRespecting { after: t.get("after").and_then(J::as_i64) });
            let pa = PathArgs {
                mode,
                max_hops: args.get("maxHops").and_then(J::as_u64).map(|h| h as u32).unwrap_or(u32::MAX),
                graphs,
                time_respecting,
            };
            let text = args.get("text").and_then(J::as_str).unwrap_or("");
            let rows = v.path_with(sid, text, &pa).map_err(db_err)?;
            Ok(J::Array(
                rows.iter()
                    .map(|r| {
                        let mut o = serde_json::Map::new();
                        o.insert("start".into(), json!(r.start.raw()));
                        o.insert("end".into(), json!(r.end.raw()));
                        o.insert("hops".into(), json!(r.hops));
                        if let Some(p) = &r.path {
                            o.insert(
                                "path".into(),
                                json!({
                                    "nodes": p.nodes.iter().map(|n| n.raw()).collect::<Vec<_>>(),
                                    "hops": p.hops.iter().map(|h| json!({
                                        "eid": h.eid.raw(), "pred": h.pred.raw(),
                                        "dir": if h.dir == tiramemsu::PathDir::Out { "out" } else { "in" },
                                        "kind": h.kind as u8,
                                    })).collect::<Vec<_>>(),
                                }),
                            );
                        }
                        if let Some(a) = r.arrival {
                            o.insert("arrival".into(), json!(a));
                        }
                        J::Object(o)
                    })
                    .collect(),
            ))
        }
        "m3.bundle" => {
            let v = view_of(db, args.get("view"))?;
            let n = args.get("root").and_then(J::as_u64).ok_or_else(|| arg("`root` is required"))?;
            let b = v.bundle(Eid::new(n)).map_err(db_err)?;
            Ok(json!({ "json": serde_json::to_string(&b.to_json()).unwrap() }))
        }
        "m3.importBundle" => {
            let text = args.get("json").and_then(J::as_str).ok_or_else(|| arg("`json` is required"))?;
            let j: J = serde_json::from_str(text).map_err(|e| arg(e.to_string()))?;
            let b = tiramemsu::Bundle::from_json(&j).map_err(db_err)?;
            let mut out = None;
            db.transact(TxOptions::default(), |tx| {
                out = Some(tx.import_bundle(&b)?);
                Ok(())
            })
            .map_err(db_err)?;
            let rep = out.unwrap();
            Ok(json!({
                "root": rep.root.oid().raw(),
                "statements": rep.statements.iter().map(|s| json!([s.local, s.eid.oid().raw(), s.new])).collect::<Vec<_>>(),
            }))
        }
        other => Err(arg(format!("unknown operation {other:?}"))),
    }
}

pub fn sort_keys(args: &J) -> Res<J> {
    let vs = args.get("values").and_then(J::as_array).ok_or_else(|| arg("`values` is required"))?;
    Ok(J::Array(
        vs.iter()
            .map(|v| match value_from_json(v) {
                Ok(v) => J::String(hex(&tm_exec::udf::value_key(&v))),
                Err(_) => J::Null,
            })
            .collect(),
    ))
}
