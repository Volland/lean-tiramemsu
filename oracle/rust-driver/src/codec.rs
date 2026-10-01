//! Codec and term-dictionary operations of the oracle driver: they call the pinned `tm-core`
//! functions directly, so the Lean codec can be compared value by value (M1).
//!
//! Values travel as tagged JSON objects, one key per variant:
//! `{"iri": s}`, `{"node": n}`, `{"bnode": n}`, `{"stmt": n}`, `{"tx": n}`, `{"int": i}`,
//! `{"bool": b}`, `{"dateTime": [ms, tz|null]}`, `{"date": d}`, `{"str": s}`,
//! `{"langStr": [lex, lang]}`, `{"typed": [lex, dt]}`, `{"double": bits}`, `{"decimal": s}`.
//! An encoding is `{"inline": raw}` or `{"term": [tag, lex, datatype|null, lang|null, numBits|null]}`;
//! a failure is `{"err": code}`.

use serde_json::{json, Value as J};
use std::path::Path;
use tm_core::codec::{self, Encoded};
use tm_core::storage::{self, meta::Counters};
use tm_core::value::{self, Value};
use tm_core::{Eid, Error, Executor, HostOptions, ObjectId, TermDict, TermReader, TxId};
use tm_rusqlite::RusqliteHost;

fn bad(msg: impl Into<String>) -> J {
    json!({ "code": "InvalidArgument", "message": msg.into() })
}

fn err_code(e: &Error) -> J {
    let code = match e {
        Error::Unsupported { .. } => "Unsupported",
        Error::InvalidTerm { .. } => "InvalidTerm",
        Error::IdSpaceExhausted { .. } => "IdSpaceExhausted",
        _ => "Other",
    };
    json!({ "err": code, "message": e.to_string() })
}

pub fn value_to_json(v: &Value) -> J {
    match v {
        Value::Iri(s) => json!({ "iri": s }),
        Value::Node(n) => json!({ "node": n }),
        Value::BNode(n) => json!({ "bnode": n }),
        Value::Stmt(e) => json!({ "stmt": e.n() }),
        Value::Tx(t) => json!({ "tx": t.0 }),
        Value::Int(i) => json!({ "int": i }),
        Value::Bool(b) => json!({ "bool": b }),
        Value::DateTime { ms, tz } => json!({ "dateTime": [ms, tz] }),
        Value::Date(d) => json!({ "date": d }),
        Value::Str(s) => json!({ "str": s }),
        Value::LangStr { lex, lang } => json!({ "langStr": [lex, lang] }),
        Value::Typed { lex, datatype } => json!({ "typed": [lex, datatype] }),
        Value::Double(x) => json!({ "double": x.to_bits() }),
        Value::Decimal(s) => json!({ "decimal": s }),
    }
}

pub fn value_from_json(j: &J) -> Result<Value, J> {
    let o = j.as_object().ok_or_else(|| bad("a value is an object"))?;
    let (k, v) = o.iter().next().ok_or_else(|| bad("empty value"))?;
    let s = |v: &J| v.as_str().map(str::to_string).ok_or_else(|| bad("expected a string"));
    let u = |v: &J| v.as_u64().ok_or_else(|| bad("expected an unsigned integer"));
    let i = |v: &J| v.as_i64().ok_or_else(|| bad("expected an integer"));
    let pair = |v: &J| -> Result<(J, J), J> {
        let a = v.as_array().ok_or_else(|| bad("expected a pair"))?;
        Ok((a.first().cloned().unwrap_or(J::Null), a.get(1).cloned().unwrap_or(J::Null)))
    };
    Ok(match k.as_str() {
        "iri" => Value::Iri(s(v)?),
        "node" => Value::Node(u(v)?),
        "bnode" => Value::BNode(u(v)?),
        "stmt" => Value::Stmt(Eid::new(u(v)?)),
        "tx" => Value::Tx(TxId(u(v)?)),
        "int" => Value::Int(i(v)?),
        "bool" => Value::Bool(v.as_bool().ok_or_else(|| bad("expected a bool"))?),
        "dateTime" => {
            let (ms, tz) = pair(v)?;
            Value::DateTime {
                ms: i(&ms)?,
                tz: if tz.is_null() { None } else { Some(i(&tz)? as i16) },
            }
        }
        "date" => Value::Date(i(v)?),
        "str" => Value::Str(s(v)?),
        "langStr" => {
            let (a, b) = pair(v)?;
            Value::LangStr { lex: s(&a)?, lang: s(&b)? }
        }
        "typed" => {
            let (a, b) = pair(v)?;
            Value::Typed { lex: s(&a)?, datatype: s(&b)? }
        }
        "double" => Value::Double(f64::from_bits(u(v)?)),
        "decimal" => Value::Decimal(s(v)?),
        other => return Err(bad(format!("unknown value kind {other}"))),
    })
}

/// The encoding of a value on the write path (`encode`, then the origin check).
fn encoded_json(v: &Value) -> J {
    let e = codec::encode(v);
    if let Err(err) = e.check_origin() {
        return err_code(&err);
    }
    match e {
        Encoded::Inline(id) => json!({ "inline": id.raw() }),
        Encoded::Term(t) => json!({ "term": [t.tag as u8, t.lex, t.datatype, t.lang,
            t.num.filter(|x| !x.is_nan()).map(f64::to_bits)] }),
    }
}

fn strs(args: &J, key: &str) -> Result<Vec<String>, J> {
    args.get(key)
        .and_then(J::as_array)
        .ok_or_else(|| bad(format!("`{key}` is required")))?
        .iter()
        .map(|x| x.as_str().map(str::to_string).ok_or_else(|| bad("expected strings")))
        .collect()
}

fn arr<'a>(args: &'a J, key: &str) -> Result<&'a Vec<J>, J> {
    args.get(key)
        .and_then(J::as_array)
        .ok_or_else(|| bad(format!("`{key}` is required")))
}

fn opt_str(j: &J) -> Option<String> {
    j.as_str().map(str::to_string)
}

/// Opens a file with the pinned build's format-1 open path (init or check, then WAL).
fn open_writer(path: &str) -> Result<Box<dyn Executor>, J> {
    let host = RusqliteHost::new();
    storage::open(&host, Path::new(path), &HostOptions::default()).map_err(|e| err_code(&e))
}

/// Interns values into a file in one transaction, as the writer does; returns raw ids.
fn term_intern(path: &str, values: &[J]) -> Result<J, J> {
    let mut exec = open_writer(path)?;
    exec.begin_immediate().map_err(|e| err_code(&e))?;
    let before = Counters::load(exec.as_mut()).map_err(|e| err_code(&e))?;
    let mut dict = TermDict::new(1024);
    dict.begin(before.next_term);
    let mut out = Vec::new();
    for v in values {
        let v = value_from_json(v)?;
        match dict.intern(exec.as_mut(), &v) {
            Ok(id) => out.push(json!(id.raw())),
            Err(e) => out.push(err_code(&e)),
        }
    }
    let after = Counters { next_term: dict.next_term(), ..before };
    after.store(&before, exec.as_mut()).map_err(|e| err_code(&e))?;
    exec.commit().map_err(|e| err_code(&e))?;
    Ok(J::Array(out))
}

/// Decodes every term row and every triple id of a file with the reader-side dictionary.
fn decode_file(path: &str) -> Result<J, J> {
    let mut exec = open_writer(path)?;
    let mut rows: Vec<(i64, i64)> = Vec::new();
    exec.query("SELECT id, tag FROM term ORDER BY id", &[], &mut |r| {
        rows.push((r[0].as_i64().unwrap_or(0), r[1].as_i64().unwrap_or(0)));
        Ok(())
    })
    .map_err(|e| err_code(&e))?;
    let mut triples: Vec<[i64; 4]> = Vec::new();
    exec.query("SELECT eid, s, p, o FROM triple ORDER BY eid", &[], &mut |r| {
        triples.push([
            r[0].as_i64().unwrap_or(0),
            r[1].as_i64().unwrap_or(0),
            r[2].as_i64().unwrap_or(0),
            r[3].as_i64().unwrap_or(0),
        ]);
        Ok(())
    })
    .map_err(|e| err_code(&e))?;
    let reader = TermReader::new(64);
    let mut dec = |raw: i64| -> J {
        match reader.decode(exec.as_mut(), ObjectId::from_raw(raw), false) {
            Ok(v) => value_to_json(&v),
            Err(e) => err_code(&e),
        }
    };
    let terms: Vec<J> = rows
        .iter()
        .map(|(id, tag)| json!([id, tag, dec((id << 4) | tag)]))
        .collect();
    let triples: Vec<J> = triples
        .iter()
        .map(|t| json!([t[0], dec(t[0]), dec(t[1]), dec(t[2]), dec(t[3])]))
        .collect();
    Ok(json!({ "terms": terms, "triples": triples }))
}

/// Handles a codec or dictionary operation; `None` when `op` is not one.
pub fn handle(op: &str, args: &J) -> Option<Result<J, J>> {
    let r = match op {
        "codecPrintDoubles" => (|| {
            let bits = arr(args, "bits")?;
            Ok(J::Array(
                bits.iter()
                    .map(|b| json!(value::canonical_double(f64::from_bits(b.as_u64().unwrap_or(0)))))
                    .collect(),
            ))
        })(),
        "codecParseDoubles" => (|| {
            Ok(J::Array(
                strs(args, "lex")?
                    .iter()
                    .map(|s| match value::parse_double(s) {
                        Some(x) => json!(x.to_bits()),
                        None => J::Null,
                    })
                    .collect(),
            ))
        })(),
        "codecLiterals" => (|| {
            let items = arr(args, "items")?;
            let mut out = Vec::new();
            for it in items {
                let a = it.as_array().ok_or_else(|| bad("an item is [lex, dt, lang]"))?;
                let lex = a.first().and_then(J::as_str).unwrap_or("");
                let dt = a.get(1).and_then(opt_str);
                let lang = a.get(2).and_then(opt_str);
                let v = Value::literal(lex, dt.as_deref(), lang.as_deref());
                out.push(json!({ "value": value_to_json(&v), "enc": encoded_json(&v) }));
            }
            Ok(J::Array(out))
        })(),
        "codecValues" => (|| {
            let vals = arr(args, "values")?;
            let mut out = Vec::new();
            for v in vals {
                let v = value_from_json(v)?;
                let c = v.canonical();
                out.push(json!({
                    "canonical": value_to_json(&c),
                    "enc": encoded_json(&v),
                    "lexical": c.lexical(),
                    "datatype": c.datatype(),
                }));
            }
            Ok(J::Array(out))
        })(),
        "codecDecode" => (|| {
            let ids = arr(args, "ids")?;
            Ok(J::Array(
                ids.iter()
                    .map(|i| match codec::decode_inline(ObjectId::from_raw(i.as_i64().unwrap_or(0))) {
                        Ok(Some(v)) => value_to_json(&v),
                        Ok(None) => J::Null,
                        Err(e) => err_code(&e),
                    })
                    .collect(),
            ))
        })(),
        "codecDates" => (|| {
            Ok(J::Array(
                strs(args, "lex")?.iter().map(|s| json!(value::parse_date(s))).collect(),
            ))
        })(),
        "codecDateTimes" => (|| {
            Ok(J::Array(
                strs(args, "lex")?
                    .iter()
                    .map(|s| match value::parse_datetime(s) {
                        Some((ms, tz)) => json!([ms, tz]),
                        None => J::Null,
                    })
                    .collect(),
            ))
        })(),
        "codecFormatDates" => (|| {
            Ok(J::Array(
                arr(args, "days")?
                    .iter()
                    .map(|d| json!(value::format_date(d.as_i64().unwrap_or(0))))
                    .collect(),
            ))
        })(),
        "codecFormatDateTimes" => (|| {
            let items = arr(args, "items")?;
            Ok(J::Array(
                items
                    .iter()
                    .map(|it| {
                        let ms = it.get(0).and_then(J::as_i64).unwrap_or(0);
                        let tz = it.get(1).and_then(J::as_i64).map(|t| t as i16);
                        json!(value::format_datetime(ms, tz))
                    })
                    .collect(),
            ))
        })(),
        "codecCanonIntegers" => (|| {
            Ok(J::Array(
                strs(args, "lex")?.iter().map(|s| json!(value::canonical_integer(s))).collect(),
            ))
        })(),
        "codecCanonDecimals" => (|| {
            Ok(J::Array(
                strs(args, "lex")?.iter().map(|s| json!(value::canonical_decimal(s))).collect(),
            ))
        })(),
        "codecBench" => (|| {
            // times printing `bits` and parsing `lex` (report-only benchmark, D14)
            let bits: Vec<u64> = arr(args, "bits")?.iter().map(|b| b.as_u64().unwrap_or(0)).collect();
            let lex = strs(args, "lex")?;
            let t0 = std::time::Instant::now();
            let mut n = 0usize;
            for b in &bits {
                n += value::canonical_double(f64::from_bits(*b)).len();
            }
            let print_ns = t0.elapsed().as_nanos() as u64;
            let t1 = std::time::Instant::now();
            for s in &lex {
                n += value::parse_double(s).map(|x| x.to_bits() as usize & 1).unwrap_or(0);
            }
            let parse_ns = t1.elapsed().as_nanos() as u64;
            Ok(json!({ "printNs": print_ns, "parseNs": parse_ns, "check": n }))
        })(),
        "termIntern" => (|| {
            let path = args.get("path").and_then(J::as_str).ok_or_else(|| bad("`path` is required"))?;
            term_intern(path, arr(args, "values")?)
        })(),
        "decodeFile" => (|| {
            let path = args.get("path").and_then(J::as_str).ok_or_else(|| bad("`path` is required"))?;
            decode_file(path)
        })(),
        _ => return None,
    };
    Some(r)
}
