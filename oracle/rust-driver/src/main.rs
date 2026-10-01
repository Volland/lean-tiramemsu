//! Oracle driver for the pinned Rust build.
//!
//! One JSON request per line on stdin: `{"id": n, "op": name, "args": {...}}`; one JSON
//! response per line on stdout: `{"id": n, "ok": result}` or
//! `{"id": n, "err": {"code": c, "message": m}}`.
//!
//! Operations: every operation of the Rust JSON bridge (`Database::call`), plus
//! `open` (`path`, `options`), `close`, `rawDump` (every row of the six format-1 tables in
//! primary-key order, read with plain SQL), `sqlPrepare` (`sql`, run on a connection of the
//! Rust build, which registers its SQL table functions) and `bench` (`op`, `args`, `reps`:
//! repeats a bridge call and reports the elapsed nanoseconds and the last result).
//! The `codec*`, `termIntern` and `decodeFile` operations call `tm-core` directly (see `codec`).

mod codec;
mod m2;

use rusqlite::{Connection, OpenFlags};
use serde_json::{json, Value as J};
use std::io::{BufRead, Write};
use std::time::Instant;
use tiramemsu_json::Database;

struct State {
    path: Option<String>,
    db: Option<Database>,
    m2: Option<m2::M2>,
}

fn err(code: &str, message: impl Into<String>) -> J {
    json!({ "code": code, "message": message.into() })
}

fn int_or_null(v: rusqlite::types::ValueRef<'_>) -> J {
    match v {
        rusqlite::types::ValueRef::Null => J::Null,
        rusqlite::types::ValueRef::Integer(i) => json!(i),
        rusqlite::types::ValueRef::Real(f) => json!(f.to_bits()),
        rusqlite::types::ValueRef::Text(t) => json!(String::from_utf8_lossy(t)),
        rusqlite::types::ValueRef::Blob(b) => json!(b),
    }
}

/// Every row of a table as arrays of column values, REAL values as IEEE bits.
fn table(conn: &Connection, sql: &str) -> Result<J, J> {
    let mut st = conn.prepare(sql).map_err(|e| err("Sqlite", e.to_string()))?;
    let n = st.column_count();
    let rows = st
        .query_map([], |r| {
            Ok(J::Array((0..n).map(|i| int_or_null(r.get_ref(i).unwrap())).collect()))
        })
        .map_err(|e| err("Sqlite", e.to_string()))?;
    let mut out = Vec::new();
    for r in rows {
        out.push(r.map_err(|e| err("Sqlite", e.to_string()))?);
    }
    Ok(J::Array(out))
}

fn raw_dump(path: &str) -> Result<J, J> {
    let conn = Connection::open_with_flags(path, OpenFlags::SQLITE_OPEN_READ_ONLY)
        .map_err(|e| err("Sqlite", e.to_string()))?;
    let pm = table(&conn, "SELECT p FROM pred_multi ORDER BY p")?;
    let pm = J::Array(
        pm.as_array()
            .unwrap()
            .iter()
            .map(|r| r.as_array().unwrap()[0].clone())
            .collect(),
    );
    Ok(json!({
        "meta": table(&conn, "SELECT key, value FROM meta ORDER BY key")?,
        "term": table(&conn, "SELECT id, tag, lex, dt, lang, num FROM term ORDER BY id")?,
        "tx": table(&conn, "SELECT t, instant FROM tx ORDER BY t")?,
        "triple": table(&conn, "SELECT eid, s, p, o, t_add, t_ret, v_from, v_to, ret_kind FROM triple ORDER BY eid")?,
        "volatile": table(&conn, "SELECT s, key, value, updated_at FROM volatile ORDER BY s, key")?,
        "pred_multi": pm,
    }))
}

fn handle(state: &mut State, op: &str, args: &J) -> Result<J, J> {
    if let Some(r) = codec::handle(op, args) {
        return r;
    }
    let need = |state: &State| -> Result<String, J> {
        state
            .path
            .clone()
            .ok_or_else(|| err("InvalidArgument", "no database is open"))
    };
    if let Some(rest) = op.strip_prefix("m2.") {
        return match rest {
            "open" => {
                state.db = None;
                state.m2 = None;
                let m = m2::open(args)?;
                state.path = args.get("path").and_then(J::as_str).map(str::to_string);
                state.m2 = Some(m);
                Ok(J::Null)
            }
            "close" => {
                state.m2 = None;
                state.path = None;
                Ok(J::Null)
            }
            _ => match &state.m2 {
                Some(m) => m2::handle(m, op, args),
                None => Err(err("InvalidArgument", "no m2 database is open")),
            },
        };
    }
    match op {
        "open" => {
            let path = args
                .get("path")
                .and_then(J::as_str)
                .ok_or_else(|| err("InvalidArgument", "`path` is required"))?;
            state.db = None;
            let db = Database::open(path, args.get("options").unwrap_or(&J::Null))
                .map_err(|e| e.to_json())?;
            state.db = Some(db);
            state.path = Some(path.to_string());
            Ok(J::Null)
        }
        "close" => {
            state.db = None;
            state.m2 = None;
            state.path = None;
            Ok(J::Null)
        }
        "rawDump" => raw_dump(&need(state)?),
        "sqlPrepare" => {
            let path = need(state)?;
            let sql = args
                .get("sql")
                .and_then(J::as_str)
                .ok_or_else(|| err("InvalidArgument", "`sql` is required"))?;
            let db = tiramemsu::Db::open(&path, tiramemsu::OpenOptions::default())
                .map_err(|e| err("Sqlite", e.to_string()))?;
            db.read_sql(sql).map_err(|e| err("Sqlite", e.to_string()))?;
            Ok(J::Bool(true))
        }
        "bench" => {
            let db = state
                .db
                .as_ref()
                .ok_or_else(|| err("InvalidArgument", "no database is open"))?;
            let inner = args
                .get("op")
                .and_then(J::as_str)
                .ok_or_else(|| err("InvalidArgument", "`op` is required"))?;
            let a = args.get("args").cloned().unwrap_or(J::Null);
            let reps = args.get("reps").and_then(J::as_u64).unwrap_or(1).max(1);
            let start = Instant::now();
            let mut last = J::Null;
            for _ in 0..reps {
                last = db.call(inner, &a).map_err(|e| e.to_json())?;
            }
            let ns = start.elapsed().as_nanos() as u64;
            Ok(json!({ "elapsedNs": ns, "reps": reps, "result": last }))
        }
        other => {
            let db = state
                .db
                .as_ref()
                .ok_or_else(|| err("InvalidArgument", "no database is open"))?;
            db.call(other, args).map_err(|e| e.to_json())
        }
    }
}

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let mut state = State { path: None, db: None, m2: None };
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        if line.trim().is_empty() {
            continue;
        }
        let resp = match serde_json::from_str::<J>(&line) {
            Err(e) => json!({ "id": J::Null, "err": err("InvalidArgument", format!("bad JSON: {e}")) }),
            Ok(req) => {
                let id = req.get("id").cloned().unwrap_or(J::Null);
                let op = req.get("op").and_then(J::as_str).unwrap_or("").to_string();
                let args = req.get("args").cloned().unwrap_or(J::Null);
                match handle(&mut state, &op, &args) {
                    Ok(r) => json!({ "id": id, "ok": r }),
                    Err(e) => json!({ "id": id, "err": e }),
                }
            }
        };
        writeln!(out, "{resp}").unwrap();
        out.flush().unwrap();
    }
}
