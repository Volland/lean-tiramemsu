/-
Fixed SQL text: one statement per scan shape (family, prefix length, bound shape, view shape)
with an explicit `ORDER BY` equal to the family key and `INDEXED BY` the family's index, plus
the point reads and writes. Order is guaranteed by the SQL text, not by the plan.
Shell module (unverified).
-/
import Tiramemsu.Store.Order
import Tiramemsu.Sqlite.Conn

namespace Tiramemsu.Sqlite

open Tiramemsu.Store

--# @lat: [[architecture#SQLite Boundary#Scan SQL]]

/-- The selected triple columns, in `TripleRow` field order. -/
def tripleCols : String := "eid, s, p, o, t_add, t_ret, v_from, v_to, ret_kind"

/-- The format-1 index a family mirrors. -/
def _root_.Tiramemsu.Store.Family.indexName : Family → String
  | .liveSpo => "live_spo" | .livePos => "live_pos" | .liveOsp => "live_osp"
  | .histSpo => "hist_spo" | .histPos => "hist_pos" | .histOsp => "hist_osp"
  | .validP => "valid_p" | .logAdd => "log_add" | .logRet => "log_ret"

/-- `ORDER BY` columns of a family (the index key, `eid` last). -/
def _root_.Tiramemsu.Store.Family.orderBy (f : Family) : String :=
  ", ".intercalate (f.cols.map fun (c, d) => if d then c.sqlName ++ " DESC" else c.sqlName)

/-- The SQL of a scan shape and its parameters. The SQL text depends only on the shape. -/
def scanSql (sp : ScanSpec) : String × Array Val := Id.run do
  let f := sp.family
  let cols := f.cols.map Prod.fst
  let mut conds : Array String := #[]
  let mut params : Array Val := #[]
  -- The partial-index predicate as the index states it (the `now` view is the same text, so
  -- the partial indexes qualify). On the full indexes the `now` view is written
  -- `+t_ret IS NULL`: the same predicate, but not an index term, because SQLite stops using
  -- index order after a column constrained by a non-seek `IS NULL` and would add a sort.
  if f == .logRet then
    conds := conds.push "t_ret IS NOT NULL"
  if f.isLive then
    conds := conds.push "t_ret IS NULL"
  else if sp.view.tx == .now then
    conds := conds.push "+t_ret IS NULL"
  for h : i in [0:sp.pre.size] do
    let c := cols[i]?.getD .eid
    conds := conds.push s!"{c.sqlName} = ?"
    params := params.push (.int sp.pre[i])
  let bcol := (sp.boundCol.getD .eid).sqlName
  match sp.lo with
  | some (.incl v) => conds := conds.push s!"{bcol} >= ?"; params := params.push (.int v)
  | some (.excl v) => conds := conds.push s!"{bcol} > ?"; params := params.push (.int v)
  | none => pure ()
  match sp.hi with
  | some (.incl v) => conds := conds.push s!"{bcol} <= ?"; params := params.push (.int v)
  | some (.excl v) => conds := conds.push s!"{bcol} < ?"; params := params.push (.int v)
  | none => pure ()
  match sp.view.tx with
  | .asOf t =>
    conds := conds.push "t_add <= ? AND (t_ret IS NULL OR t_ret > ?)"
    params := params.push (.int t) |>.push (.int t)
  | _ => pure ()
  match sp.view.valid with
  | .at d =>
    conds := conds.push "(v_from IS NULL OR v_from <= ?) AND (v_to IS NULL OR v_to > ?)"
    params := params.push (.int d) |>.push (.int d)
  | .unfiltered => pure ()
  let whereClause := if conds.isEmpty then "" else " WHERE " ++ " AND ".intercalate conds.toList
  -- `INDEXED BY` pins the plan to the family index (which already yields ORDER BY order);
  -- the explicit ORDER BY keeps the order independent of the plan.
  (s!"SELECT {tripleCols} FROM triple INDEXED BY {f.indexName}{whereClause} ORDER BY {f.orderBy}",
    params)

/-! ## Point reads -/

def sqlTriple : String := s!"SELECT {tripleCols} FROM triple WHERE eid = ?"
def sqlTermById : String :=
  "SELECT id, tag, CAST(lex AS BLOB), dt, CAST(lang AS BLOB), num FROM term WHERE id = ?"
/-- Absent datatype or language matches only absent (`IS`); the `ifnull` terms let the
`term_key` index serve the lookup. -/
def sqlTermByKey : String :=
  "SELECT id FROM term WHERE tag = ?1 AND lex = CAST(?2 AS TEXT) " ++
  "AND ifnull(dt, 0) = ifnull(?3, 0) AND ifnull(lang, '') = ifnull(CAST(?4 AS TEXT), '') " ++
  "AND dt IS ?3 AND lang IS CAST(?4 AS TEXT)"
def sqlTxByT : String := "SELECT t, instant FROM tx WHERE t = ?"
def sqlTxAtOrBefore : String :=
  "SELECT t, instant FROM tx WHERE instant <= ? ORDER BY instant DESC LIMIT 1"
def sqlCounter : String := "SELECT value FROM meta WHERE key = CAST(? AS TEXT)"
def sqlVolatileGet : String :=
  "SELECT s, key, value, updated_at FROM volatile WHERE s = ? AND key = ?"
def sqlVolatileOf : String :=
  "SELECT s, key, value, updated_at FROM volatile WHERE s = ? ORDER BY key"
def sqlPredMulti : String := "SELECT 1 FROM pred_multi WHERE p = ?"

/-! ## Writes -/

def sqlInsertTriple : String :=
  s!"INSERT INTO triple({tripleCols}) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)"
def sqlRetract : String :=
  "UPDATE triple SET t_ret = ?, ret_kind = ? WHERE eid = ? AND t_ret IS NULL"
def sqlInsertTerm : String :=
  "INSERT INTO term(id, tag, lex, dt, lang, num) VALUES (?, ?, CAST(? AS TEXT), ?, CAST(? AS TEXT), ?)"
def sqlInsertTx : String := "INSERT INTO tx(t, instant) VALUES (?, ?)"
def sqlSetCounter : String :=
  "INSERT INTO meta(key, value) VALUES (CAST(? AS TEXT), ?) " ++
  "ON CONFLICT(key) DO UPDATE SET value = excluded.value"
def sqlVolatilePut : String :=
  "INSERT INTO volatile(s, key, value, updated_at) VALUES (?, ?, ?, ?) " ++
  "ON CONFLICT(s, key) DO UPDATE SET value = excluded.value, updated_at = excluded.updated_at"
def sqlVolatileDel : String := "DELETE FROM volatile WHERE s = ? AND key = ?"
def sqlAddPredMulti : String := "INSERT INTO pred_multi(p) VALUES (?) ON CONFLICT(p) DO NOTHING"

end Tiramemsu.Sqlite
