/-
The sorted range-scan interface every join algorithm consumes (this change's index nested
loop, and M3b's Leapfrog Triejoin), as read programs over the M0 `Store` interface, and index
choice for triple patterns.

- `rangeScan ord v pfx`: the statements visible in `v` whose leading key columns (in the order
  `ord`) equal `pfx`, ascending in the family key with the eid last. The live family serves
  `Now`, the history family `AsOf` and `History`; a valid-time selector filters inside the scan.
- `seek ord v pfx lo`: the least next-column key at or after `lo` among those statements.
- `lookupEid`: one statement by eid.
- `indexFor`: the order whose key prefix is exactly the bound positions.
- `dedupAdj`: one statement per run of equal `(s, p, o)` (scan order keeps them adjacent).
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Sem.Denote

namespace Tiramemsu.Exec

open Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec

--# @lat: [[query#Index Nested-Loop Join#Sorted Range Scans]]

/-- The three index orders. -/
inductive IndexOrder where
  | spo | pos | osp
  deriving Repr, DecidableEq, Inhabited

def IndexOrder.name : IndexOrder → String
  | .spo => "spo" | .pos => "pos" | .osp => "osp"

/-- The family serving an order under a view: live under `Now`, history otherwise. -/
def IndexOrder.family (ord : IndexOrder) (v : Store.View) : Family :=
  if v.tx == .now then
    match ord with | .spo => .liveSpo | .pos => .livePos | .osp => .liveOsp
  else
    match ord with | .spo => .histSpo | .pos => .histPos | .osp => .histOsp

/-- The scan of an order, view and key prefix. -/
def scanSpec (ord : IndexOrder) (v : Store.View) (pfx : List Int64) : ScanSpec :=
  { family := ord.family v, pre := pfx.toArray, view := v }

/-- Every visible statement matching the prefix, in key order. -/
def rangeScan (ord : IndexOrder) (v : Store.View) (pfx : List Int64) : RProg (List TripleRow) := do
  return (← RProg.lift (.scan (scanSpec ord v pfx))).toList

/-- The key column following a prefix of length `k` in an order. -/
def nextCol (ord : IndexOrder) (k : Nat) : TripleRow → Int64 := fun r =>
  match (Family.perm (ord.family {})).getD k .eid with
  | .s => r.s | .p => r.p | .o => r.o | _ => r.eid

/-- The least next-column key at or after `lo` among the statements of a prefix. -/
def seek (ord : IndexOrder) (v : Store.View) (pfx : List Int64) (lo : Int64) : RProg (Option Int64) := do
  let rows ← RProg.lift (.scan { scanSpec ord v pfx with lo := some (.incl lo) })
  return (rows.toList.head?).map (nextCol ord pfx.length)

/-- One statement by eid, if the view selects it. -/
def lookupEid (v : Store.View) (e : Int64) : RProg (Option TripleRow) := do
  match ← RProg.lift (.triple e) with
  | some r => return if v.admits r then some r else none
  | none => return none

/-- The order and key prefix for bound subject, predicate and object positions: the order
whose prefix is exactly the bound set. -/
def indexFor : Option Int64 → Option Int64 → Option Int64 → IndexOrder × List Int64
  | some s, some p, some o => (.spo, [s, p, o])
  | some s, some p, none => (.spo, [s, p])
  | some s, none, some o => (.osp, [o, s])
  | some s, none, none => (.spo, [s])
  | none, some p, some o => (.pos, [p, o])
  | none, some p, none => (.pos, [p])
  | none, none, some o => (.osp, [o])
  | none, none, none => (.spo, [])

/-- The content of a statement. -/
def spo (r : TripleRow) : Int64 × Int64 × Int64 := (r.s, r.p, r.o)

/-- Drops the statements equal in `(s, p, o)` to the last one kept. -/
def dedupAdjFrom (last : TripleRow) : List TripleRow → List TripleRow
  | [] => []
  | b :: rest => if spo last == spo b then dedupAdjFrom last rest else b :: dedupAdjFrom b rest

/-- Removes consecutive statements with equal `(s, p, o)`. -/
def dedupAdj : List TripleRow → List TripleRow
  | [] => []
  | a :: rest => a :: dedupAdjFrom a rest

end Tiramemsu.Exec
