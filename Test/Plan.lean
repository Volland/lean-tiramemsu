/-
The plan test: `EXPLAIN QUERY PLAN` of every scan shape. Order never depends on the plan (the
SQL has an explicit ORDER BY); this test reports every shape that is not served by its
family's index as a covering index without a separate sort step. It fails only when a shape
cannot be prepared.
-/
import Test.Util

namespace Test.Plan

open Test Tiramemsu.Store Tiramemsu.Sqlite

/-- Every scan shape (family, prefix length, bound shapes, view shape), with dummy values. -/
def shapes : Array ScanSpec := Id.run do
  let fams := #[Family.liveSpo, .livePos, .liveOsp, .histSpo, .histPos, .histOsp, .validP,
    .logAdd, .logRet]
  let bounds : Array (Option Bound) := #[none, some (.incl 5), some (.excl 5)]
  let mut out := #[]
  for f in fams do
    let txs : Array TxSel := if f.isLive then #[.now] else #[.now, .asOf 3, .history]
    for k in [0:f.maxPrefix + 1] do
      for lo in bounds do
        for hi in bounds do
          for tx in txs do
            for valid in #[ValidSel.unfiltered, .at 7] do
              out := out.push { family := f, pre := (Array.range k).map (·.toInt64), lo, hi,
                                view := { tx, valid } }
  return out

def describe (sp : ScanSpec) : String :=
  let b (x : Option Bound) := match x with | none => "-" | some (.incl _) => "incl" | some (.excl _) => "excl"
  let tx := match sp.view.tx with | .now => "now" | .asOf _ => "asOf" | .history => "history"
  let v := match sp.view.valid with | .unfiltered => "" | .at _ => "+validAt"
  s!"{sp.family.indexName} prefix {sp.pre.size} lo {b sp.lo} hi {b sp.hi} {tx}{v}"

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | [p] => pure (p : System.FilePath)
    | _ => freshFormat1 "plan"
  let res ← (do
    let c ← openReader path
    let mut covering := 0
    let mut notCovering : Array String := #[]
    let mut otherIndex : Array String := #[]
    let mut sorted : Array String := #[]
    for sp in shapes do
      let (sql, params) := scanSql sp
      let details ← c.queryAll ("EXPLAIN QUERY PLAN " ++ sql) params fun st => lift (st.columnText 3)
      let idx := sp.family.indexName
      let has (needle : String) := details.any fun d => (d.splitOn needle).length > 1
      let usesIdx := has s!"INDEX {idx} " || details.any (·.endsWith s!"INDEX {idx}")
      if has "TEMP B-TREE" then sorted := sorted.push s!"{describe sp}: {details}"
      else if !usesIdx then otherIndex := otherIndex.push s!"{describe sp}: {details}"
      else if has s!"COVERING INDEX {idx}" then covering := covering + 1
      else notCovering := notCovering.push (describe sp)
    c.clearCache
    pure (covering, notCovering, otherIndex, sorted) : SqlM _).run
  match res with
  | .error e => IO.eprintln s!"FAIL plan test: {e}"; pure 1
  | .ok (covering, notCovering, otherIndex, sorted) =>
    IO.println s!"plan: {shapes.size} scan shapes on {path}: {covering} covering, {notCovering.size} use the family index without covering it, {otherIndex.size} use another index or a table scan, {sorted.size} need a sort step"
    let fams := (notCovering.map fun s => (s.splitOn " ").head!).toList.eraseDups
    unless notCovering.isEmpty do
      IO.println s!"  reported (index used, not covering: the row needs columns the index lacks): {fams}"
    for s in otherIndex do IO.println s!"  reported (other plan): {s}"
    for s in sorted do IO.println s!"  reported (sort step): {s}"
    pure 0

end Test.Plan
