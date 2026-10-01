/-
Memory merge as an algebraic object only (D15): statements form a two-phase set keyed by eid;
the merge of two statement sets holds every eid of either, and for an eid in both, the row
whose content is smallest in a fixed total order with the earliest retraction (by `t_ret`, then
`ret_kind`; live counts as later than any retraction). No database operation merges.
Verified module: imports only `Init` and verified modules.
-/
import Tiramemsu.Store.Order

namespace Tiramemsu.Model

open Tiramemsu.Store

--# @lat: [[engine#Merge Laws]]

/-- A statement set: rows strictly ascending by eid. -/
abbrev StmtSet := List TripleRow

/-- The content of a row (everything but the retraction), as a key. -/
def contentKey (r : TripleRow) : List (Option Int) :=
  [some r.eid.toInt, some r.s.toInt, some r.p.toInt, some r.o.toInt, some r.tAdd.toInt,
   r.vFrom.map (·.toInt), r.vTo.map (·.toInt)]

/-- The retraction of a row as a key: retracted rows first (earliest `t_ret`, then
`ret_kind`), live rows last. -/
def retKey (r : TripleRow) : List (Option Int) :=
  [some (if r.tRet.isNone then 1 else 0), r.tRet.map (·.toInt), r.retKind.map (·.toInt)]

/-- The smaller of two rows under a key. -/
def minBy (k : TripleRow → List (Option Int)) (a b : TripleRow) : TripleRow :=
  if cmpKey (k a) (k b) == .gt then b else a

/-- The join of two states of one eid: the smallest content with the earliest retraction. -/
def joinRow (a b : TripleRow) : TripleRow :=
  let c := minBy contentKey a b
  let r := minBy retKey a b
  { c with tRet := r.tRet, retKind := r.retKind }

/-- The join of two optional states (absent is the bottom). -/
def joinOpt : Option TripleRow → Option TripleRow → Option TripleRow
  | none, y => y
  | x, none => x
  | some a, some b => some (joinRow a b)

/-- The merge of two statement sets (strictly ascending by eid). -/
def merge : StmtSet → StmtSet → StmtSet
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x.eid.toInt < y.eid.toInt then x :: merge xs (y :: ys)
    else if y.eid.toInt < x.eid.toInt then y :: merge (x :: xs) ys
    else joinRow x y :: merge xs ys
termination_by xs ys => xs.length + ys.length

/-- The state of an eid in a statement set. -/
def lookup (s : StmtSet) (e : Int) : Option TripleRow := s.find? (·.eid.toInt == e)

end Tiramemsu.Model
