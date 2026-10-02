/-
The bag operators of the reference semantics, shared with the evaluator: filter, extend,
left join, projection with distinct, aggregation with canonical folds, ordering with the
canonical tie-break, skip and limit, and the relationship-isomorphism filter.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Sem.Expr

namespace Tiramemsu.Sem

open Tiramemsu.Codec Tiramemsu.IR

--# @lat: [[query#Reference Semantics#Operators]]

/-- `Filter`: the rows whose condition is true. -/
def filterB (c : RExpr) (xs : Bag) : Bag := xs.filter c.holds

/-- `Extend`: binds position `i` to the value of `e`, or leaves it unbound when `e` errors. -/
def extendB (i : Nat) (e : RExpr) (xs : Bag) : Bag :=
  xs.map fun r => match e.eval r with
    | some v => r.setAt i (some v)
    | none => r

/-- `LeftJoin`: each merge with a compatible right row satisfying the condition, or the left
row alone when there is none. -/
def leftJoinB (m : Missing) (P Q : Schema) (c : Option RExpr) (xs ys : Bag) : Bag :=
  xs.flatMap fun a =>
    let ms := ys.filterMap fun b =>
      if compat m P Q a b then
        let r := merge a b
        if (match c with | some e => e.holds r | none => true) then some r else none
      else none
    if ms.isEmpty then [a] else ms

/-- `Project`: keeps the listed positions; distinct keeps one copy of each row. -/
def projectB (keep : List Nat) (distinct : Bool) (xs : Bag) : Bag :=
  let ys := xs.map (Row.restrict keep.contains)
  if distinct then ys.eraseDups else ys

/-- Values in the canonical value order. -/
def sortValues (vs : List Value) : List Value := vs.mergeSort fun a b => cmpValue a b != .gt

/-- One aggregate over a group (`none`: unbound). Every fold runs in the canonical value
order, so the result depends only on the multiset of the group. -/
def aggregateOne (f : AggFunc) (arg : Option RExpr) (distinct : Bool) (grp : Bag) : Option Value :=
  match arg with
  | none => some (.int grp.length)
  | some e =>
    let vs0 := sortValues (grp.filterMap e.eval)
    let vs := if distinct then vs0.eraseDups else vs0
    match f with
    | .count => some (.int vs.length)
    | .sum =>
      match vs.filterMap Value.num? with
      | [] => none
      | n :: ns => some (ns.foldl (arith .add) n).toValue
    | .avg =>
      match vs.filterMap Value.num? with
      | [] => none
      | n :: ns =>
        let s := (ns.foldl (arith .add) n).toDouble
        some (.double (ofFloat (toFloat s / (Float.ofNat (ns.length + 1)))))
    | .min => vs.head?
    | .max => vs.getLast?
    | .sample => vs.head?
    | .groupConcat sep =>
      if vs.isEmpty then none else some (.str (sep.intercalate (vs.map strOf)))

/-- The group key of a row. -/
def groupKey (g : List Nat) (r : Row) : List (Option Value) := g.map r.get

/-- Groups of a bag by key, in order of first appearance. -/
def groupBy (g : List Nat) (xs : Bag) : List (List (Option Value) × Bag) :=
  let keys := (xs.map (groupKey g)).eraseDups
  keys.map fun k => (k, xs.filter fun r => groupKey g r == k)

/-- `Aggregate(G, aggs)`: one row per group binding `G` and every output. With empty `G` and
an empty input, one row (`COUNT` = 0, other aggregates unbound). -/
def aggregateB (n : Nat) (g : List Nat) (aggs : List (Nat × AggFunc × Option RExpr × Bool))
    (xs : Bag) : Bag :=
  let groups := if g.isEmpty && xs.isEmpty then [([], [])] else groupBy g xs
  groups.map fun (k, grp) =>
    let r0 := (g.zip k).foldl (fun (r : Row) (i, c) => r.set i c) (Row.empty n)
    aggs.foldl (fun (r : Row) (i, f, a, d) => r.set i (aggregateOne f a d grp)) r0

/-- Comparison of two key cells: present values by sort key; a missing value is smallest
under `Unbound` and largest under `Null3VL` (Rust's NULL placement). -/
def cmpKeyCell (m : Missing) : Option Value → Option Value → Ordering
  | none, none => .eq
  | none, some _ => if m == .unbound then .lt else .gt
  | some _, none => if m == .unbound then .gt else .lt
  | some a, some b => cmpBytes (sortKey a) (sortKey b)

/-- Lexicographic comparison of key vectors, descending keys reversed. -/
def cmpKeys (m : Missing) : List Bool → List (Option Value) → List (Option Value) → Ordering
  | d :: ds, a :: as, b :: bs =>
    match cmpKeyCell m a b with
    | .eq => cmpKeys m ds as bs
    | o => if d then o.swap else o
  | _, _, _ => .eq

/-- The order of `OrderLimit`: by the keys, ties by the canonical row order. -/
def orderLe (m : Missing) (descs : List Bool) (a b : List (Option Value) × Row) : Bool :=
  match cmpKeys m descs a.1 b.1 with
  | .lt => true
  | .gt => false
  | .eq => rowLe a.2 b.2

/-- `OrderLimit`: sort, drop `skip`, keep at most `limit`. -/
def orderLimitB (m : Missing) (keys : List (RExpr × Bool)) (skip limit : Option Nat) (xs : Bag) : Bag :=
  let keyed := xs.map fun r => (keys.map fun (e, _) => e.eval r, r)
  let sorted := (keyed.mergeSort (orderLe m (keys.map (·.2)))).map (·.2)
  let dropped := sorted.drop (skip.getD 0)
  match limit with
  | some l => dropped.take l
  | none => dropped

/-- Relationship isomorphism: no two eid cells of one match group are equal. -/
def isoOk (cols : List (Nat × Nat)) (r : Row) : Bool :=
  cols.all fun (g, i) => cols.all fun (h, j) =>
    g != h || i == j || (match r.get i, r.get j with
      | some a, some b => a != b
      | _, _ => true)

def isoFilter (cols : List (Nat × Nat)) (xs : Bag) : Bag :=
  if cols.isEmpty then xs else xs.filter (isoOk cols)

end Tiramemsu.Sem
