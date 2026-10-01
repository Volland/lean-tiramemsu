/-
The walk behind the retraction cascade and the dependents read: from a root, breadth-first
over the statements (selected by a view) whose subject or object is a statement already
reached. Each expansion appends unseen eids in ascending order; a visited set makes reference
cycles terminate. The loop is total: its fuel is the `next_stmt` counter plus one, which bounds
the number of statements (proven sufficient on well-formed states).
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Std.Data.HashSet
import Tiramemsu.Engine.Op

namespace Tiramemsu.Engine

open Tiramemsu.Store

--# @lat: [[engine#Cascade Walk]]

/-- Ascending order of raw ids, without duplicates. -/
def sortDedup (xs : List Int64) : List Int64 :=
  ((xs.mergeSort fun a b => decide (a.toInt ≤ b.toInt))).eraseDups

/-- The families a walk expands over: live ones under now, history ones otherwise. -/
def walkFamilies (v : View) : Family × Family :=
  if v.tx == .now then (.liveSpo, .liveOsp) else (.histSpo, .histOsp)

/-- The statements selected by `v` whose subject or object is `x`: eids, ascending. -/
def neighbors (v : View) (x : Int64) : RProg (List Int64) := do
  let (fs, fo) := walkFamilies v
  let a ← RProg.lift (.scan { family := fs, pre := #[x], view := v })
  let b ← RProg.lift (.scan { family := fo, pre := #[x], view := v })
  pure (sortDedup ((a.toList ++ b.toList).map (·.eid)))

/-- The outcome of a walk. -/
inductive WalkResult where
  /-- Every statement reached, root first. -/
  | done (order : Array Int64)
  /-- The set grew past the limit. -/
  | exceeded
  /-- The fuel ran out first (impossible on well-formed stores). -/
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- Appends the unseen ids of one expansion; `true` once the order is longer than the limit. -/
def walkPush (limit : Option Nat) :
    List Int64 → Array Int64 → Std.HashSet Int64 → Array Int64 × Std.HashSet Int64 × Bool
  | [], order, seen => (order, seen, false)
  | x :: xs, order, seen =>
    if seen.contains x then walkPush limit xs order seen
    else
      let order := order.push x
      if limit.any (order.size > ·) then (order, seen.insert x, true)
      else walkPush limit xs order (seen.insert x)

/-- The breadth-first loop: expands `order[i]`, then the rest. -/
def walkLoop (nb : Int64 → RProg (List Int64)) (limit : Option Nat) :
    Nat → Array Int64 → Std.HashSet Int64 → Nat → RProg WalkResult
  | 0, _, _, _ => pure .outOfFuel
  | fuel + 1, order, seen, i =>
    if h : i < order.size then do
      let ns ← nb order[i]
      match walkPush limit ns order seen with
      | (_, _, true) => pure .exceeded
      | (order', seen', false) => walkLoop nb limit fuel order' seen' (i + 1)
    else pure (.done order)

/-- The walk from `root` with at most `fuel` expansions. -/
def walk (nb : Int64 → RProg (List Int64)) (limit : Option Nat) (root : Int64) (fuel : Nat) :
    RProg WalkResult :=
  if limit.any (1 > ·) then pure .exceeded
  else walkLoop nb limit fuel #[root] (({} : Std.HashSet Int64).insert root) 0

/-- The fuel of a walk: the `next_stmt` counter plus one. -/
def walkFuel : RProg Nat := do
  let n ← RProg.lift (.counter "next_stmt")
  pure ((n.getD 0).toInt.toNat + 1)

end Tiramemsu.Engine
