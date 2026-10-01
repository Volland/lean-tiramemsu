/-
Canonical comparison of driver results: object keys sorted; integers exact (arbitrary
precision, never through a double); arrays at the listed paths compared as multisets, every
other array in order; doubles by lexical form; errors by code only. Tooling only.
-/
import Tiramemsu.Shell.Json

namespace Oracle

open Tiramemsu.Json

--# @lat: [[verification#Differential Oracle#Canonical Comparison]]

/-- The result of one driver call. -/
inductive Outcome where
  | ok (result : Json)
  | err (code : String) (message : String)
  deriving Repr, Inhabited, BEq

def Outcome.ofResponse (resp : Json) : Outcome :=
  match resp.get? "ok", resp.get? "err" with
  | some r, _ => .ok r
  | none, some e => .err ((e.getStr? "code").getD "Error") ((e.getStr? "message").getD "")
  | none, none => .err "Protocol" s!"malformed response {resp}"

def Outcome.isUnsupported : Outcome → Bool
  | .err "Unsupported" _ => true
  | _ => false

private def child (path k : String) : String := if path.isEmpty then k else path ++ "." ++ k

/-- The canonical form of a value; `unordered` lists the paths of multiset arrays
(`""` is the value itself, `"a.b"` the array under keys `a`, then `b`). -/
partial def canon (unordered : List String) (path : String := "") : Json → Json
  | .obj kvs =>
    let sorted := kvs.qsort (·.1 < ·.1)
    .obj (sorted.map fun (k, v) => (k, canon unordered (child path k) v))
  | .arr xs =>
    let ys := xs.map (canon unordered path)
    if unordered.contains path then .arr (ys.qsort (·.compress < ·.compress)) else .arr ys
  | j => j

/-- The canonical form of an outcome: errors by code only. -/
def Outcome.canon (unordered : List String) : Outcome → Json
  | .ok r => .obj #[("ok", Oracle.canon unordered "" r)]
  | .err code _ => .obj #[("err", .obj #[("code", .str code)])]

/-- Whether two outcomes are equal in canonical form. -/
def sameOutcome (unordered : List String) (a b : Outcome) : Bool :=
  (a.canon unordered).compress == (b.canon unordered).compress

end Oracle
