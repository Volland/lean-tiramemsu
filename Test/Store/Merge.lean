/-
`tiramemsu-tests merge`: randomised checks of the merge laws on statement sets (commutativity,
associativity, idempotence, every eid kept, retraction wins, earliest retraction), and a check
that no runtime module outside `Tiramemsu/Model/Merge.lean` uses the merge.
-/
import Test.Util

namespace Test.Store.MergeTest

open Tiramemsu.Store Tiramemsu.Model

--# @lat: [[engine#Merge Laws]]

/-- A small linear congruential generator. -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
def draw (s : Nat) (n : Nat) : Nat × Nat := let s' := next s; ((s' / 65536) % n, s')

/-- One random state of statement `e`: content from a small range so that two sets often
disagree on it; retracted half of the time. -/
def randRow (e : Nat) (s : Nat) : TripleRow × Nat := Id.run do
  let (a, s) := draw s 3
  let (b, s) := draw s 3
  let (r, s) := draw s 2
  let (t, s) := draw s 4
  let (k, s) := draw s 4
  let row : TripleRow :=
    TripleRow.mk (Int64.ofNat (e * 16 + 3)) (Int64.ofNat a) 0 (Int64.ofNat b) (Int64.ofNat (1 + a)) none none none none
  let row := if r == 0 then row else { row with tRet := some (Int64.ofNat (2 + t)), retKind := some (Int64.ofNat k) }
  (row, s)

/-- A random statement set over eids `0 … 11`, strictly ascending. -/
def randSet (s : Nat) : StmtSet × Nat := Id.run do
  let mut s := s
  let mut out : StmtSet := []
  for e in List.range 12 do
    let (keep, s1) := draw s 2
    s := s1
    if keep == 0 then
      let (row, s2) := randRow e s
      s := s2
      out := out ++ [row]
  (out, s)

def eids (xs : StmtSet) : List Int64 := xs.map (·.eid)

def main (args : List String) : IO UInt32 := do
  let seeds := match args with
    | ["--seeds", n] => n.toNat?.getD 500
    | _ => 500
  let (_, r) ← (do
    let mut s := 7
    let mut ok := true
    let mut detail := ""
    for i in List.range seeds do
      let (a, s1) := randSet s
      let (b, s2) := randSet s1
      let (c, s3) := randSet s2
      s := s3
      let m := merge a b
      if merge a b != merge b a then ok := false; detail := s!"commutativity, seed {i}"
      if merge (merge a b) c != merge a (merge b c) then ok := false; detail := s!"associativity, seed {i}"
      if merge a a != a then ok := false; detail := s!"idempotence, seed {i}"
      -- every eid of either set is kept, once, ascending
      let all := (eids a ++ eids b).eraseDups.mergeSort fun x y => decide (x.toInt ≤ y.toInt)
      if eids m != all then ok := false; detail := s!"eids kept, seed {i}"
      for x in a do
        match lookup m x.eid.toInt with
        | none => ok := false; detail := s!"lost eid, seed {i}"
        | some y =>
          -- retraction wins, and the earliest retraction is kept
          if x.tRet.isSome && y.tRet.isNone then ok := false; detail := s!"retraction wins, seed {i}"
          match x.tRet, y.tRet with
          | some tx, some ty => if ty.toInt > tx.toInt then ok := false; detail := s!"earliest retraction, seed {i}"
          | _, _ => pure ()
    check "merge laws on random statement sets" ok detail
    -- no runtime module except the merge itself refers to it
    let files ← System.FilePath.walkDir "src/Tiramemsu"
    let mut users := #[]
    for f in files do
      if f.extension == some "lean" && !(f.toString.endsWith "Model/Merge.lean") then
        let text ← IO.FS.readFile f
        if (text.splitOn "Tiramemsu.Model.Merge").length > 1 && !(f.toString.endsWith "Tiramemsu.lean") then
          users := users.push f.toString
        if (text.splitOn "Model.merge").length > 1 || (text.splitOn "joinRow").length > 1 then
          users := users.push f.toString
    check "no public operation merges" users.isEmpty s!"used in {users}" : TestM Unit).run {}
  finish "merge" r

end Test.Store.MergeTest
