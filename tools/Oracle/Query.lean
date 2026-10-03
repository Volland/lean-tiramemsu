/-
The M3a differential suite (D6): random store scripts written by the pinned Rust build, then the
same file opened by both drivers and queried through their `m3.*` operations: random IR trees
(rows compared as multisets, in order under a root `OrderLimit`), paths in every mode (rows in
order), fact bundles (JSON bytes) and sort keys (bytes). Lean bundles are also imported by Rust
and Rust bundles by Lean. Mismatches pass only through `oracle/deviations.toml`. Tooling only.
-/
import Oracle.Driver
import Oracle.Deviation
import Oracle.Canon
import Test.Store.Gen
import Tiramemsu.Shell.IrJson

namespace Oracle.Query

open Tiramemsu Tiramemsu.Json Tiramemsu.IR Tiramemsu.Codec Tiramemsu.Shell Oracle

--# @lat: [[query#Differential Query Oracle]]

structure Totals where
  compared : Nat := 0
  nonEmpty : Nat := 0
  accepted : Array String := #[]
  failures : Array String := #[]

/-! ## Random queries over the store generator's vocabulary -/

structure G where
  rng : Nat

abbrev GM := StateM G

def nat (lo hi : Nat) : GM Nat := modifyGet fun s =>
  let r := (s.rng * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  (lo + (r / 65536) % (hi - lo + 1), { rng := r })

def pick {α : Type} [Inhabited α] (xs : List α) : GM α := do return xs.getD (← nat 0 (xs.length - 1)) default
def chance (pct : Nat) : GM Bool := do return (← nat 0 99) < pct

def vIri (s : String) : Value := .iri ("urn:tiramemsu:v:" ++ s)

def vars : List String := ["a", "b", "c", "d"]

def subjectT : GM TermOrVar := do
  if ← chance 80 then return .var (← pick vars)
  match ← nat 0 3 with
  | 0 => return .const (.stmt (← nat 1 6))
  | _ => return .const (vIri (← pick ["alice", "bob", "carol", "g1"]))

def objectT : GM TermOrVar := do
  if ← chance 80 then return .var (← pick vars)
  match ← nat 0 4 with
  | 0 => return .const (.int (← nat 0 3))
  | 1 => return .const (.str (← pick ["x", "a@x.org"]))
  | _ => return .const (vIri (← pick ["alice", "bob", "carol", "acme", "g1"]))

def predT : GM TermOrVar := do
  if ← chance 25 then return .var "p"
  if ← chance 5 then return .const (.iri ("urn:tiramemsu:sys:" ++ (← pick ["subject", "object"])))
  return .const (vIri (← pick ["p", "q", "note", "email", "age", "status", "worksAt"]))

def viewG : GM View.ViewSpec := do
  match ← nat 0 19 with
  | 0 => return { tx := .asOf (.tx (Int64.ofNat (← nat 1 6))) }
  | 1 => return { tx := .history }
  | 2 => return { valid := .at (Int64.ofNat ((← nat 0 3) * 400000000000)) }
  | 3 => return { tx := .asOf (.instant (Int64.ofNat (1000 + (← nat 0 30) * 1000))) }
  | _ => return {}

def patternG : GM Op := do
  let p ← predT
  let virt := p.virtual?.isSome
  let c15 ← chance 15
  let eid := if virt then none else if c15 then some "e" else none
  let graph : GraphSel ← if virt then pure .any else match ← nat 0 9 with
    | 0 => pure (.var "g")
    | 1 => pure (.set [.const (vIri "g1")])
    | _ => pure .any
  return .triple { s := ← subjectT, p, o := ← objectT, eid, graph, view := ← viewG }

def exprG : GM Expr := do
  let x : Expr := .var (← pick vars)
  match ← nat 0 9 with
  | 0 => return .cmp (← pick [.eq, .ne, .lt, .gt]) x (.const (.int (← nat 0 3)))
  | 1 => return .cmp .eq x (.const (vIri (← pick ["alice", "bob", "acme"])))
  | 2 => return .bound (← pick vars)
  | 3 => return .not (.bound (← pick vars))
  | 4 => return .func .isIri [x]
  | 5 => return .cmp .gt (.func .strLen [.func .str [x]]) (.const (.int 3))
  | 6 => return .or [.cmp .eq x (.const (.int 1)), .func .isLiteral [x]]
  | 7 => return .func .contains [.func .str [x], .const (.str "a")]
  | 8 => return .cmp .ge (.arith (← pick [.add, .mul, .sub]) x (.const (.int 2))) (.const (.int 3))
  | _ => return .sameTerm x (.const (vIri "alice"))

def pathTextG : Nat → GM String
  | 0 => pick ["p", "q", "worksAt", "sys:subject", "sys:object", "sys:anyRelationship", "^p", "^sys:subject"]
  | d + 1 => do
    match ← nat 0 6 with
    | 0 => return s!"({← pathTextG d})/({← pathTextG d})"
    | 1 => return s!"({← pathTextG d})|({← pathTextG d})"
    | 2 => return s!"({← pathTextG d})*"
    | 3 => return s!"({← pathTextG d})+"
    | 4 => return s!"({← pathTextG d})\{1,2}"
    | _ => pathTextG 0

def opG : Nat → GM Op
  | 0 => patternG
  | d + 1 => do
    match ← nat 0 11 with
    | 0 | 1 => return .join [← opG d, ← opG d]
    | 2 => return .union [← opG d, ← opG d]
    | 3 => return .leftJoin (← opG d) (← opG d) none
    | 4 => return .filter (← exprG) (← opG d)
    | 5 =>
      let x ← opG d
      let vs := (outputVars x).take 2
      let d ← chance 50
      return if vs.isEmpty then x else .project vs d x
    | 6 =>
      if ← chance 30 then
        let x ← opG d
        let vs := outputVars x
        if vs.contains "n" || vs.contains "m" then return x
        return .agg (vs.take 1) [{ var := "n", func := ← pick [.sum, .avg, .groupConcat ","], arg := some (.var (← pick vars)) }] x
      let x ← opG d
      let vs := outputVars x
      if vs.contains "n" then return x
      return .agg (vs.take 1) [{ var := "n", func := .count },
        { var := "m", func := ← pick [.min, .max, .count, .sample], arg := some (.var (← pick vars)) }] x
    | 7 =>
      -- keys over every column, so ties (whose order Rust leaves unspecified) are between equal rows
      let x ← opG d
      let mut keys : List Key := []
      for vv in outputVars x do
        keys := keys ++ [{ expr := .var vv, desc := ← chance 50 }]
      return .order keys none (some (.const (.int (← nat 1 4)))) x
    | 8 =>
      let x ← opG d
      if (scope x).binds "z" then return x
      return .extend "z" (← pick [.var (← pick vars), .const (.int 7), .func .str [.var (← pick vars)]]) x
    | 9 =>
      if ← chance 50 then
        let text ← pathTextG 1
        let pe := (Path.parse text).toOption.getD (.atom "urn:tiramemsu:v:p")
        let mode ← pick [PathMode.reach, .trail, .anyShortest, .allShortest]
        let bp ← chance 30
        let pp : PathPattern := { start := .var "a", «end» := .var "w", path := pe, mode, maxHops := some 2, bindPath := if bp then some "pv" else none }
        let who ← pick ["alice", "bob", "carol"]
        -- bound start, or bound end only (evaluated from the end with the inverse path)
        if ← chance 50 then
          return .join [.values ["a"] [[some (.const (vIri who))]], .path pp]
        return .join [.values ["w"] [[some (.const (vIri who))]], .path pp]
      return .join [← opG d, .values ["a"] [[some (.const (vIri "alice"))], [none]]]
    | _ => return .join [← opG d, ← opG d, ← patternG]

def semG : GM Semantics := do
  match ← nat 0 5 with
  | 0 => return .cypher
  | 1 => return { graphSet := .bagOfEids }
  | 2 => return { missing := .null3VL }
  | _ => return .sparql

/-! ## Comparison -/

def isOrdered : Op → Bool
  | .orderLimit .. => true
  | _ => false

/-- Compares one request on both drivers (`unordered`: the multiset paths of the result). -/
def compare (rust lean : Driver) (reg : Array Deviation) (where_ : String) (op : String) (args : Json)
    (unordered : List String) (t : Totals) : IO Totals := do
  let r ← rust.call op args
  let l ← lean.call op args
  let t := { t with compared := t.compared + 1 }
  let nonEmpty : Bool := match r with
    | .ok j => match j.get? "rows" with
      | some (.arr xs) => xs.size > 0
      | _ => match j with | .arr xs => xs.size > 1 | _ => false
    | _ => false
  let t := if nonEmpty then { t with nonEmpty := t.nonEmpty + 1 } else t
  if sameOutcome unordered l r then return t
  match findDeviation reg op args l r with
  | some d => return { t with accepted := t.accepted.push s!"{where_}: accepted deviation {d.id}" }
  | none =>
    let msg := s!"{where_}: {op} {args.compress}\n  rust: {(r.canon unordered).compress}\n  lean: {(l.canon unordered).compress}"
    return { t with failures := t.failures.push msg }

def runSeed (rust lean : Driver) (reg : Array Deviation) (seed ops queries : Nat) (t : Totals) : IO Totals := do
  let dir : System.FilePath := ".oracle" / "work" / "m3-query"
  IO.FS.createDirAll dir
  let f := dir / s!"rust-{seed}.db"
  let g := dir / s!"import-{seed}"
  for p in [f, (g.toString ++ "-rust.db" : System.FilePath), (g.toString ++ "-lean.db" : System.FilePath)] do
    for suf in ["", "-wal", "-shm"] do
      let q : System.FilePath := p.toString ++ suf
      if ← q.pathExists then IO.FS.removeFile q
  -- one build writes the store (Rust for odd seeds, Lean for even ones: files cross-open)
  let writer := if seed % 2 == 1 then rust else lean
  let _ ← writer.call! "m2.open" (.obj #[("path", .str f.toString), ("clock", .int 1000)])
  for s in Test.Store.Gen.script seed ops do
    let _ ← writer.call s.op s.args
  let _ ← writer.call "m2.close"
  -- both builds query it
  let openArgs := Json.obj #[("path", .str f.toString)]
  let _ ← rust.call! "m3.open" openArgs
  let _ ← lean.call! "m3.open" openArgs
  let mut t := t
  let mut gs : G := { rng := seed * 1000003 + 17 }
  for i in [0:queries] do
    let ((op, sem), gs') := (do pure (← opG 2, ← semG) : GM _).run gs
    gs := gs'
    let q : Query := { root := op, sem }
    if (validate q).toOption.isNone then continue
    let args := Json.obj #[("query", irQueryJ q)]
    t ← compare rust lean reg s!"seed {seed} query {i}" "m3.execute" args
      (if isOrdered op then [] else ["rows"]) t
  -- paths
  for i in [0:queries / 2] do
    let ((text, start, mode, view), gs') := (do
      pure (← pathTextG 2, ← pick [vIri "alice", vIri "bob", vIri "carol", .stmt 1, .stmt 2, .stmt 3],
        ← pick ["REACH", "TRAIL", "ANY_SHORTEST", "ALL_SHORTEST"], ← viewG) : GM _).run gs
    gs := gs'
    let args := Json.obj #[("start", valueJ start), ("text", .str text), ("mode", .str mode), ("maxHops", .int 3),
      ("view", irViewJ view)]
    t ← compare rust lean reg s!"seed {seed} path {i}" "m3.path" args [] t
    let targs := Json.obj #[("start", valueJ start), ("text", .str text), ("mode", .str "REACH"),
      ("timeRespecting", .obj #[]), ("view", irViewJ view)]
    t ← compare rust lean reg s!"seed {seed} timed path {i}" "m3.path" targs [] t
  -- bundles: bytes, and import of each build's bundle by the other
  for e in [1:9] do
    for view in [Json.null, irViewJ { tx := .history }] do
      t ← compare rust lean reg s!"seed {seed} bundle {e}" "m3.bundle" (.obj #[("root", .int e), ("view", view)]) [] t
  -- each build imports the other's bundle into a fresh file (reports compared)
  for e in [1:5] do
    let bj ← rust.call "m3.bundle" (.obj #[("root", .int e)])
    match bj with
    | .ok j =>
      match j.getStr? "json" with
      | some text =>
        for (who, dr) in [("rust", rust), ("lean", lean)] do
          let target : System.FilePath := g.toString ++ s!"-{who}-{e}.db"
          for suf in ["", "-wal", "-shm"] do
            let q : System.FilePath := target.toString ++ suf
            if ← q.pathExists then IO.FS.removeFile q
          let _ := dr
        let tr : System.FilePath := g.toString ++ s!"-rust-{e}.db"
        let tl : System.FilePath := g.toString ++ s!"-lean-{e}.db"
        let _ ← rust.call "m3.close"
        let _ ← lean.call "m3.close"
        let _ ← rust.call! "m3.open" (.obj #[("path", .str tr.toString)])
        let _ ← lean.call! "m3.open" (.obj #[("path", .str tl.toString)])
        let r ← rust.call "m3.importBundle" (.obj #[("json", .str text)])
        let l ← lean.call "m3.importBundle" (.obj #[("json", .str text)])
        t := { t with compared := t.compared + 1 }
        if !sameOutcome [] l r then
          t := { t with failures := t.failures.push s!"seed {seed} import bundle {e}\n  rust: {(r.canon []).compress}\n  lean: {(l.canon []).compress}" }
        let _ ← rust.call "m3.close"
        let _ ← lean.call "m3.close"
        let _ ← rust.call! "m3.open" openArgs
        let _ ← lean.call! "m3.open" openArgs
      | none => pure ()
    | _ => pure ()
  let _ ← rust.call "m3.close"
  let _ ← lean.call "m3.close"
  pure t

def sortKeyCheck (rust lean : Driver) (t : Totals) : IO Totals := do
  let vals : Array Value := #[.iri "urn:a", .node 3, .bnode 4, .stmt 5, .tx 6, .int 0, .int (-7), .int 576460752303423487,
    .bool true, .bool false, .dateTime 1700000000000 (some 60), .dateTime (-5) none, .date (-3), .str "", .str "héllo",
    .langStr "hi" "en", .typed "x" "urn:dt", .double ⟨0x3FF8000000000000⟩, .double ⟨0x8000000000000000⟩,
    .double ⟨0x7FF0000000000000⟩, .double ⟨0xFFF0000000000000⟩, .double ⟨0x7FF8000000000000⟩,
    .double ⟨0x4340000000000001⟩, .decimal "1.5", .decimal "-0.25", .decimal "123456789012345678901234567890.5",
    .int 9007199254740993]
  -- and generated ones
  let gen : Array Value := (List.range 400).toArray.map fun i =>
    let r := (i * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    match i % 8 with
    | 0 => .int (Int.ofNat (r % 2 ^ 59) - 2 ^ 58)
    | 1 => .double ⟨r.toUInt64⟩
    | 2 => .dateTime (Int.ofNat (r % 2 ^ 46) - 2 ^ 45) (some ((r % 1681 : Nat) - 840 : Int))
    | 3 => .date (Int.ofNat (r % 2 ^ 30) - 2 ^ 29)
    | 4 => .str (String.ofList ((List.range (r % 12)).map fun k => Char.ofNat (32 + (r / (k + 1)) % 200)))
    | 5 => .decimal s!"{(r % 100000 : Nat)}.{(r / 7 % 1000 : Nat)}"
    | 6 => .node (r % 2 ^ 40)
    | _ => .iri s!"urn:x:{r % 1000}"
  let args := Json.obj #[("values", .arr ((vals ++ gen).map valueJ))]
  compare rust lean #[] "sort keys" "m3.sortKey" args [] t

def flagNat (args : List String) (name : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def main (args : List String) : IO UInt32 := do
  let seeds := flagNat args "--seeds" 10
  let ops := flagNat args "--ops" 80
  let queries := flagNat args "--queries" 40
  let reg ← loadDeviations ("oracle" / "deviations.toml")
  let rust ← startRust
  let lean ← startLean
  let mut t : Totals ← sortKeyCheck rust lean {}
  for seed in [1:seeds + 1] do
    t ← runSeed rust lean reg seed ops queries t
    if t.failures.size ≥ 20 then break
  rust.stop
  lean.stop
  for f in t.failures do IO.eprintln s!"FAIL {f}"
  for a in t.accepted do IO.println s!"  {a}"
  IO.println s!"query differential: {seeds} seeds, {t.compared} compared ({t.nonEmpty} non-empty), {t.accepted.size} accepted deviations, {t.failures.size} failures"
  pure (if t.failures.isEmpty then 0 else 1)

end Oracle.Query
