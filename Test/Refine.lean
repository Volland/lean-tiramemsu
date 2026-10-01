/-
Refinement tests: seeded random operation sequences (core `StdGen`) mixing valid and invalid
writes, transaction and savepoint control, three snapshot readers and every read kind, run in
lock step on `ModelStore` and `SqliteStore` through the same interface code, comparing every
result (scan order and error variant included). A divergence is minimized by delta debugging
and written to `testdata/refine/` as a regression case, which every later run replays.
-/
import Test.Util

namespace Test.Refine

open Test Tiramemsu.Store Tiramemsu.Sqlite Tiramemsu.Json

--# @lat: [[verification#Differential Oracle#Refinement Tests]]

/-- A read. -/
inductive ReadOp where
  | scan (sp : ScanSpec) (limit : Option Nat)
  | triple (e : Int64)
  | termById (i : Int64)
  | termByKey (tag : Int64) (lex : String) (dt : Option Int64) (lang : Option String)
  | txByT (t : Int64)
  | txAtOrBefore (i : Int64)
  | counter (n : String)
  | volatileGet (s k : Int64)
  | volatileOf (s : Int64)
  | predMulti (p : Int64)
  deriving Repr, Inhabited

/-- An operation of a sequence. -/
inductive Op where
  | write (w : WriteOp)
  | read (r : ReadOp)
  | beginRead (slot : Nat)
  | endRead (slot : Nat)
  | readOn (slot : Nat) (r : ReadOp)
  deriving Repr, Inhabited

/-- A comparable result. Misuse is compared by variant, not by message. -/
inductive Res where
  | unit
  | skip
  | rows (xs : List TripleRow)
  | triple (o : Option TripleRow)
  | term (o : Option TermRow)
  | id (o : Option Int64)
  | tx (o : Option TxRow)
  | vol (o : Option VolatileRow)
  | vols (xs : List VolatileRow)
  | bool (b : Bool)
  | err (kind : String)
  deriving Repr, DecidableEq, Inhabited

def errKind : StoreError → String
  | .violation v => s!"violation {reprStr v}"
  | .notFound => "notFound"
  | .invalidScan => "invalidScan"
  | .misuse _ => "misuse"
  | .sqlite c x m => s!"sqlite {c}/{x} {m}"

/-! ## Execution through the interface (same code for both stores) -/

def execRead {n : Type → Type} [Monad n] [ReadStore n] : ReadOp → n Res
  | .scan sp limit => do
    let acc ← ReadStore.scan sp (#[] : Array TripleRow) fun acc r =>
      let acc := acc.push r
      pure (if limit == some acc.size then .done acc else .yield acc)
    pure (.rows acc.toList)
  | .triple e => .triple <$> ReadStore.triple e
  | .termById i => .term <$> ReadStore.termById i
  | .termByKey t l d g => .id <$> ReadStore.termByKey t l d g
  | .txByT t => .tx <$> ReadStore.txByT t
  | .txAtOrBefore i => .tx <$> ReadStore.txAtOrBefore i
  | .counter c => .id <$> ReadStore.counter c
  | .volatileGet s k => .vol <$> ReadStore.volatileGet s k
  | .volatileOf s => (.vols ·.toList) <$> ReadStore.volatileOf s
  | .predMulti p => .bool <$> ReadStore.predMulti p

def execWrite {m : Type → Type} [WriteStore m] : WriteOp → m Unit
  | .insertTriple r => WriteStore.insertTriple r
  | .retract e t k => WriteStore.retract e t k
  | .insertTerm r => WriteStore.insertTerm r
  | .insertTx r => WriteStore.insertTx r
  | .setCounter n v => WriteStore.setCounter n v
  | .volatilePut r => WriteStore.volatilePut r
  | .volatileDel s k => WriteStore.volatileDel s k
  | .addPredMulti p => WriteStore.addPredMulti p
  | .begin => WriteStore.begin
  | .commit => WriteStore.commit
  | .rollback => WriteStore.rollback
  | .savepoint n => WriteStore.savepoint n
  | .rollbackTo n => WriteStore.rollbackTo n
  | .release n => WriteStore.release n

section
variable {m : Type → Type} {snap : Type} {r : Type → Type}
variable [Monad m] [MonadExceptOf StoreError m] [WriteStore m] [SnapshotStore m snap r]
variable [Monad r] [ReadStore r]

def caught (x : m Res) : m Res := tryCatchThe StoreError x fun e => pure (.err (errKind e))

/-- One operation with the reader slots; a reader op on an empty slot (or a begin on a busy
one) is skipped identically on both stores. -/
def execOp (readers : Array (Option snap)) : Op → m (Res × Array (Option snap))
  | .write w => do return (← caught (do execWrite w; pure .unit), readers)
  | .read q => do return (← caught (execRead q), readers)
  | .beginRead i => do
    match readers[i]? with
    | some none =>
      let res ← tryCatchThe StoreError (do let s ← SnapshotStore.beginRead (m := m); pure (Sum.inr s))
        (fun e => pure (.inl (errKind e)))
      match res with
      | .inr s => pure (.unit, readers.set! i (some s))
      | .inl e => pure (.err e, readers)
    | _ => pure (.skip, readers)
  | .endRead i => do
    match readers[i]? with
    | some (some s) =>
      let res ← caught (do SnapshotStore.endRead (m := m) s; pure .unit)
      pure (res, readers.set! i none)
    | _ => pure (.skip, readers)
  | .readOn i q => do
    match readers[i]? with
    | some (some s) => return (← caught (SnapshotStore.withSnapshot s (execRead q)), readers)
    | _ => pure (.skip, readers)
end

/-- Runs a sequence on the model. -/
def runModel (init : ModelState) (ops : Array Op) : Array Res := Id.run do
  let mut s := ModelStore.ofState init
  let mut readers : Array (Option ModelState) := #[none, none, none]
  let mut out := #[]
  for op in ops do
    match (execOp readers op : ModelM _).run s with
    | .ok ((res, rd), s') => out := out.push res; readers := rd; s := s'
    | .error e => out := out.push (.err (errKind e))
  return out

/-- Runs a sequence on a SQLite copy of `initFile`. -/
def runSqlite (initFile : System.FilePath) (ops : Array Op) (fault : Op → Res → Res := fun _ r => r) :
    IO (Array Res) := do
  let path ← freshPath "refine"
  copyDb initFile path
  match ← (Store.open path).run with
  | .error e => throw (IO.userError s!"cannot open {path}: {e}")
  | .ok st =>
    let mut readers : Array (Option Reader) := #[none, none, none]
    let mut out := #[]
    for op in ops do
      match ← ((execOp readers op : SqliteM _) st).run with
      | .ok (res, rd) => out := out.push (fault op res); readers := rd
      | .error e => out := out.push (.err (errKind e))
    for rd in readers do
      if let some s := rd then let _ ← (SnapshotStore.endRead (m := SqliteM) s st).run
    st.close
    return out

/-- The index of the first differing result, if any. -/
def firstDiff (a b : Array Res) : Option Nat :=
  (List.range (max a.size b.size)).find? fun i => a[i]? != b[i]?

/-! ## Generator -/

/-- Generator state: the random generator and a guess of whether a write transaction is open,
used to keep most writes inside a transaction while still producing misuse. -/
structure G where
  g : StdGen
  inTx : Bool := false

abbrev GenM := StateM G

def nat (lo hi : Nat) : GenM Nat := modifyGet fun s =>
  let (n, g) := randNat s.g lo hi
  (n, { s with g })
def pick {α : Type} [Inhabited α] (xs : Array α) : GenM α := do return xs[← nat 0 (xs.size - 1)]!
def chance (pct : Nat) : GenM Bool := do return (← nat 0 99) < pct

def vals : Array Int64 := #[-9223372036854775808, -2, -1, 0, 1, 2, 3, 4611686018427387904,
  9223372036854775807]
def small : GenM Int64 := do return (← nat 0 6).toInt64
def anyVal : GenM Int64 := do if ← chance 12 then pick vals else (return (← nat 0 3).toInt64)
def optOf {α : Type} (x : GenM α) (pct : Nat := 50) : GenM (Option α) := do
  if ← chance pct then some <$> x else pure none

def genTriple : GenM TripleRow := do
  let tRet ← optOf small 25
  let rk ← nat 0 3
  pure { eid := (← nat 1 30).toInt64, s := ← anyVal, p := (← nat 0 3).toInt64, o := ← anyVal, tAdd := ← small,
         tRet, vFrom := ← optOf (pick #[0, 5, 10]) 40, vTo := ← optOf (pick #[5, 10, 20]) 40,
         retKind := if tRet.isSome then some rk.toInt64 else none }

def lexes : Array String := #["", "a", "b", "a\x00b", "é", "long literal value"]
def nums : Array (Option UInt64) := #[none, some 0x7FF8000000000000, some 0x8000000000000000, some 0,
  some (1.5 : Float).toBits, some 0x7FF0000000000000]

def genTerm : GenM TermRow := do
  pure { id := (← nat 1 6).toInt64, tag := (← nat 0 3).toInt64, lex := ← pick lexes,
         dt := ← pick #[none, some 0, some 7], lang := ← pick #[none, some "", some "en"],
         num := ← pick nums }

def genBound : GenM (Option Bound) := do
  match ← nat 0 3 with
  | 0 | 1 => pure none
  | 2 => return some (.incl (← anyVal))
  | _ => return some (.excl (← anyVal))

def fams : Array Family := #[.liveSpo, .livePos, .liveOsp, .histSpo, .histPos, .histOsp, .validP,
  .logAdd, .logRet]

def genView : GenM View := do
  let k ← nat 0 2
  let t ← small
  let tx := match k with
    | 0 => TxSel.now
    | 1 => TxSel.asOf t
    | _ => TxSel.history
  let valid ← if ← chance 30 then (return .at (← pick #[0, 5, 9, 10, 20])) else pure .unfiltered
  pure { tx, valid }

def genScan : GenM ReadOp := do
  let f ← pick fams
  let k ← if ← chance 50 then nat 0 (min 1 f.maxPrefix)
    else nat 0 (f.maxPrefix + (if ← chance 10 then 1 else 0))
  let mut pre := #[]
  for _ in [0:k] do pre := pre.push (← anyVal)
  let view ← if f.isLive && (← chance 85) then (return { (← genView) with tx := .now }) else genView
  let limit ← optOf (nat 1 3) 25
  pure (.scan { family := f, pre, lo := ← genBound, hi := ← genBound, view } limit)

def genRead : GenM ReadOp := do
  match ← nat 0 11 with
  | 0 | 1 | 2 => genScan
  | 3 => return .triple (← nat 0 31).toInt64
  | 4 => return .termById (← nat 0 7).toInt64
  | 5 => return .termByKey (← nat 0 3).toInt64 (← pick lexes) (← pick #[none, some 0, some 7])
                    (← pick #[none, some "", some "en"])
  | 6 => return .txByT (← nat 0 6).toInt64
  | 7 => return .txAtOrBefore (← pick #[-10, 0, 50, 100, 150, 250, 400])
  | 8 => return .counter (← pick #["next_stmt", "last_t", "x", "format_version"])
  | 9 => return .volatileGet (← nat 1 3).toInt64 (← nat 1 3).toInt64
  | 10 => return .volatileOf (← nat 1 3).toInt64
  | _ => return .predMulti (← nat 1 4).toInt64

def genData : GenM WriteOp := do
  let n ← nat 0 65
  if n < 22 then return .insertTriple (← genTriple)
  if n < 34 then return .retract (← nat 0 31).toInt64 (← small) (← nat 0 3).toInt64
  if n < 43 then return .insertTerm (← genTerm)
  if n < 49 then return .insertTx { t := (← nat 1 5).toInt64, instant := ← pick #[-5, 0, 100, 200, 300] }
  if n < 54 then return .setCounter (← pick #["next_stmt", "last_t", "x"]) (← anyVal)
  if n < 59 then
    return .volatilePut { s := (← nat 1 3).toInt64, key := (← nat 1 3).toInt64, value := ← anyVal,
                          updatedAt := ← small }
  if n < 62 then return .volatileDel (← nat 1 3).toInt64 (← nat 1 3).toInt64
  return .addPredMulti (← nat 1 4).toInt64

def genWrite : GenM WriteOp := do
  let inTx := (← get).inTx
  let n ← nat 0 99
  let op ← if !inTx then
      -- outside a transaction: mostly begin, sometimes misuse
      if n < 80 then pure .begin
      else if n < 90 then genData
      else pick #[.commit, .rollback, .savepoint "a", .rollbackTo "a", .release "a"]
    else
      if n < 70 then genData
      else if n < 73 then pure .begin
      else if n < 81 then pure .commit
      else if n < 84 then pure .rollback
      else if n < 92 then (return .savepoint (← pick #["a", "b", "c"]))
      else if n < 97 then (return .rollbackTo (← pick #["a", "b", "c"]))
      else (return .release (← pick #["a", "b", "c"]))
  match op with
  | .begin => modify ({ · with inTx := true })
  | .commit | .rollback => modify ({ · with inTx := false })
  | _ => pure ()
  return op

def genOp : GenM Op := do
  let n ← nat 0 99
  if n < 55 then return .write (← genWrite)
  if n < 75 then return .read (← genRead)
  if n < 81 then return .beginRead (← nat 0 2)
  if n < 86 then return .endRead (← nat 0 2)
  return .readOn (← nat 0 2) (← genRead)

def genOps (seed count : Nat) : Array Op := Id.run do
  let mut g : G := { g := mkStdGen seed }
  let mut out := #[]
  for _ in [0:count] do
    let (op, g') := genOp.run g
    out := out.push op
    g := g'
  return out

/-! ## Serialization of regression cases -/

def i64 (v : Int64) : Json := .int v.toInt
def optI (v : Option Int64) : Json := match v with | some x => i64 x | none => .null
def optS (v : Option String) : Json := match v with | some x => .str x | none => .null
def optU (v : Option UInt64) : Json := match v with | some x => .int x.toNat | none => .null
def boundJ : Option Bound → Json
  | none => .null
  | some (.incl v) => .arr #[.str "incl", i64 v]
  | some (.excl v) => .arr #[.str "excl", i64 v]
def famName (f : Family) : String := reprStr f |>.replace "Tiramemsu.Store.Family." ""
def viewJ (v : View) : Json :=
  .obj #[("tx", match v.tx with | .now => .str "now" | .history => .str "history" | .asOf t => i64 t),
         ("valid", match v.valid with | .unfiltered => .null | .at d => i64 d)]
def tripleJ (r : TripleRow) : Json :=
  .arr #[i64 r.eid, i64 r.s, i64 r.p, i64 r.o, i64 r.tAdd, optI r.tRet, optI r.vFrom, optI r.vTo, optI r.retKind]

def readJ : ReadOp → Json
  | .scan sp l => .arr #[.str "scan", .str (famName sp.family), .arr (sp.pre.map i64), boundJ sp.lo,
      boundJ sp.hi, viewJ sp.view, match l with | some n => .int n | none => .null]
  | .triple e => .arr #[.str "triple", i64 e]
  | .termById i => .arr #[.str "termById", i64 i]
  | .termByKey t l d g => .arr #[.str "termByKey", i64 t, .str l, optI d, optS g]
  | .txByT t => .arr #[.str "txByT", i64 t]
  | .txAtOrBefore i => .arr #[.str "txAtOrBefore", i64 i]
  | .counter c => .arr #[.str "counter", .str c]
  | .volatileGet s k => .arr #[.str "volatileGet", i64 s, i64 k]
  | .volatileOf s => .arr #[.str "volatileOf", i64 s]
  | .predMulti p => .arr #[.str "predMulti", i64 p]

def writeJ : WriteOp → Json
  | .insertTriple r => .arr #[.str "insertTriple", tripleJ r]
  | .retract e t k => .arr #[.str "retract", i64 e, i64 t, i64 k]
  | .insertTerm r => .arr #[.str "insertTerm", i64 r.id, i64 r.tag, .str r.lex, optI r.dt, optS r.lang, optU r.num]
  | .insertTx r => .arr #[.str "insertTx", i64 r.t, i64 r.instant]
  | .setCounter n v => .arr #[.str "setCounter", .str n, i64 v]
  | .volatilePut r => .arr #[.str "volatilePut", i64 r.s, i64 r.key, i64 r.value, i64 r.updatedAt]
  | .volatileDel s k => .arr #[.str "volatileDel", i64 s, i64 k]
  | .addPredMulti p => .arr #[.str "addPredMulti", i64 p]
  | .begin => .arr #[.str "begin"]
  | .commit => .arr #[.str "commit"]
  | .rollback => .arr #[.str "rollback"]
  | .savepoint n => .arr #[.str "savepoint", .str n]
  | .rollbackTo n => .arr #[.str "rollbackTo", .str n]
  | .release n => .arr #[.str "release", .str n]

def opJ : Op → Json
  | .write w => .obj #[("write", writeJ w)]
  | .read q => .obj #[("read", readJ q)]
  | .beginRead i => .obj #[("beginRead", .int i)]
  | .endRead i => .obj #[("endRead", .int i)]
  | .readOn i q => .obj #[("readOn", .arr #[.int i, readJ q])]

def jI : Json → Except String Int64
  | .int i => pure (Int64.ofInt i)
  | j => throw s!"expected an integer, got {j}"
def jOI : Json → Except String (Option Int64)
  | .null => pure none
  | j => some <$> jI j
def jS : Json → Except String String
  | .str s => pure s
  | j => throw s!"expected a string, got {j}"
def jOS : Json → Except String (Option String)
  | .null => pure none
  | j => some <$> jS j
def jOU : Json → Except String (Option UInt64)
  | .null => pure none
  | .int i => pure (some (UInt64.ofNat i.toNat))
  | j => throw s!"expected bits, got {j}"
def jBound : Json → Except String (Option Bound)
  | .null => pure none
  | .arr #[.str "incl", v] => do return some (.incl (← jI v))
  | .arr #[.str "excl", v] => do return some (.excl (← jI v))
  | j => throw s!"bad bound {j}"
def jFam (s : String) : Except String Family :=
  match fams.find? (famName · == s) with
  | some f => pure f
  | none => throw s!"bad family {s}"
def jView (j : Json) : Except String View := do
  let tx ← match j.get? "tx" with
    | some (.str "now") => pure TxSel.now
    | some (.str "history") => pure .history
    | some v => .asOf <$> jI v
    | none => throw "bad view"
  let valid ← match j.get? "valid" with
    | some .null | none => pure ValidSel.unfiltered
    | some v => .at <$> jI v
  pure { tx, valid }
def jTriple : Json → Except String TripleRow
  | .arr #[e, s, p, o, a, r, f, t, k] => do
    pure { eid := ← jI e, s := ← jI s, p := ← jI p, o := ← jI o, tAdd := ← jI a, tRet := ← jOI r,
           vFrom := ← jOI f, vTo := ← jOI t, retKind := ← jOI k }
  | j => throw s!"bad triple {j}"

def jRead : Json → Except String ReadOp
  | .arr #[.str "scan", .str f, .arr pre, lo, hi, v, l] => do
    pure (.scan { family := ← jFam f, pre := ← pre.mapM jI, lo := ← jBound lo, hi := ← jBound hi,
                  view := ← jView v } (match l with | .int n => some n.toNat | _ => none))
  | .arr #[.str "triple", e] => .triple <$> jI e
  | .arr #[.str "termById", i] => .termById <$> jI i
  | .arr #[.str "termByKey", t, l, d, g] => do return .termByKey (← jI t) (← jS l) (← jOI d) (← jOS g)
  | .arr #[.str "txByT", t] => .txByT <$> jI t
  | .arr #[.str "txAtOrBefore", i] => .txAtOrBefore <$> jI i
  | .arr #[.str "counter", c] => .counter <$> jS c
  | .arr #[.str "volatileGet", s, k] => do return .volatileGet (← jI s) (← jI k)
  | .arr #[.str "volatileOf", s] => .volatileOf <$> jI s
  | .arr #[.str "predMulti", p] => .predMulti <$> jI p
  | j => throw s!"bad read {j}"

def jWrite : Json → Except String WriteOp
  | .arr #[.str "insertTriple", r] => .insertTriple <$> jTriple r
  | .arr #[.str "retract", e, t, k] => do return .retract (← jI e) (← jI t) (← jI k)
  | .arr #[.str "insertTerm", i, t, l, d, g, n] => do
    return .insertTerm { id := ← jI i, tag := ← jI t, lex := ← jS l, dt := ← jOI d, lang := ← jOS g, num := ← jOU n }
  | .arr #[.str "insertTx", t, i] => do return .insertTx { t := ← jI t, instant := ← jI i }
  | .arr #[.str "setCounter", n, v] => do return .setCounter (← jS n) (← jI v)
  | .arr #[.str "volatilePut", s, k, v, u] => do
    return .volatilePut { s := ← jI s, key := ← jI k, value := ← jI v, updatedAt := ← jI u }
  | .arr #[.str "volatileDel", s, k] => do return .volatileDel (← jI s) (← jI k)
  | .arr #[.str "addPredMulti", p] => .addPredMulti <$> jI p
  | .arr #[.str "begin"] => pure .begin
  | .arr #[.str "commit"] => pure .commit
  | .arr #[.str "rollback"] => pure .rollback
  | .arr #[.str "savepoint", n] => .savepoint <$> jS n
  | .arr #[.str "rollbackTo", n] => .rollbackTo <$> jS n
  | .arr #[.str "release", n] => .release <$> jS n
  | j => throw s!"bad write {j}"

def jOp (j : Json) : Except String Op :=
  match j with
  | .obj #[("write", w)] => .write <$> jWrite w
  | .obj #[("read", q)] => .read <$> jRead q
  | .obj #[("beginRead", .int i)] => pure (.beginRead i.toNat)
  | .obj #[("endRead", .int i)] => pure (.endRead i.toNat)
  | .obj #[("readOn", .arr #[.int i, q])] => .readOn i.toNat <$> jRead q
  | j => throw s!"bad op {j}"

/-! ## Minimization -/

/-- Delta debugging (ddmin): a 1-minimal subsequence on which `fails` still holds. -/
partial def ddmin (fails : Array Op → IO Bool) (ops : Array Op) (n : Nat := 2) : IO (Array Op) := do
  if ops.size < 2 then return ops
  let size := (ops.size + n - 1) / n
  let chunks := (List.range n).filterMap fun i =>
    let c := ops.extract (i * size) ((i + 1) * size)
    if c.isEmpty then none else some (i, c)
  for (_, c) in chunks do
    if ← fails c then return ← ddmin fails c 2
  for (i, _) in chunks do
    let rest := ops.extract 0 (i * size) ++ ops.extract ((i + 1) * size) ops.size
    if ← fails rest then return ← ddmin fails rest (max (n - 1) 2)
  if n < ops.size then ddmin fails ops (min (2 * n) ops.size) else return ops

/-! ## Runner -/

structure Setup where
  /-- The database file both stores start from (copied for each run). -/
  initFile : System.FilePath
  init : ModelState
  /-- `fresh` for the schema fixture, otherwise the start file given on the command line. -/
  label : String := "fresh"

def Setup.ofFile (f : System.FilePath) (label : String := "fresh") : IO Setup := do
  match ← (loadModelState f).run with
  | .ok init => pure { initFile := f, init, label }
  | .error e => throw (IO.userError s!"cannot load {f}: {e}")

/-- A setup for a start label: `fresh`, or a start file (copied to a pristine scratch file). -/
def Setup.ofLabel (label : String) : IO (Option Setup) := do
  let src ← if label == "fresh" then freshFormat1 "refine-start"
    else if ← (label : System.FilePath).pathExists then pure (label : System.FilePath)
    else return none
  let pristine := (← scratchDir) / s!"refine-pristine-{hash label}.db"
  copyDb src pristine
  some <$> Setup.ofFile pristine label

/-- Runs a sequence on both stores; the first divergence, if any. -/
def diverges (s : Setup) (ops : Array Op) (fault : Op → Res → Res := fun _ r => r) :
    IO (Option (Nat × Res × Res)) := do
  let a := runModel s.init ops
  let b ← runSqlite s.initFile ops fault
  return (firstDiff a b).map fun i => (i, a[i]?.getD .skip, b[i]?.getD .skip)

def regressionDir : System.FilePath := "testdata" / "refine"

/-- Minimizes a failing sequence and writes it as a regression case. -/
def recordFailure (s : Setup) (dir : System.FilePath) (label : String) (seed : Option Nat)
    (ops : Array Op) (fault : Op → Res → Res := fun _ r => r) : IO (Array Op) := do
  let min ← ddmin (fun xs => return (← diverges s xs fault).isSome) ops
  IO.FS.createDirAll dir
  let file := dir / s!"{label}.json"
  let j := Json.obj #[("seed", match seed with | some n => .int n | none => .null),
    ("start", .str s.label), ("ops", .arr (min.map opJ))]
  IO.FS.writeFile file (j.compress ++ "\n")
  IO.eprintln s!"  minimized to {min.size} op(s), written to {file}:"
  for op in min do IO.eprintln s!"    {(opJ op).compress}"
  return min

/-- Replays every regression case on the start it was found on. -/
def replay : IO Nat := do
  if !(← regressionDir.isDir) then return 0
  let mut failures := 0
  for e in ← regressionDir.readDir do
    unless e.path.extension == some "json" do continue
    let j ← match Json.parse (← IO.FS.readFile e.path) with
      | .ok j => pure j
      | .error err => throw (IO.userError s!"{e.path}: {err}")
    let ops ← match ((j.getArr? "ops").getD #[]).mapM jOp with
      | .ok ops => pure ops
      | .error err => throw (IO.userError s!"{e.path}: {err}")
    let label := (j.getStr? "start").getD "fresh"
    let some s ← Setup.ofLabel label
      | IO.println s!"  regression {e.fileName}: start {label} not available, skipped"
    if let some (i, a, b) ← diverges s ops then
      failures := failures + 1
      IO.eprintln s!"FAIL regression {e.fileName}: op {i}: model {reprStr a}, sqlite {reprStr b}"
  return failures

def flagNat (args : List String) (name : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

/-- The self-test of the machinery: an injected fault in the SQLite results must be found,
minimized and recorded (outside `testdata/refine`). -/
def selfTest (s : Setup) : IO UInt32 := do
  let fault (op : Op) (r : Res) : Res := match op, r with
    | .read (.predMulti _), .bool b => .bool (!b)
    | _, r => r
  let ops := genOps 42 300
  match ← diverges s ops fault with
  | none => IO.eprintln "FAIL refine self-test: injected fault not detected"; return 1
  | some (i, _, _) =>
    let dir ← (do let d := (← scratchDir) / "refine-selftest"; pure d)
    let min ← recordFailure s dir "selftest" (some 42) ops fault
    let file := dir / "selftest.json"
    let back ← match Json.parse (← IO.FS.readFile file) >>= fun j => ((j.getArr? "ops").getD #[]).mapM jOp with
      | .ok ops => pure ops
      | .error e => IO.eprintln s!"FAIL refine self-test: {e}"; return 1
    let roundTrip := (back.map opJ).map (·.compress) == (min.map opJ).map (·.compress)
    let ok := min.size ≤ 2 && roundTrip && (← diverges s back fault).isSome
    IO.println s!"refine self-test: fault found at op {i}, minimized to {min.size} op(s), case round-trips: {roundTrip}"
    return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  let startLabel := match args.dropWhile (· != "--start") with
    | _ :: f :: _ => f
    | _ => "fresh"
  let some setup ← Setup.ofLabel startLabel
    | IO.eprintln s!"refine: start file {startLabel} not found"; return 2
  let startFile := startLabel
  if args.contains "--self-test" then return ← selfTest setup
  if args.contains "--stats" then
    -- distribution of result kinds on one seed, to show what the generator exercises
    let ops := genOps (flagNat args "--first-seed" 1) (flagNat args "--ops" 300)
    let res := runModel setup.init ops
    let sq ← runSqlite setup.initFile ops
    let kind : Res → String
      | .rows xs => if xs.isEmpty then "rows (empty)" else "rows (non-empty)"
      | .err k => s!"err {k}"
      | .unit => "unit" | .skip => "skip"
      | .bool b => s!"bool {b}"
      | r => if reprStr r |>.endsWith "none" then "absent" else "present"
    let mut counts : Std.HashMap String Nat := {}
    for r in res do counts := counts.insert (kind r) (counts.getD (kind r) 0 + 1)
    for (k, n) in counts.toList.mergeSort (fun a b => a.1 ≤ b.1) do IO.println s!"  {k}: {n}"
    IO.println s!"  identical on SQLite: {res == sq}"
    return 0
  let seeds := flagNat args "--seeds" 200
  let count := flagNat args "--ops" 300
  let first := flagNat args "--first-seed" 1
  let regressions ← replay
  let mut failures := regressions
  let mut opsRun := 0
  for seed in [first:first + seeds] do
    let ops := genOps seed count
    opsRun := opsRun + ops.size
    if let some (i, a, b) ← diverges setup ops then
      failures := failures + 1
      IO.eprintln s!"FAIL seed {seed}: op {i} {(opJ ops[i]!).compress}: model {reprStr a}, sqlite {reprStr b}"
      let _ ← recordFailure setup regressionDir s!"seed-{seed}" (some seed) ops
  IO.println s!"refine: {seeds} seed(s) × {count} ops from {startFile} ({opsRun} ops), {failures} failure(s)"
  return if failures == 0 then 0 else 1

end Test.Refine
