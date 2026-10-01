/-
The engine's store primitives and the two free monads built on them.

- `ROp`: one read of the store (scan, point reads, counters, dictionary lookups).
  `RProg` is the free monad over reads: every view read is an `RProg`, run on a snapshot
  reader, on the writer, or on a model state.
- `Op`: a read, or one of the guarded writes a transaction body may perform (id allocation,
  statement insert, retraction, term intern, volatile rows, multi-eid bookkeeping).
  `SProg` is the free monad over `Op`: the engine's verbs are `SProg` programs.

Begin, commit, rollback, savepoints, the `tx` row and the `last_t`/`last_instant` counters are
not operations: only the transaction cores (`Engine.Transact`) use them. So no body can touch
them, and the never-forget invariant is proven once per operation and then for every program
by induction on `SProg`.

Each write checks its own guard (`rowGuard`) before writing, so the invariant holds whatever
the arguments are; the engine's pipeline reports user errors before a guard can fail.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Interval
import Tiramemsu.Engine.Vocab
import Tiramemsu.Term.Backend

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Store Operations]]

/-! ## Reads -/

/-- One read of the store. -/
inductive ROp where
  /-- Every row of a scan, in the family's key order. -/
  | scan (sp : ScanSpec)
  | triple (eid : Int64)
  | counter (name : String)
  | txByT (t : Int64)
  | txAtOrBefore (instant : Int64)
  | volatileGet (s key : Int64)
  | predMulti (p : Int64)
  | lookupKey (k : TermKey)
  | rowById (i : Nat)
  deriving Repr, Inhabited

/-- The result type of a read. -/
@[reducible] def ROp.Res : ROp → Type
  | .scan _ => Array TripleRow
  | .triple _ => Option TripleRow
  | .counter _ => Option Int64
  | .txByT _ => Option TxRow
  | .txAtOrBefore _ => Option TxRow
  | .volatileGet .. => Option VolatileRow
  | .predMulti _ => Bool
  | .lookupKey _ => Option Nat
  | .rowById _ => Option Row

/-- A read program: the free monad over `ROp`. -/
inductive RProg (α : Type) where
  | pure (a : α)
  | read (r : ROp) (k : r.Res → RProg α)

namespace RProg

def bind {α β : Type} : RProg α → (α → RProg β) → RProg β
  | .pure a, f => f a
  | .read r k, f => .read r fun x => bind (k x) f

instance : Monad RProg where
  pure := .pure
  bind := bind

/-- One read as a program. -/
def lift (r : ROp) : RProg r.Res := .read r .pure

/-- Runs a read program in any monad, given the meaning of each read. -/
def interp {m : Type → Type} [Monad m] {α : Type} (h : (r : ROp) → m r.Res) : RProg α → m α
  | .pure a => Pure.pure a
  | .read r k => h r >>= fun x => interp h (k x)

/-- Runs a read program on a pure state, given the pure meaning of each read. -/
def runPure {σ α : Type} (h : (r : ROp) → σ → Except StoreError r.Res) (s : σ) :
    RProg α → Except StoreError α
  | .pure a => .ok a
  | .read r k =>
    match h r s with
    | .ok x => runPure h s (k x)
    | .error e => .error e

end RProg

/-! ## Body operations -/

/-- The id counters a body may advance. -/
inductive IdCounter where
  | node
  | bnode
  | stmt
  deriving Repr, DecidableEq, Inhabited

def IdCounter.name : IdCounter → String
  | .node => "next_node" | .bnode => "next_bnode" | .stmt => "next_stmt"

def IdCounter.allocTag : IdCounter → AllocTag
  | .node => .node | .bnode => .bnode | .stmt => .stmt

/-- A statement to insert: the store adds `t_add` (the current transaction). -/
structure NewRow where
  eid : Int64
  s : Int64
  p : Int64
  o : Int64
  vFrom : Option Int64 := none
  vTo : Option Int64 := none
  deriving Repr, DecidableEq, Inhabited

/-- One operation of a transaction body. -/
inductive Op where
  | read (r : ROp)
  /-- Takes the next number of an id counter (`IdSpaceExhausted` past `2^48 − 1`). -/
  | alloc (c : IdCounter)
  /-- Inserts a statement after checking its guard. -/
  | insert (r : NewRow)
  /-- Retracts a live statement at the current transaction; `false` when not live. -/
  | retract (eid : Int64) (kind : RetKind)
  /-- Lookup-or-insert of a dictionary key. -/
  | intern (k : TermKey) (num : Option UInt64)
  | volPut (r : VolatileRow)
  | volDel (s key : Int64)
  /-- Records a multi-eid predicate (adds it to `pred_multi` and bumps `multi_version` when
  absent). -/
  | markMulti (p : Int64)
  deriving Repr, Inhabited

/-- The result type of an operation. -/
@[reducible] def Op.Res : Op → Type
  | .read r => r.Res
  | .alloc _ => Except CodecError ObjectId
  | .insert _ => Unit
  | .retract .. => Bool
  | .intern .. => Except CodecError Nat
  | .volPut _ => Unit
  | .volDel .. => Unit
  | .markMulti _ => Unit

/-- A body program: the free monad over `Op`. -/
inductive SProg (α : Type) where
  | pure (a : α)
  | op (o : Op) (k : o.Res → SProg α)

namespace SProg

def bind {α β : Type} : SProg α → (α → SProg β) → SProg β
  | .pure a, f => f a
  | .op o k, f => .op o fun x => bind (k x) f

instance : Monad SProg where
  pure := .pure
  bind := bind

/-- One operation as a program. -/
def lift (o : Op) : SProg o.Res := .op o .pure

/-- Runs a body program in any monad, given the meaning of each operation. -/
def interp {m : Type → Type} [Monad m] {α : Type} (h : (o : Op) → m o.Res) : SProg α → m α
  | .pure a => Pure.pure a
  | .op o k => h o >>= fun x => interp h (k x)

end SProg

/-- A read program as a body program. -/
def RProg.toS {α : Type} : RProg α → SProg α
  | .pure a => .pure a
  | .read r k => .op (.read r) fun x => RProg.toS (k x)

instance : MonadLift RProg SProg := ⟨RProg.toS⟩

/-! ## The guard of an insert -/

/-- The tag number of a raw id (its low 4 bits, as an integer). -/
def rawTag (x : Int64) : Int := x.toInt % 16

/-- The counter of a raw `STMT` id. -/
def eidCtr (x : Int64) : Int := x.toInt / 16

/-- The checks every inserted statement passes, against the `next_stmt` counter at the start of
the transaction (`base`) and now (`next`): its eid is a `STMT` id allocated in this
transaction; the subject is subject-capable; the predicate an `IRI`; the interval nonempty;
neither subject nor object is its own eid. -/
def rowGuard (r : NewRow) (base next : Int64) : Bool :=
  rawTag r.eid == 3 && decide (base.toInt ≤ eidCtr r.eid) && decide (eidCtr r.eid < next.toInt) &&
  decide (0 ≤ rawTag r.s) && decide (rawTag r.s ≤ 4) && rawTag r.p == 0 &&
  (Valid.nonempty ⟨r.vFrom, r.vTo⟩) && r.s != r.eid && r.o != r.eid

/-- The largest `last_t` a body may run under (so that `last_t + 1` fits a counter). -/
def lastTLimit : Int := 2 ^ 48 - 1

/-! ## Meaning of reads and operations on a store -/

section
variable {m : Type → Type} [Monad m]

/-- Every row of a scan. -/
def scanAll [ReadStore m] (sp : ScanSpec) : m (Array TripleRow) :=
  ReadStore.scan sp #[] fun acc r => pure (.yield (acc.push r))

/-- A read on a store. -/
def ROp.run [ReadStore m] [TermReader m] : (r : ROp) → m r.Res
  | .scan sp => scanAll sp
  | .triple e => ReadStore.triple e
  | .counter n => ReadStore.counter n
  | .txByT t => ReadStore.txByT t
  | .txAtOrBefore i => ReadStore.txAtOrBefore i
  | .volatileGet s k => ReadStore.volatileGet s k
  | .predMulti p => ReadStore.predMulti p
  | .lookupKey k => TermReader.lookupKey k
  | .rowById i => TermReader.rowById i

variable [MonadExceptOf StoreError m] [WriteStore m] [TermBackend m]

/-- A counter that must exist. -/
def needCounter (n : String) : m Int64 := do
  match ← ReadStore.counter (m := m) n with
  | some v => pure v
  | none => throw (StoreError.misuse s!"meta table is missing counter {n}")

/-- A base counter that must exist. -/
def needBase (n : String) : m Int64 := do
  match ← WriteStore.baseCounter (m := m) n with
  | some v => pure v
  | none => throw (StoreError.misuse s!"meta table is missing counter {n}")

/-- Takes the next number of an id counter. -/
def allocRun (c : IdCounter) : m (Except CodecError ObjectId) := do
  let n ← needCounter (m := m) c.name
  if 0 ≤ n.toInt ∧ n.toInt ≤ (counterMax : Int) then
    WriteStore.setCounter (m := m) c.name (n + 1)
    pure (.ok (mkAlloc c.allocTag 0 n.toUInt64))
  else pure (.error (.idSpaceExhausted c.allocTag.kind))

/-- The guarded insert, with `t_add` the current transaction (`last_t + 1` at its start). -/
def insertRun (r : NewRow) : m Unit := do
  let lastT ← needBase (m := m) "last_t"
  let base ← needBase (m := m) "next_stmt"
  let next ← needCounter (m := m) "next_stmt"
  if 0 ≤ lastT.toInt ∧ lastT.toInt < lastTLimit ∧ rowGuard r base next then
    WriteStore.insertTriple (m := m)
      { eid := r.eid, s := r.s, p := r.p, o := r.o, tAdd := lastT + 1, vFrom := r.vFrom, vTo := r.vTo }
  else throw (StoreError.misuse "engine guard: statement rejected")

/-- Retracts a live statement at the current transaction. -/
def retractRun (e : Int64) (k : RetKind) : m Bool := do
  let lastT ← needBase (m := m) "last_t"
  if 0 ≤ lastT.toInt ∧ lastT.toInt < lastTLimit then
    match ← ReadStore.triple (m := m) e with
    | some r =>
      if r.tRet.isNone then
        WriteStore.retract (m := m) e (lastT + 1) k.code
        pure true
      else pure false
    | none => pure false
  else throw (StoreError.misuse "engine guard: retraction rejected")

/-- Records a multi-eid predicate. -/
def markMultiRun (p : Int64) : m Unit := do
  if !(← ReadStore.predMulti (m := m) p) then
    WriteStore.addPredMulti (m := m) p
    let v ← needCounter (m := m) "multi_version"
    WriteStore.setCounter (m := m) "multi_version" (v + 1)

/-- An operation on a store. -/
def Op.run : (o : Op) → m o.Res
  | .read r => ROp.run r
  | .alloc c => allocRun c
  | .insert r => insertRun r
  | .retract e k => retractRun e k
  | .intern k num => internKey k num
  | .volPut r => WriteStore.volatilePut r
  | .volDel s k => WriteStore.volatileDel s k
  | .markMulti p => markMultiRun p

end

/-! ## The model store -/

/-- A body program on the model store (tail-recursive). -/
def SProg.runModel {α : Type} : SProg α → ModelStore → Except StoreError (α × ModelStore)
  | .pure a, s => .ok (a, s)
  | .op o k, s =>
    match (Op.run o : ModelM o.Res) s with
    | .ok (x, s') => SProg.runModel (k x) s'
    | .error e => .error e

/-- A read on a model state. -/
def ROp.model (r : ROp) (st : ModelState) : Except StoreError r.Res :=
  match (ROp.run r : SnapM r.Res) st with
  | .ok x => .ok x
  | .error e => .error e

/-- A read program on a model state. -/
def RProg.onModel {α : Type} (st : ModelState) (p : RProg α) : Except StoreError α :=
  RProg.runPure ROp.model st p

end Tiramemsu.Engine
