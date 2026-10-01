/-
The transaction cores, generic over the store: commit (`transactCore`), dry run and
speculation (`speculativeCore`), following Rust's `Store::transact` and `run_speculative`.

- A transaction takes `t = last_t + 1` and `instant = max(now, last_instant + 1)`, where `now`
  is read from the clock after `BEGIN IMMEDIATE` and the counters, inserts its
  `tx` row, runs the body, then writes `last_t` and `last_instant` and commits. Any failure rolls
  everything back.
- A dry run or speculation does the same inside the savepoint `spec`, runs its follow-up (the
  report, or a query on the writer), rolls the savepoint back and burns the id counters the
  body advanced, in a commit of its own (or in a separate transaction if that fails).

Instants are integers in the core; one outside the signed 64-bit range fails with a store
error before anything is written (listed deviation: Rust overflows).
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Exec

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Transactions]]

/-- The instant of the next transaction: the clock reading, or one past the previous instant. -/
def nextInstant (prev now : Int) : Int := max now (prev + 1)

/-- The signed 64-bit range. -/
def inInt64 (x : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ x) && decide (x < 2 ^ 63)

/-- The report as returned: `existing` without duplicates and without eids the transaction
inserted (Rust's `Tx::report`). -/
def TxReport.finish (r : TxReport) : TxReport :=
  let ex := r.existing.foldl (init := #[]) fun acc e =>
    if r.asserted.contains e || acc.contains e then acc else acc.push e
  { r with existing := ex }

/-- The counters a transaction reads at its start. -/
structure Counters where
  nextTerm : Int64
  nextNode : Int64
  nextBNode : Int64
  nextStmt : Int64
  lastT : Int64
  lastInstant : Int64
  multiVersion : Int64
  deriving Repr, DecidableEq, Inhabited

/-- The id counters a speculation burns. -/
def idCounterNames : List String := ["next_term", "next_node", "next_bnode", "next_stmt"]

section
variable {m : Type → Type} [Monad m] [MonadExceptOf StoreError m] [WriteStore m] [TermBackend m]

/-- Reads every counter; `InvalidTerm` when one is missing (Rust's `Counters::load`). -/
def loadCounters : m (Except Error Counters) := do
  let get (n : String) : m (Option Int64) := ReadStore.counter (m := m) n
  match ← get "next_term", ← get "next_node", ← get "next_bnode", ← get "next_stmt",
      ← get "last_t", ← get "last_instant", ← get "multi_version" with
  | some a, some b, some c, some d, some e, some f, some g => pure (.ok ⟨a, b, c, d, e, f, g⟩)
  | _, _, _, _, _, _, _ => pure (.error (.invalidTerm .value "meta table is missing counters"))

/-- Starts a body: the transaction number and instant, and the `tx` row. -/
def beginBody (clock : m Int) (opts : TxOptions) (c0 : Counters) : m (Except Error TxCtx) := do
  let t := c0.lastT.toInt + 1
  if !(0 ≤ t ∧ t ≤ (counterMax : Int)) then return .error (.idSpaceExhausted .tx)
  let now ← clock
  let inst := nextInstant c0.lastInstant.toInt now
  if !inInt64 inst then throw (StoreError.misuse s!"instant {inst} is outside the 64-bit range")
  WriteStore.insertTx (m := m) { t := Int64.ofInt t, instant := Int64.ofInt inst }
  let t := Int64.ofInt t
  let inst := Int64.ofInt inst
  pure (.ok { t, instant := inst, opts, report := { t, instant := inst } })

/-- Runs a body program on the store. -/
def runBody {α : Type} (ctx : TxCtx) (body : EngM α) : m (Except Error (α × TxCtx)) :=
  SProg.interp Op.run ((body.run ctx).run)

/-- Rolls back, ignoring a failure (the store may already have rolled back). -/
def rollbackQuiet : m Unit :=
  tryCatchThe StoreError (WriteStore.rollback (m := m)) fun _ => pure ()

/-- Begins a write transaction; the store error when it cannot. -/
def tryBegin : m (Option StoreError) :=
  tryCatchThe StoreError (do WriteStore.begin (m := m); pure none) fun e => pure (some e)

/-- One transaction: commits the body's effects, or leaves no trace on any failure. -/
def transactCore {α : Type} (clock : m Int) (opts : TxOptions) (body : EngM α) :
    m (Except Error (α × TxReport)) := do
  if let some e ← tryBegin (m := m) then return .error (.store e)
  tryCatchThe StoreError
    (do
      match ← loadCounters (m := m) with
      | .error e => rollbackQuiet (m := m); pure (.error e)
      | .ok c0 =>
        match ← beginBody clock opts c0 with
        | .error e => rollbackQuiet (m := m); pure (.error e)
        | .ok ctx0 =>
          match ← runBody ctx0 body with
          | .error e => rollbackQuiet (m := m); pure (.error e)
          | .ok (a, ctx) =>
            -- the number and instant are the transaction's, whatever the body did to its context
            WriteStore.setCounter (m := m) "last_t" ctx0.t
            WriteStore.setCounter (m := m) "last_instant" ctx0.instant
            WriteStore.commit (m := m)
            pure (.ok (a, { ctx.report with t := ctx0.t, instant := ctx0.instant }.finish)))
    fun e => do rollbackQuiet (m := m); pure (.error (.store e))

/-- The current id counters (to burn). -/
def readIdCounters : m (List (String × Int64)) := do
  let a ← ReadStore.counter (m := m) "next_term"
  let b ← ReadStore.counter (m := m) "next_node"
  let c ← ReadStore.counter (m := m) "next_bnode"
  let d ← ReadStore.counter (m := m) "next_stmt"
  pure ([("next_term", a), ("next_node", b), ("next_bnode", c), ("next_stmt", d)].filterMap
    fun (n, v) => v.map (n, ·))

/-- The value of a named counter in a list. -/
def counterIn (cs : List (String × Int64)) (n : String) : Option Int64 :=
  (cs.find? (·.1 == n)).map (·.2)

/-- Raises the id counters to `c1` where they are below it. -/
def burnIds : List (String × Int64) → m Unit
  | [] => pure ()
  | (n, v) :: rest => do
    match ← ReadStore.counter (m := m) n with
    | some cur => if cur.toInt < v.toInt then WriteStore.setCounter (m := m) n v
    | none => pure ()
    burnIds rest

/-- Burns ids in a transaction of its own (after a failed speculative commit). -/
def burnAfterFailure (c1 : List (String × Int64)) : m Unit :=
  tryCatchThe StoreError
    (do
      WriteStore.begin (m := m)
      tryCatchThe StoreError (do burnIds c1; WriteStore.commit (m := m))
        fun _ => rollbackQuiet (m := m))
    fun _ => pure ()

/-- A dry run or speculation: the body inside the savepoint `spec`, then `after` on the
speculative state; then everything is rolled back and the advanced id counters are burned. -/
def speculativeCore {α β : Type} (clock : m Int) (opts : TxOptions) (body : EngM α)
    (after : TxCtx → α → m (Except Error β)) : m (Except Error β) := do
  if let some e ← tryBegin (m := m) then return .error (.store e)
  tryCatchThe StoreError
    (do
      WriteStore.savepoint (m := m) "spec"
      let (res, c1) ← (do
        match ← loadCounters (m := m) with
        | .error e => pure (Except.error e, none)
        | .ok c0 =>
          match ← beginBody clock opts c0 with
          | .error e => pure (.error e, none)
          | .ok ctx0 =>
            let r ← match ← runBody ctx0 body with
              | .error e => pure (Except.error e)
              | .ok (a, ctx) =>
                after { ctx with t := ctx0.t, instant := ctx0.instant,
                                 report := { ctx.report with t := ctx0.t, instant := ctx0.instant } } a
            pure (r, some (← readIdCounters (m := m))))
      let ok ← tryCatchThe StoreError
        (do
          WriteStore.rollbackTo (m := m) "spec"
          WriteStore.release (m := m) "spec"
          if let some c1 := c1 then burnIds c1
          WriteStore.commit (m := m)
          pure true)
        fun _ => pure false
      if !ok then
        rollbackQuiet (m := m)
        if let some c1 := c1 then burnAfterFailure c1
      pure res)
    fun e => do rollbackQuiet (m := m); pure (.error (.store e))

/-- A dry run: the report a commit would return, with every effect discarded. -/
def dryRunCore {α : Type} (clock : m Int) (opts : TxOptions) (body : EngM α) :
    m (Except Error (α × TxReport)) :=
  speculativeCore clock opts body fun ctx a => pure (.ok (a, ctx.report.finish))

/-- A read program on the store the monad reaches (the writer, inside a transaction). -/
def runReads {α : Type} (p : RProg α) : m α := RProg.interp ROp.run p

/-- The view of a speculative query: now, optionally filtered by valid time. -/
def specView (validAt : Option Int64) : View.ViewSpec :=
  match validAt with
  | some d => { valid := .at d }
  | none => {}

/-- A speculation: the body, then the query on the uncommitted state (now view, optionally
filtered by valid time); the query is not run when the body fails. -/
def speculateCore {α β : Type} (clock : m Int) (body : EngM α) (validAt : Option Int64)
    (query : ReadProg β) : m (Except Error β) :=
  speculativeCore clock {} body fun _ _ => runReads (ReadProg.run (specView validAt) query)

end

end Tiramemsu.Engine
