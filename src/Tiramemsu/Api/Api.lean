/-
The public Lean API (Rust facade `tiramemsu::{Db, View, Tx}`): opening a database, transactions
and speculation, views and their reads, IR execution (validated before any read, one snapshot,
optional provenance), paths, fact bundles and explain. Errors carry Rust's variant names.
Shell module (unverified): it only composes the verified core with the connection pool.
-/
import Tiramemsu.Shell.Db
import Tiramemsu.Shell.BundleJson
import Tiramemsu.Exec.Explain
import Tiramemsu.Prov.EvalProv

namespace Tiramemsu.Api

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.Engine Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Exec
open Tiramemsu.Shell Tiramemsu.Bundle Tiramemsu.Json

--# @lat: [[query#Lean API]]

/-- Open options (Rust `OpenOptions`), with Rust's defaults. -/
structure OpenOptions where
  readers : Nat := 4
  clock : Clock := systemClock
  busyTimeoutMs : Nat := 5000
  termCacheCapacity : Nat := 16384
  optimizeEvery : Nat := 1000
  pathMaxHops : Nat := 15
  pathMaxStates : Nat := 1000000

/-- Every failure of the API, with Rust's variant names (`code`). -/
inductive ApiError where
  | engine (e : Engine.Error)
  | query (e : QError)
  | open_ (e : Storage.OpenError)
  | io (msg : String)

def ApiError.code : ApiError → String
  | .engine e => e.code
  | .query e => e.code
  | .open_ e => e.code
  | .io _ => "Custom"

def ApiError.message : ApiError → String
  | .engine e => toString e
  | .query e => toString e
  | .open_ e => s!"{repr e}"
  | .io m => m

instance : ToString ApiError := ⟨fun e => s!"{e.code}: {e.message}"⟩

/-- Per-predicate statement counts for join ordering, stamped with the last transaction they
reflect; a commit (a new basis) refreshes them. They change only speed. -/
structure PredCounts where
  basis : Int64 := -1
  counts : List (Value × Nat) := []

/-- An open database. -/
structure Db where
  shell : Shell.Db
  opts : OpenOptions
  counts : IO.Ref PredCounts

/-- A view handle: deriving one reads nothing. -/
structure View where
  db : Db
  spec : Tiramemsu.View.ViewSpec

def Db.open (path : System.FilePath) (opts : OpenOptions := {}) : IO (Except ApiError Db) := do
  let dbo : DbOptions := { readers := opts.readers, busyTimeoutMs := opts.busyTimeoutMs, termCacheCapacity := some opts.termCacheCapacity }
  match ← Shell.Db.open path dbo opts.clock with
  | .ok d => pure (.ok { shell := d, opts, counts := ← IO.mkRef {} })
  | .error e => pure (.error (.open_ e))

def Db.close (db : Db) : IO Unit := db.shell.close

def Db.pathOpts (db : Db) : Path.PathOpts := { maxHops := db.opts.pathMaxHops, maxStates := db.opts.pathMaxStates }

/-- One transaction (a failing body leaves no trace). -/
def Db.transact {α : Type} (db : Db) (body : TxProg α) (opts : TxOptions := {}) :
    IO (Except ApiError (α × TxReport)) := do
  return (← db.shell.transact opts body).mapError .engine

def Db.now (db : Db) : View := { db, spec := {} }
def Db.asOf (db : Db) (at_ : Tiramemsu.View.TimeRef) : View := { db, spec := { tx := .asOf at_ } }
def Db.history (db : Db) : View := { db, spec := { tx := .history } }
def View.validAt (v : View) (ms : Int64) : View := { v with spec := v.spec.validAt ms }

/-- Runs a read program on one snapshot of the view's store. -/
def View.read {α : Type} (v : View) (p : RProg α) : IO (Except ApiError α) := do
  try
    -- one term cache per read: decoding the same term twice in a query costs one lookup
    let cache ← Term.ReaderCache.new v.db.opts.termCacheCapacity
    v.db.shell.withView v.spec fun pv => do
      match ← ((RProg.interp (m := ReaderT Term.ReaderCache Sqlite.ReaderM) ROp.run p) cache pv.conn).run with
      | .ok a => pure (.ok a)
      | .error e => pure (.error (.engine (.store e)))
  catch e => pure (.error (.io (toString e)))

/-- A view read (`ReadProg`). -/
def View.query {α : Type} (v : View) (q : ReadProg α) : IO (Except ApiError α) := do
  match ← v.read (ReadProg.run v.spec q) with
  | .ok (.ok a) => pure (.ok a)
  | .ok (.error e) => pure (.error (.engine e))
  | .error e => pure (.error e)

/-! ## View reads -/

def lookupOpt (x : Option Value) : ReadProg (Option (Option ObjectId)) := do
  match x with
  | none => return some none
  | some v => return (← ReadProg.query (.lookup v)).map some

/-- `triples(s?, p?, o?)`: a constant that is not stored matches nothing. -/
def View.triples (v : View) (s p o : Option Value) : IO (Except ApiError (List TripleRow)) :=
  v.query do
    match ← lookupOpt s, ← lookupOpt p, ← lookupOpt o with
    | some s, some p, some o => return (← ReadProg.query (.triples s p o)).toList
    | _, _, _ => return []

def View.values (v : View) (s key : ObjectId) : IO (Except ApiError (List ObjectId)) :=
  v.query do return (← ReadProg.query (.values s key)).toList
def View.dependents (v : View) (e : ObjectId) : IO (Except ApiError (List ObjectId)) :=
  v.query do return (← ReadProg.query (.dependents e)).toList
def View.graphs (v : View) : IO (Except ApiError (List ObjectId)) :=
  v.query do return (← ReadProg.query .graphs).toList
def View.graphMembers (v : View) (g : ObjectId) : IO (Except ApiError (List ObjectId)) :=
  v.query do return (← ReadProg.query (.graphMembers g)).toList
/-- A dictionary lookup that never inserts. -/
def View.encode (v : View) (x : Value) : IO (Except ApiError (Option ObjectId)) := v.query (ReadProg.query (.lookup x))
def View.decode (v : View) (x : ObjectId) : IO (Except ApiError Value) := v.query (ReadProg.query (.decode x))
def View.eventsSince (v : View) (since : Int64) : IO (Except ApiError (List Event)) :=
  v.query do return (← ReadProg.query (.events since)).toList

/-! ## IR execution -/

/-- A query result: columns, rows of decoded values, and with provenance each row's citations. -/
structure Result where
  columns : List Var
  rows : List (List (Option Value))
  cites : Option (List (List ObjectId)) := none
  deriving Repr, Inhabited

/-- Validation and parameter binding, before any read. -/
def checkQuery (q : Query) (ps : Params) : Except QError Prepared := do
  validate q
  prepare ps q

/-- The read program of an execution. -/
def execProg (opts : Path.PathOpts) (ps : Params) (q : Query) (provenance : Bool)
    (counts : Value → Option Nat := fun _ => none) : RProg (Except QError Result) :=
  if provenance then do
    match ← (Prov.evalQueryProv opts ps q).run with
    | .ok (p, b) => return .ok { columns := p.columns, rows := b.map (p.project ·.1),
                                 cites := some (b.map fun (_, es) => es.map (⟨·⟩)) }
    | .error e => return .error e
  else do
    match ← (Query.eval opts ps q counts).run with
    | .ok (p, b) => return .ok { columns := p.columns, rows := b.map p.project }
    | .error e => return .error e

/-- The constant predicates of a tree's triple patterns. -/
partial def constPreds : IR.Op → List Value
  | .triple t => match t.p with | .const c => [c.canonical] | _ => []
  | .join xs | .union xs => xs.flatMap constPreds
  | .leftJoin l r _ => constPreds l ++ constPreds r
  | .filter _ x | .extend _ _ x | .aggregate _ _ x | .project _ _ x | .orderLimit _ _ _ x => constPreds x
  | _ => []

/-- Counts the live statements of predicates (one range scan each). -/
def countProg (preds : List Value) : RProg (Int64 × List (Value × Nat)) := do
  let basis ← Tiramemsu.View.basisT
  let cs ← preds.mapM fun p => do
    match ← Term.lookupValue (m := RProg) p with
    | .ok (some id) => do
      let rows ← RProg.lift (.scan { family := .livePos, pre := #[id.raw], view := {} })
      pure (p, rows.size)
    | _ => pure (p, 0)
  return (basis, cs)

/-- The per-predicate counts a query needs, from the cache when its basis is current. -/
def View.predCounts (v : View) (preds : List Value) : IO (Value → Option Nat) := do
  let cur ← v.db.counts.get
  let missing := preds.eraseDups.filter fun p => !(cur.counts.any (·.1 == p))
  if missing.isEmpty && cur.basis != -1 then
    match ← v.read Tiramemsu.View.basisT with
    | .ok b => if b == cur.basis then return fun p => (cur.counts.lookup p) else pure ()
    | .error _ => pure ()
  match ← v.read (countProg preds.eraseDups) with
  | .ok (b, cs) =>
    let keep := if b == cur.basis then cur.counts.filter (fun kv => !(cs.any (·.1 == kv.1))) else []
    let all := keep ++ cs
    v.db.counts.set { basis := b, counts := all }
    return fun p => all.lookup p
  | .error _ => return fun _ => none

/-- `execute`: validates, then evaluates in one snapshot. A pattern's own view takes precedence
over the handle's (which only front ends use as their default). -/
def View.execute (v : View) (q : Query) (ps : Params := []) (provenance : Bool := false) :
    IO (Except ApiError Result) := do
  match checkQuery q ps with
  | .error e => return .error (.query e)
  | .ok _ =>
    let counts ← v.predCounts (constPreds q.root)
    match ← v.read (execProg v.db.pathOpts ps q provenance counts) with
    | .ok (.ok r) => return .ok r
    | .ok (.error e) => return .error (.query e)
    | .error e => return .error e

/-- `with`: runs a body speculatively, then the query on the speculative state; every write is
discarded. -/
def Db.with {α : Type} (db : Db) (body : TxProg α) (q : Query) (ps : Params := []) (validAt : Option Int64 := none) :
    IO (Except ApiError Result) := do
  match checkQuery q ps with
  | .error e => return .error (.query e)
  | .ok _ =>
    let prog : RProg (Except Engine.Error (Except QError Result)) := do
      return .ok (← execProg db.pathOpts ps q false)
    let _ := validAt
    match ← db.shell.runCore false (speculativeCore db.shell.now {} body.run fun _ _ => runReads prog) with
    | .ok (.ok r) => return .ok r
    | .ok (.error e) => return .error (.query e)
    | .error e => return .error (.engine e)

/-! ## Paths -/

/-- The options of `pathWith` (Rust `PathArgs`): `REACH`, no hop bound, no graph set, not
time-respecting by default. -/
structure PathArgs where
  mode : PathMode := .reach
  maxHops : Option Nat := none
  graphs : Option (List ObjectId) := none
  /-- `some after`: time-respecting from `after` (`none`: −∞). -/
  timeRespecting : Option (Option Int64) := none

def View.pathWith (v : View) (start : ObjectId) (text : String) (args : PathArgs := {}) :
    IO (Except ApiError (List Path.PathRow)) := do
  let prog : RProg (Except QError (List Path.PathRow)) := (do
    let expr ← Path.parseText text
    let req : Path.Request := { start := start.raw, expr, mode := args.mode, maxHops := args.maxHops, view := v.spec, graphs := Option.map (List.map ObjectId.raw) args.graphs, timed := Option.map (Option.map Int64.toInt) args.timeRespecting }
    Path.run v.db.pathOpts req).run
  match ← v.read prog with
  | .ok (.ok rows) => return .ok rows
  | .ok (.error e) => return .error (.query e)
  | .error e => return .error e

def View.path (v : View) (start : ObjectId) (text : String) (mode : PathMode := .reach) (maxHops : Option Nat := none) :
    IO (Except ApiError (List Path.PathRow)) :=
  v.pathWith start text { mode, maxHops }

/-! ## Bundles and explain -/

def View.bundle (v : View) (root : ObjectId) : IO (Except ApiError Bundle) := do
  match ← v.read (exportBundle v.spec root).run with
  | .ok (.ok b) => return .ok b
  | .ok (.error e) => return .error (.engine e)
  | .error e => return .error e

/-- `Tx.importBundle`: the import as a transaction-body program. -/
def Tx.importBundle (b : Bundle) : TxProg ImportReport := Bundle.importBundle b

/-- The plan the evaluator will run (no store read). -/
def View.explain (_ : View) (q : Query) (ps : Params := []) : Except ApiError Plan :=
  match checkQuery q ps with
  | .ok p => .ok (planOf p.root)
  | .error e => .error (.query e)

def _root_.Tiramemsu.Exec.Plan.text (p : Plan) : String := "\n".intercalate (p.render "")

partial def _root_.Tiramemsu.Exec.Plan.toJson : Plan → Json
  | .node op pats paths children =>
    .obj #[("op", .str op),
      ("patterns", .arr (pats.map fun p => Json.obj #[("pattern", .str p.pattern), ("access", .str p.access),
        ("prefix", .arr (p.keyPrefix.map Json.str).toArray), ("family", .str p.family),
        ("filters", .arr (p.filters.map Json.str).toArray)]).toArray),
      ("paths", .arr (paths.map fun p => Json.obj #[("pattern", .str p.pattern), ("mode", .str p.mode),
        ("states", .int p.states), ("direction", .str p.direction)]).toArray),
      ("children", .arr (children.map Exec.Plan.toJson).toArray)]

end Tiramemsu.Api
