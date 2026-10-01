/-
The M2 test harness: one interface over the model store and a SQLite file, so every store
scenario runs unchanged on both ("Same body on both stores"). Clock readings are explicit
(a manual clock), so instants are deterministic.
-/
import Test.Util

namespace Test.Store

open Tiramemsu Tiramemsu.Store Tiramemsu.Sqlite Tiramemsu.Engine Tiramemsu.Term Tiramemsu.Codec

/-- A store under test. -/
structure Harness where
  name : String
  tx : {α : Type} → Int → TxOptions → TxProg α → IO (Except Error (α × TxReport))
  dry : {α : Type} → Int → TxOptions → TxProg α → IO (Except Error (α × TxReport))
  spec : {α β : Type} → Int → TxProg α → Option Int64 → ReadProg β → IO (Except Error β)
  query : {α : Type} → View.ViewSpec → ReadProg α → IO (Except Error α)
  /-- Every table, as a model state (committed contents). -/
  tables : IO ModelState
  close : IO Unit

/-- The model store, from an initial committed state. -/
def modelHarness (ref : IO.Ref ModelState) : Harness :=
  {
    name := "model"
    tx := fun now opts prog => do
      let (r, st) := Model.transact now opts prog (← ref.get)
      ref.set st
      pure r
    dry := fun now opts prog => do
      let (r, st) := Model.dryRun now opts prog (← ref.get)
      ref.set st
      pure r
    spec := fun now prog d q => do
      let (r, st) := Model.speculate now prog d q (← ref.get)
      ref.set st
      pure r
    query := fun v q => do pure (Model.query (← ref.get) v q)
    tables := ref.get
    close := pure () }

/-- The empty format-1 model state (the `meta` rows of a fresh file). -/
def freshModelState : ModelState :=
  { counters := Storage.initialMeta.toList }

def storeErr {α : Type} : Except StoreError (Except Error α) → Except Error α
  | .ok r => r
  | .error e => .error (.store e)

/-- A SQLite file opened with the format-1 open path, with an unbounded writer term cache. -/
def finishWith {α : Type} (cache : WriterCache) (keep : Bool) (r : Except StoreError (Except Error α)) :
    IO (Except Error α) := do
  match r with
  | .ok (.ok _) => if keep then cache.commit else cache.rollback
  | _ => cache.rollback
  pure (storeErr r)

/-- Opens a SQLite file with the format-1 open path. -/
def openStore (path : System.FilePath) : IO Sqlite.Store := do
  match ← Storage.openFile path with
  | .ok st => pure st
  | .error e => throw (IO.userError s!"cannot open {path}: {e}")

def sqliteHarness (path : System.FilePath) (st : Sqlite.Store) (cache : WriterCache) : Harness :=
  let finish {α : Type} := finishWith (α := α) cache
  {
    name := "sqlite"
    tx := fun now opts prog => do
      finish true (← ((transactCore (pure now) opts prog.run : CachedM SqliteM _) cache st).run)
    dry := fun now opts prog => do
      finish false (← ((dryRunCore (pure now) opts prog.run : CachedM SqliteM _) cache st).run)
    spec := fun now prog d q => do
      finish false (← ((speculateCore (pure now) prog.run d q : CachedM SqliteM _) cache st).run)
    query := fun v q => do
      let r ← (do
        let rd ← SnapshotStore.beginRead (m := SqliteM) st
        let x ← (RProg.interp (m := ReaderM) ROp.run (ReadProg.run v q)) rd.conn
        SnapshotStore.endRead (m := SqliteM) rd st
        pure x : SqlM _).run
      pure (storeErr r)
    tables := do
      match ← (loadModelState path).run with
      | .ok s => pure s
      | .error e => throw (IO.userError s!"cannot dump {path}: {e}")
    close := st.close }

/-! ## Body helpers -/

def v (local_ : String) : Value := .iri (Vocab.vIri local_)
def enc (x : Value) : TxProg ObjectId := .verb (.encode x)
def assertV (s p o : Value) (valid : Valid := {}) (on : OnExisting := .return_) : TxProg Asserted := do
  TxProg.verb (.assert (← enc s) (← enc p) (← enc o) { valid, onExisting := on })
def assertI (s : ObjectId) (p o : Value) (valid : Valid := {}) : TxProg Asserted := do
  TxProg.verb (.assert s (← enc p) (← enc o) { valid })
def createV (s p o : Value) (valid : Valid := {}) : TxProg ObjectId := do
  TxProg.verb (.create (← enc s) (← enc p) (← enc o) valid)
def retractE (e : ObjectId) : TxProg Bool := .verb (.retract e)
def supersedeE (e : ObjectId) (patch : Patch) : TxProg ObjectId := .verb (.supersede e patch)
def stmt (n : Nat) : ObjectId := mkAlloc .stmt 0 n.toUInt64
def txOid (n : Nat) : ObjectId := mkAlloc .tx 0 n.toUInt64
def ctr (e : ObjectId) : Nat := e.counter.toNat

/-- Statement eids of a report list. -/
def eidsOf (xs : Array ObjectId) : List Nat := xs.toList.map ctr
def kindsOf (xs : Array (ObjectId × RetKind)) : List (Nat × RetKind) := xs.toList.map fun (e, k) => (ctr e, k)

/-- Rows of a query. -/
def triplesQ (s p o : Option Value := none) : ReadProg (Array TripleRow) := do
  let look (x : Option Value) : ReadProg (Option (Option ObjectId)) := match x with
    | none => pure (some none)
    | some x => do return (← ReadProg.query (.lookup x)).map some
  match ← look s, ← look p, ← look o with
  | some s, some p, some o => ReadProg.query (.triples s p o)
  | _, _, _ => pure #[]

def errCode {α : Type} : Except Error α → String
  | .ok _ => "ok"
  | .error e => e.code

end Test.Store

namespace Test.Store

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec

/-- Epoch milliseconds of a date `YYYY-MM-DD`. -/
def day (s : String) : Int64 := Int64.ofInt ((parseDate s).getD 0 * 86400000)

def dbl (s : String) : Value := .typed s xsdDouble
def sysV (local_ : String) : Value := .iri (Vocab.sys ++ local_)
def tagV (t : Tag) : Value := .iri (Vocab.tagIri t)
def between (a b : String) : Valid := { vFrom := some (day a), vTo := some (day b) }
def fromD (a : String) : Valid := { vFrom := some (day a) }

def flagV (pred : String) (flag : String) (o : Value) : TxProg Asserted := assertV (v pred) (sysV flag) o

/-- History rows of a statement. -/
def rowOf (h : Harness) (e : ObjectId) : IO (Option TripleRow) := do
  return (← h.tables).triples.find? (·.eid == e.raw)

def liveQ (e : ObjectId) : ReadProg Bool := do
  return (← ReadProg.query (.triples (some e) none none)).isEmpty == false

/-- The eids a view shows for a pattern. -/
def eidsQ (s p o : Option Value := none) : ReadProg (List Nat) := do
  return (← triplesQ s p o).toList.map fun r => ctr ⟨r.eid⟩

def depsQ (e : ObjectId) : ReadProg (List Nat) := do
  return (← ReadProg.query (.dependents e)).toList.map ctr

def asOf (t : Int64) : View.ViewSpec := View.ViewSpec.asOfT t
def hist : View.ViewSpec := View.ViewSpec.history
def nowV : View.ViewSpec := {}

end Test.Store
