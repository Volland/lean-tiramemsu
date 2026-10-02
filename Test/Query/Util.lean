/-
Query test utilities: a small IR builder, fixtures built through the memory verbs on the model
store, and runners that evaluate a query with the reference semantics and with the evaluator
(on the model and on SQLite) and compare the bags.
-/
import Test.Store.Run

namespace Test.Query

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem
open Tiramemsu.Exec (EvM)
open Tiramemsu.Sqlite
open Test.Store (v sysV assertV createV enc day)

/-! ## IR builder -/

/-- `?x` is a variable, `$x` a parameter, `sys:x`/`tm:x` a reserved IRI, anything else a
`v:` IRI. -/
def term (s : String) : TermOrVar :=
  if s.startsWith "?" then .var (s.drop 1).toString
  else if s.startsWith "$" then .param (s.drop 1).toString
  else if s.startsWith "sys:" then .const (.iri (Vocab.sys ++ (s.drop 4).toString))
  else if s.startsWith "tm:" then .const (.iri (Vocab.tm ++ (s.drop 3).toString))
  else .const (v s)

def tp (s p o : String) (view : View.ViewSpec := {}) : IR.Op := .triple { s := term s, p := term p, o := term o, view }

def tpe (s p o e : String) (view : View.ViewSpec := {}) : IR.Op :=
  .triple { s := term s, p := term p, o := term o, eid := some e, view }

def tpt (t : TriplePattern) : IR.Op := .triple t

def x (n : String) : Expr := .var n
def c (val : Value) : Expr := .const val
def eq (a b : Expr) : Expr := .cmp .eq a b

/-! ## Fixtures -/

/-- Runs bodies one transaction each (clock `1000 · i`) on a fresh model state. -/
def build (bodies : List (TxProg Unit)) : IO ModelState := do
  let mut st := Test.Store.freshModelState
  let mut i : Int := 1
  for b in bodies do
    let (r, st') := Model.transact (1000 * i) {} b st
    match r with
    | .ok _ => st := st'
    | .error e => throw (IO.userError s!"fixture transaction {i} failed: {e}")
    i := i + 1
  return st

def facts (fs : List (String × String × Value)) : TxProg Unit := do
  for (s, p, o) in fs do
    let _ ← assertV (v s) (v p) o
  pure ()

/-- Every permutation of a list. -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun p => (List.range (p.length + 1)).map fun i => p.take i ++ [x] ++ p.drop i

/-- A fixture on both stores: the model state and a SQLite file with the same transactions. -/
structure Fix where
  st : ModelState
  db : Sqlite.Store

/-- Builds a fixture on the model and on a fresh SQLite file (same clock readings). -/
def buildBoth (name : String) (bodies : List (TxProg Unit)) : IO Fix := do
  let st ← build bodies
  let path ← freshPath s!"m3-{name}"
  let db ← Test.Store.openStore path
  let h := Test.Store.sqliteHarness path db (← Term.WriterCache.new none)
  let mut i : Int := 1
  for b in bodies do
    match ← h.tx (1000 * i) {} b with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"sqlite fixture transaction {i} failed: {e}")
    i := i + 1
  return { st, db }

/-- A read program on a SQLite snapshot. -/
def onSqlite {α : Type} (db : Sqlite.Store) (p : RProg α) : IO (Except StoreError α) := do
  (do
    let rd ← SnapshotStore.beginRead (m := SqliteM) db
    let x ← (RProg.interp (m := ReaderM) ROp.run p) rd.conn
    SnapshotStore.endRead (m := SqliteM) rd db
    pure x : SqlM _).run

/-! ## Running -/

/-- The reference semantics without paths. -/
def denoteQ (st : ModelState) (ps : Params) (q : Query) : Except QError (Prepared × Bag) := do
  let p ← prepare ps q
  return (p, ← denote (p.env st) (Path.denotePath {}) p.root)

/-- The evaluator run on a model state. -/
def evalModel (st : ModelState) (ps : Params) (q : Query) : Except QError (Prepared × Bag) :=
  match (Exec.evalQueryWith (Path.evalPath {}) ps q).run.onModel st with
  | .ok r => r
  | .error e => .error (.store e)

/-- The evaluator run on a SQLite snapshot. -/
def evalSqlite (db : Sqlite.Store) (ps : Params) (q : Query) : IO (Except QError (Prepared × Bag)) := do
  match ← onSqlite db (Exec.evalQueryWith (Path.evalPath {}) ps q).run with
  | .ok r => pure r
  | .error e => pure (.error (.store e))

/-- A bag in canonical order (for comparing bags). -/
def canon (b : Bag) : Bag := b.mergeSort rowLe

/-- The projected rows of a result, canonically ordered. -/
def rowsOf (p : Prepared) (b : Bag) : List (List (Option Value)) :=
  (b.map p.project).mergeSort fun a c => rowLe a c

/-- Rows over named columns, canonically ordered. -/
def rowsBy (p : Prepared) (cols : List Var) (b : Bag) : List (List (Option Value)) :=
  (b.map fun r => cols.map fun c => if p.vars.contains c then r.get (p.vars.idxOf c) else none).mergeSort
    fun a c => rowLe a c

def showErr {α : Type} : Except QError α → String
  | .ok _ => "ok"
  | .error e => e.code

end Test.Query
