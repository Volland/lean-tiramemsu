/-
The engine on the model store: `Model.transact`, `Model.dryRun`, `Model.speculate` are the
generic transaction cores at the model instance, with the clock reading as an argument; reads
run a read program on a committed model state. Every Tier 1 theorem is stated over these.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Transact

namespace Tiramemsu.Model

open Tiramemsu.Store Tiramemsu.Engine

--# @lat: [[engine#Model Instance]]

/-- Runs a store computation on a committed state and returns the new committed state. -/
def onState {α : Type} (x : ModelM (Except Error α)) (st : ModelState) : Except Error α × ModelState :=
  match x (ModelStore.ofState st) with
  | .ok (r, s) => (r, s.committed)
  | .error e => (.error (.store e), st)

/-- One transaction with clock reading `now`. -/
def transactE {α : Type} (now : Int) (opts : TxOptions) (body : EngM α) (st : ModelState) :
    Except Error (α × TxReport) × ModelState :=
  onState (transactCore (pure now) opts body) st

def transact {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState) :
    Except Error (α × TxReport) × ModelState :=
  transactE now opts prog.run st

/-- A dry run with clock reading `now`. -/
def dryRun {α : Type} (now : Int) (opts : TxOptions) (prog : TxProg α) (st : ModelState) :
    Except Error (α × TxReport) × ModelState :=
  onState (dryRunCore (pure now) opts prog.run) st

/-- A speculation with clock reading `now`: the query's value on the uncommitted state. -/
def speculate {α β : Type} (now : Int) (prog : TxProg α) (validAt : Option Int64)
    (query : ReadProg β) (st : ModelState) : Except Error β × ModelState :=
  onState (speculateCore (pure now) prog.run validAt query) st

/-- A read program on a committed state. -/
def reads {α : Type} (st : ModelState) (p : RProg α) : Except StoreError α := p.onModel st

/-- A query on a view of a committed state. -/
def query {α : Type} (st : ModelState) (v : View.ViewSpec) (q : ReadProg α) : Except Error α :=
  match (ReadProg.run v q).onModel st with
  | .ok r => r
  | .error e => .error (.store e)

end Tiramemsu.Model
