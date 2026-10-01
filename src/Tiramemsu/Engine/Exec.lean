/-
The interpreters of bodies and queries: `TxProg.run` runs a body verb by verb in `EngM`;
`ReadProg.run` runs a read-only query on a view as a read program.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Supersede
import Tiramemsu.Engine.Graph

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Transaction Bodies]]

namespace EngM

def lookup (v : Value) : EngM (Option ObjectId) := do
  codec .value (← reads (lookupValue v))

def decodeId (x : ObjectId) : EngM Value := do
  codec .value (← reads (decode x))

end EngM

/-- One verb in the engine. -/
def Verb.exec {β : Type} : Verb β → EngM β
  | .encode v => EngM.internValue v
  | .lookup v => EngM.lookup v
  | .decode x => EngM.decodeId x
  | .assert s p o opts => EngM.assertStmt s p o opts
  | .create s p o valid => EngM.create s p o valid
  | .retract e => EngM.retract e
  | .retractMatching s p o => return (← EngM.retractMatching s p o).toArray
  | .supersede e patch => EngM.supersede e patch
  | .confirm e => EngM.confirm e
  | .upsert p o => EngM.upsert p o
  | .metadata p o => EngM.metadata p o
  | .newNode => EngM.newNode
  | .newBNode => EngM.newBNode
  | .setVolatile s k v => EngM.setVolatile s k v
  | .clearVolatile s k => EngM.clearVolatile s k
  | .addToGraph e g opts => EngM.addToGraph e g opts
  | .removeFromGraph e g => EngM.removeFromGraph e g
  | .clearGraph g => return (← EngM.clearGraph g).toArray
  | .createGraph g => EngM.createGraph g
  | .dropGraph g => return (← EngM.dropGraph g).toArray
  | .triples s p o => return (← EngM.reads (View.triplesIn {} s p o)).toArray
  | .dependents e => return ((← EngM.reads (View.dependentsIn {} e.raw)).map (⟨·⟩)).toArray
  | .schema p => EngM.schema p
  | .abort e => EngM.fail e

/-- Runs a body in the engine, verb by verb. -/
def TxProg.run {α : Type} : TxProg α → EngM α
  | .pure a => Pure.pure a
  | .step v k => do
    let b ← v.exec
    TxProg.run (k b)

/-- One query verb on a view. -/
def QVerb.exec {β : Type} (v : View.ViewSpec) : QVerb β → RProg (Except Error β)
  | .triples s p o => do return .ok (← View.triples v s p o).toArray
  | .values s k => do return .ok (← View.values v s k).toArray
  | .dependents e => do return .ok (← View.dependents v e).toArray
  | .events since => do return .ok (← View.eventsSince since).toArray
  | .graphs => do return .ok (← View.graphs v).toArray
  | .graphMembers g => do return .ok (← View.graphMembers v g).toArray
  | .lookup x => do
    match ← Term.lookupValue x with
    | .ok r => pure (.ok r)
    | .error e => pure (.error (Error.ofCodec .value e))
  | .decode x => do
    match ← Term.decode x with
    | .ok r => pure (.ok r)
    | .error e => pure (.error (Error.ofCodec .value e))
  | .basis => do return .ok (← View.basisT)

/-- Runs a query on a view. -/
def ReadProg.run {α : Type} (v : View.ViewSpec) : ReadProg α → RProg (Except Error α)
  | .pure a => Pure.pure (Except.ok a)
  | .fail e => Pure.pure (Except.error e)
  | .step q k => do
    match ← QVerb.exec v q with
    | .ok b => ReadProg.run v (k b)
    | .error e => Pure.pure (Except.error e)

end Tiramemsu.Engine
