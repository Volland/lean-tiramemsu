/-
Transaction bodies: the engine monad `EngM` (the transaction context over body programs), the
verbs a body may use, and the IO-free body type `TxProg` (a free monad over `Verb`), with the
read-only `ReadProg` that speculative queries get.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Engine.Op

namespace Tiramemsu.Engine

open Tiramemsu.Codec Tiramemsu.Store Tiramemsu.Term

--# @lat: [[engine#Transaction Bodies]]

/-- The flags in force for one predicate. -/
structure PredicateSchema where
  one : Bool := false
  unique : Bool := false
  valueType : Option ObjectId := none
  /-- Tag IRIs, in eid order of their flag statements; empty: any subject kind. -/
  subjectTypes : List ObjectId := []
  isEdge : Option Bool := none
  deriving Repr, DecidableEq, Inhabited

/-- The state of a running transaction: its number and instant, its options and the report
under construction. -/
structure TxCtx where
  t : Int64
  instant : Int64
  opts : TxOptions
  report : TxReport
  deriving Repr, Inhabited

/-- The engine monad: the transaction context and engine errors over body programs. -/
abbrev EngM := StateT TxCtx (ExceptT Error SProg)

namespace EngM

/-- One operation. -/
def op (o : Op) : EngM o.Res := monadLift (SProg.lift o)

/-- One read. -/
def rd (r : ROp) : EngM r.Res := op (.read r)

/-- A read program. -/
def reads {α : Type} (p : RProg α) : EngM α := monadLift p.toS

/-- Fails the transaction. -/
def fail {α : Type} (e : Error) : EngM α := throw e

/-- An `Except` as an engine step. -/
def ofExcept {α : Type} : Except Error α → EngM α
  | .ok a => pure a
  | .error e => throw e

/-- A codec result in a position. -/
def codec {α : Type} (pos : Position) : Except CodecError α → EngM α
  | .ok a => pure a
  | .error e => throw (Error.ofCodec pos e)

/-- Updates the report. -/
def report (f : TxReport → TxReport) : EngM Unit :=
  modify fun c => { c with report := f c.report }

end EngM

instance : TermReader RProg where
  lookupKey k := RProg.lift (.lookupKey k)
  rowById i := RProg.lift (.rowById i)

/-! ## Verbs and bodies -/

/-- The operations of a transaction body. -/
inductive Verb : Type → Type where
  /-- Encodes a value, interning it when it needs the dictionary. -/
  | encode (v : Value) : Verb ObjectId
  /-- Looks a value up without interning (`none` when a needed term is absent). -/
  | lookup (v : Value) : Verb (Option ObjectId)
  /-- Decodes an id, seeing this transaction's own terms. -/
  | decode (x : ObjectId) : Verb Value
  | assert (s p o : ObjectId) (opts : AssertOpts) : Verb Asserted
  | create (s p o : ObjectId) (valid : Valid) : Verb ObjectId
  | retract (e : ObjectId) : Verb Bool
  | retractMatching (s p o : Option ObjectId) : Verb (Array ObjectId)
  | supersede (e : ObjectId) (patch : Patch) : Verb ObjectId
  | confirm (e : ObjectId) : Verb ObjectId
  | upsert (p o : ObjectId) : Verb ObjectId
  | metadata (p o : ObjectId) : Verb ObjectId
  | newNode : Verb ObjectId
  | newBNode : Verb ObjectId
  | setVolatile (s key value : ObjectId) : Verb Unit
  | clearVolatile (s key : ObjectId) : Verb Unit
  | addToGraph (e g : ObjectId) (opts : AssertOpts) : Verb (ObjectId × Bool)
  | removeFromGraph (e g : ObjectId) : Verb Bool
  | clearGraph (g : ObjectId) : Verb (Array ObjectId)
  | createGraph (g : ObjectId) : Verb Asserted
  | dropGraph (g : ObjectId) : Verb (Array ObjectId)
  /-- Statements live at this point of the transaction matching the bound positions. -/
  | triples (s p o : Option ObjectId) : Verb (Array TripleRow)
  /-- What stands on a statement at this point of the transaction. -/
  | dependents (e : ObjectId) : Verb (Array ObjectId)
  | schema (p : ObjectId) : Verb PredicateSchema
  /-- Aborts the body with an error. -/
  | abort (e : Error) : Verb PEmpty

/-- A transaction body: an IO-free program over the verbs. -/
inductive TxProg (α : Type) : Type 1 where
  | pure (a : α)
  | step {β : Type} (v : Verb β) (k : β → TxProg α)

namespace TxProg

def bind {α β : Type} : TxProg α → (α → TxProg β) → TxProg β
  | .pure a, f => f a
  | .step v k, f => .step v fun x => bind (k x) f

instance : Monad TxProg where
  pure := .pure
  bind := bind

/-- One verb as a body. -/
def verb {β : Type} (v : Verb β) : TxProg β := .step v .pure

/-- Aborts the body. -/
def abort {α : Type} (e : Error) : TxProg α := .step (.abort e) fun x => nomatch x

end TxProg

/-- The reads of a view. -/
inductive QVerb : Type → Type where
  | triples (s p o : Option ObjectId) : QVerb (Array TripleRow)
  | values (s key : ObjectId) : QVerb (Array ObjectId)
  | dependents (e : ObjectId) : QVerb (Array ObjectId)
  | events (since : Int64) : QVerb (Array Event)
  | graphs : QVerb (Array ObjectId)
  | graphMembers (g : ObjectId) : QVerb (Array ObjectId)
  | lookup (v : Value) : QVerb (Option ObjectId)
  | decode (x : ObjectId) : QVerb Value
  | basis : QVerb Int64

/-- A read-only program over a view (speculative queries and pinned views). -/
inductive ReadProg (α : Type) : Type 1 where
  | pure (a : α)
  | step {β : Type} (q : QVerb β) (k : β → ReadProg α)
  | fail (e : Error)

namespace ReadProg

def bind {α β : Type} : ReadProg α → (α → ReadProg β) → ReadProg β
  | .pure a, f => f a
  | .step q k, f => .step q fun x => bind (k x) f
  | .fail e, _ => .fail e

instance : Monad ReadProg where
  pure := .pure
  bind := bind

def query {β : Type} (q : QVerb β) : ReadProg β := .step q .pure

end ReadProg

end Tiramemsu.Engine
