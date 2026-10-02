/-
Bundle import (Rust `engine/bundle.rs`): a transaction-body program. It checks the bundle's
structure (unique ids, a known root, IRI predicates, known references, no ids local to another
database) and its reference graph (a cycle is `Unsupported` before any write), then writes every
statement in reference order: a `sys:inGraph` statement as a graph membership, any other as an
idempotent assert with its valid time. One fresh node per anonymous label. The report gives the
root's eid and, in bundle order, each local id with its eid and whether it is new.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.Bundle.Export

namespace Tiramemsu.Bundle

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.Engine

--# @lat: [[query#Fact Bundles]]

/-- One imported statement. -/
structure Imported where
  local_ : Nat
  eid : ObjectId
  new : Bool
  deriving Repr, DecidableEq, Inhabited

/-- What an import did. -/
structure ImportReport where
  root : ObjectId
  statements : List Imported
  deriving Repr, DecidableEq, Inhabited

def malformed (reason : String) : Error := .invalidTerm .value s!"malformed bundle: {reason}"

/-- An id local to another database (a node, blank node, statement or transaction). -/
def isLocalId (v : Value) : Bool :=
  match v.canonical with
  | .node _ | .bnode _ | .stmt _ | .tx _ => true
  | _ => false

/-- The structural check, before any write. -/
def Bundle.check (b : Bundle) : Except Error Unit := do
  let ids := b.statements.map (·.local_)
  if ids.eraseDups.length != ids.length then
    throw (malformed "duplicate id")
  if !ids.contains b.root then throw (malformed s!"root {b.root} is not a statement")
  for st in b.statements do
    match st.p with
    | .iri _ => if isLocalId st.p then throw (malformed s!"predicate of statement {st.local_} is not an IRI")
    | _ => throw (malformed s!"predicate of statement {st.local_} is not an IRI")
    for t in [st.s, st.o] do
      match t with
      | .stmt r => if !ids.contains r then throw (malformed s!"statement {st.local_} references unknown statement {r}")
      | .value v => if isLocalId v then
          throw (malformed s!"statement {st.local_} names {v.lexical}, an id local to another database")
      | .node _ => pure ()

/-- The import order (references first), or `none` on a reference cycle. -/
def Bundle.importOrder (b : Bundle) : Option (List Nat) :=
  let pos (l : Nat) : Option Nat := b.statements.findIdx? (·.local_ == l)
  let refsOf (i : Nat) : List Nat :=
    match b.statements[i]? with
    | some st => [st.s, st.o].filterMap fun t => match t with | .stmt r => pos r | _ => none
    | none => []
  let order := topological b.statements.length refsOf
  if order.length == b.statements.length then some order else none

/-- Imports a bundle within the caller's transaction. -/
def importBundle (b : Bundle) : TxProg ImportReport := do
  match b.check with
  | .error e => TxProg.abort e
  | .ok () =>
  match b.importOrder with
  | none => TxProg.abort (.unsupported "bundle with a reference cycle")
  | some order =>
    let inGraph : Value := .iri Vocab.sysInGraph
    let mut eids : List (Nat × ObjectId × Bool) := []
    let mut nodes : List (Nat × ObjectId) := []
    for i in order do
      let some st := b.statements[i]? | continue
      let mut ts : List ObjectId := []
      for t in [st.s, st.o] do
        match t with
        | .value v => ts := ts ++ [← TxProg.verb (.encode v)]
        | .stmt r => ts := ts ++ [((eids.lookup r).map (·.1)).getD ⟨0⟩]
        | .node n =>
          match nodes.lookup n with
          | some x => ts := ts ++ [x]
          | none =>
            let x ← TxProg.verb .newNode
            nodes := nodes ++ [(n, x)]
            ts := ts ++ [x]
      let s := ts.getD 0 ⟨0⟩
      let o := ts.getD 1 ⟨0⟩
      let opts : AssertOpts := { valid := { vFrom := st.vFrom, vTo := st.vTo }, onExisting := .return_ }
      if st.p == inGraph then
        if s.tagBits != Tag.stmt.toUInt64 then
          TxProg.abort (.invalidTerm .subject s!"the member of membership {st.local_} is not a statement")
        let (e, new) ← TxProg.verb (.addToGraph s o opts)
        eids := eids ++ [(st.local_, e, new)]
      else
        let p ← TxProg.verb (.encode st.p)
        let a ← TxProg.verb (.assert s p o opts)
        eids := eids ++ [(st.local_, a.eid, a.isNew)]
    let statements := b.statements.map fun st =>
      let (e, new) := (eids.lookup st.local_).getD (⟨0⟩, false)
      ({ local_ := st.local_, eid := e, new } : Imported)
    return { root := ((eids.lookup b.root).map (·.1)).getD ⟨0⟩, statements }

end Tiramemsu.Bundle
