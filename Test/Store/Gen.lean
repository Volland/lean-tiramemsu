/-
A seeded generator of random store scripts in the JSON forms of the bridge: transactions with
every verb (including failures, dry runs and cascade limits), speculations with queries, clock
moves (forwards, standing, backwards) and reads on every kind of view. The refinement suite runs
the scripts on the model store and on SQLite; the differential suite on the Lean and the Rust
drivers.
-/
import Tiramemsu

namespace Test.Store.Gen

open Tiramemsu.Json

/-- One request of a script. -/
structure Step where
  op : String
  args : Json
  deriving Inhabited

structure GenState where
  rng : Nat
  /-- An upper estimate of the statements issued so far. -/
  eids : Nat := 0
  clock : Int := 1000
  deriving Inhabited

abbrev GenM := StateM GenState

def nat (lo hi : Nat) : GenM Nat := modifyGet fun s =>
  let r := (s.rng * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  (lo + (r / 65536) % (hi - lo + 1), { s with rng := r })

def pick {α : Type} [Inhabited α] (xs : Array α) : GenM α := do return xs[← nat 0 (xs.size - 1)]!
def chance (pct : Nat) : GenM Bool := do return (← nat 0 99) < pct

def iri (s : String) : Json := .obj #[("iri", .str ("urn:tiramemsu:v:" ++ s))]
def sysIri (s : String) : Json := .obj #[("iri", .str ("urn:tiramemsu:sys:" ++ s))]

def eid : GenM Json := do
  let e := (← get).eids
  let n ← if ← chance 85 then nat (e / 2 + 1) (e + 1) else nat 1 (e + 2)
  if ← chance 20 then return .obj #[("stmt", .int n)] else return .int n

def subject : GenM Json := do
  match ← nat 0 9 with
  | 0 => return .obj #[("stmt", .int (← nat 1 ((← get).eids + 2)))]
  | 1 => return .obj #[("node", .int (← nat 1 3))]
  | 2 => return .obj #[("tx", .int (← nat 1 4))]
  | 3 => if ← chance 30 then return .int 5 else return iri "alice"
  | _ => return iri (← pick #["alice", "bob", "carol", "g1"])

def predicate : GenM Json := do
  if ← chance 4 then return sysIri (← pick #["confirmedBy", "inGraph", "reason", "sensitive"])
  return iri (← pick #["p", "q", "note", "email", "age", "status", "worksAt"])

def object : GenM Json := do
  match ← nat 0 11 with
  | 0 => return .int (← nat 0 3)
  | 1 => return .str (← pick #["x", "a@x.org", "a longer string that needs a term row"])
  | 2 => return .num (← pick #["0.8", "2.5", "1e-7"])
  | 3 => return .obj #[("lex", .str "2025-01-01"), ("datatype", .str "http://www.w3.org/2001/XMLSchema#date")]
  | 4 => return .obj #[("stmt", .int (← nat 1 ((← get).eids + 2)))]
  | 5 => return .bool (← chance 50)
  | 6 => return .obj #[("lex", .str "Anna"), ("lang", .str "de")]
  | _ => return iri (← pick #["acme", "globex", "tea", "x", "alice"])

def time : GenM Json := do return .int ((← pick #[100, 200, 300, 400]) : Nat)

def withValid (base : Array (String × Json)) : GenM Json := do
  let mut kvs := base
  if ← chance 25 then kvs := kvs.push ("validFrom", ← time)
  if ← chance 25 then kvs := kvs.push ("validTo", ← time)
  return .obj kvs

def flag : GenM Json := do
  let p ← pick #["email", "age", "status", "note", "worksAt"]
  match ← nat 0 5 with
  | 0 => return .obj #[("op", .str "assert"), ("s", iri p), ("p", sysIri "unique"), ("o", .bool (← chance 70))]
  | 1 => return .obj #[("op", .str "assert"), ("s", iri p), ("p", sysIri "cardinality"), ("o", sysIri (← pick #["one", "many"]))]
  | 2 => return .obj #[("op", .str "assert"), ("s", iri p), ("p", sysIri "subjectType"), ("o", sysIri (← pick #["STMT", "IRI", "TX", "INT"]))]
  | 3 => return .obj #[("op", .str "assert"), ("s", iri p), ("p", sysIri "valueType"),
      ("o", .obj #[("iri", .str (← pick #["http://www.w3.org/2001/XMLSchema#integer", "http://www.w3.org/2001/XMLSchema#string", "urn:tiramemsu:sys:IRI"]))])]
  | _ => return .obj #[("op", .str "assert"), ("s", iri p), ("p", sysIri "isEdge"), ("o", .bool true)]

def graph : GenM Json := do
  if ← chance 8 then return .str "g" else return iri (← pick #["g1", "g2"])

def txOp : GenM Json := do
  let op ← match ← nat 0 29 with
    | 0 | 1 | 2 | 3 | 4 | 5 => do
      let mut kvs := #[("op", .str "assert"), ("s", ← subject), ("p", ← predicate), ("o", ← object)]
      if ← chance 10 then kvs := kvs.push ("onExisting", .str "confirm")
      withValid kvs
    | 6 | 7 => withValid #[("op", .str "create"), ("s", ← subject), ("p", ← predicate), ("o", ← object)]
    | 8 | 9 => pure (.obj #[("op", .str "retract"), ("eid", ← eid)])
    | 10 => do
      let mut kvs := #[("op", .str "retractMatching")]
      if ← chance 50 then kvs := kvs.push ("s", ← subject)
      if ← chance 70 then kvs := kvs.push ("p", ← predicate)
      if ← chance 30 then kvs := kvs.push ("o", ← object)
      pure (.obj kvs)
    | 11 | 12 | 13 => do
      let mut patch := #[]
      if ← chance 60 then patch := patch.push ("o", ← object)
      if ← chance 30 then
        let t ← time
        patch := patch.push ("validFrom", if ← chance 30 then .null else t)
      if ← chance 30 then
        let t ← time
        patch := patch.push ("validTo", if ← chance 30 then .null else t)
      pure (.obj #[("op", .str "supersede"), ("eid", ← eid), ("patch", .obj patch)])
    | 14 => pure (.obj #[("op", .str "confirm"), ("eid", ← eid)])
    | 15 => pure (.obj #[("op", .str "meta"), ("p", ← pick #[sysIri "author", sysIri "reason", iri "note"]), ("o", ← object)])
    | 16 => pure (.obj #[("op", .str "upsert"), ("p", iri (← pick #["email", "p"])), ("o", ← object)])
    | 17 => pure (.obj #[("op", .str (← pick #["newNode", "newBNode"]))])
    | 18 => pure (.obj #[("op", .str "setVolatile"), ("s", ← subject), ("key", ← pick #[iri "seen", iri "status", .int 3]), ("value", ← object)])
    | 19 => pure (.obj #[("op", .str "clearVolatile"), ("s", ← subject), ("key", ← pick #[iri "seen", iri "status"])])
    | 20 | 21 => withValid #[("op", .str "addToGraph"), ("eid", ← eid), ("graph", ← graph)]
    | 22 => pure (.obj #[("op", .str "removeFromGraph"), ("eid", ← eid), ("graph", ← graph)])
    | 23 => pure (.obj #[("op", .str (← pick #["clearGraph", "createGraph", "dropGraph"])), ("graph", ← graph)])
    | 24 | 25 => flag
    | 26 => do if ← chance 30 then pure (.obj #[("op", .str "fail")]) else withValid #[("op", .str "create"), ("s", ← subject), ("p", ← predicate), ("o", ← object)]
    | _ => do
      -- an annotation on a recent statement
      withValid #[("op", .str "assert"), ("s", .obj #[("stmt", .int (← nat 1 ((← get).eids + 1)))]),
        ("p", iri "note"), ("o", ← object)]
  modify fun s => { s with eids := s.eids + 1 }
  pure op

def view : GenM Json := do
  let kind ← pick #["now", "now", "asOf", "history"]
  let mut kvs := #[("kind", .str kind)]
  if kind == "asOf" then
    if ← chance 70 then kvs := kvs.push ("tx", .int (← nat 0 12))
    else kvs := kvs.push ("instant", .int ((← get).clock - (← nat 0 20)))
  if ← chance 25 then kvs := kvs.push ("validAt", ← time)
  pure (.obj kvs)

def query : GenM Json := do
  match ← nat 0 6 with
  | 0 | 1 => do
    let mut kvs := #[("op", .str "triples")]
    if ← chance 40 then kvs := kvs.push ("s", ← subject)
    if ← chance 40 then kvs := kvs.push ("p", ← predicate)
    if ← chance 20 then kvs := kvs.push ("o", ← object)
    pure (.obj kvs)
  | 2 => pure (.obj #[("op", .str "dependents"), ("eid", ← eid)])
  | 3 => pure (.obj #[("op", .str "values"), ("s", ← subject), ("key", iri (← pick #["seen", "status", "age"]))])
  | 4 => pure (.obj #[("op", .str "graphs")])
  | 5 => pure (.obj #[("op", .str "graphMembers"), ("graph", ← graph)])
  | _ => pure (.obj #[("op", .str "events"), ("since", .int (← nat 0 6))])

def step : GenM Step := do
  match ← nat 0 19 with
  | 0 => do
    let d : Int ← pick #[0, 0, 1, 50, -300]
    modify fun s => { s with clock := s.clock + d }
    pure { op := "m2.setClock", args := .obj #[("ms", .int (← get).clock)] }
  | 1 | 2 => do
    let n ← nat 1 3
    let mut ops := #[]
    for _ in [0:n] do ops := ops.push (← txOp)
    let mut qs := #[]
    for _ in [0:(← nat 1 3)] do qs := qs.push (← query)
    let mut kvs := #[("ops", .arr ops), ("queries", .arr qs)]
    if ← chance 20 then kvs := kvs.push ("validAt", ← time)
    pure { op := "m2.with", args := .obj kvs }
  | 3 | 4 | 5 => do
    let q ← query
    match q with
    | .obj kvs => pure { op := "m2.read", args := .obj (kvs.push ("view", ← view)) }
    | j => pure { op := "m2.read", args := j }
  | _ => do
    let n ← nat 1 3
    let mut ops := #[]
    for _ in [0:n] do ops := ops.push (← txOp)
    let mut opts := #[]
    if ← chance 10 then opts := opts.push ("dryRun", .bool true)
    if ← chance 10 then opts := opts.push ("maxCascade", .int (← nat 0 3))
    pure { op := "m2.transact", args := .obj #[("ops", .arr ops), ("options", .obj opts)] }

/-- A script of `n` steps from a seed. -/
def script (seed n : Nat) : Array Step := Id.run do
  let mut st : GenState := { rng := seed * 2654435761 + 12345 }
  let mut out := #[]
  for _ in [0:n] do
    let (s, st') := step.run st
    st := st'
    out := out.push s
  out

end Test.Store.Gen
