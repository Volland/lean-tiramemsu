/-
The JSON forms of the Rust bridge (`bindings/json`): terms, times, statement ids, transaction
operations, reads on a view and reports, turned into transaction bodies (`TxProg`) and view
queries (`ReadProg`). The oracle driver and the M6 bridge share them. Shell module (unverified).
-/
import Tiramemsu.Engine.Exec
import Tiramemsu.Engine.Transact
import Tiramemsu.Shell.Json

namespace Tiramemsu.Shell

open Tiramemsu.Json Tiramemsu.Codec Tiramemsu.Engine Tiramemsu.Store

--# @lat: [[engine#JSON Bridge]]

/-! ## Terms -/

/-- `x` as serde_json prints an `f64` (Ryu's shortest form). -/
def ryuText (x : Double64) : String :=
  if x.isZero then (if x.neg then "-0.0" else "0.0") else
  let (c, k) := shortestDec x
  let ds := toString c
  let n : Int := ds.length
  let kk := n + k
  let sign := if x.neg then "-" else ""
  let zeros (m : Int) : String := String.ofList (List.replicate m.toNat '0')
  let body :=
    if 0 ≤ k ∧ kk ≤ 16 then ds ++ zeros k ++ ".0"
    else if 0 < kk ∧ kk ≤ 16 then
      (ds.take kk.toNat).toString ++ "." ++ (ds.drop kk.toNat).toString
    else if -5 < kk ∧ kk ≤ 0 then "0." ++ zeros (-kk) ++ ds
    else if n == 1 then ds ++ "e" ++ toString (kk - 1)
    else (ds.take 1).toString ++ "." ++ (ds.drop 1).toString ++ "e" ++ toString (kk - 1)
  sign ++ body

/-- Whether a finite double has a fractional part. -/
def hasFraction (x : Double64) : Bool :=
  !x.isZero && (shortestDec x).2 < 0

/-- The JSON form of a term. -/
def bridgeTermJ : Value → Json
  | .iri s => .obj #[("iri", .str s)]
  | .node n => .obj #[("node", .int n)]
  | .bnode n => .obj #[("bnode", .int n)]
  | .stmt n => .obj #[("stmt", .int n)]
  | .tx n => .obj #[("tx", .int n)]
  | .int i => if i.natAbs ≤ 2 ^ 53 then .int i else .obj #[("$int", .str (intText i))]
  | .bool b => .bool b
  | .str s => .str s
  | .langStr lex lang => .obj #[("lex", .str lex), ("lang", .str lang)]
  | v@(.double x) =>
    if x.isFinite && hasFraction x then .num (ryuText x)
    else .obj #[("lex", .str v.lexical), ("datatype", .str (v.datatype.getD ""))]
  | v => .obj #[("lex", .str v.lexical), ("datatype", .str (v.datatype.getD ""))]

/-- A term from its JSON form. -/
def termOfJ (j : Json) : Except String Value :=
  let str (k : String) : Option String := j.getStr? k
  let nat (k : String) : Option Nat := match j.get? k with
    | some (.int i) => if 0 ≤ i ∧ i < 2 ^ 64 then some i.toNat else none
    | _ => none
  match j with
  | .str s => .ok (.str s)
  | .bool b => .ok (.bool b)
  | .int i =>
    if -(2 ^ 63) ≤ i ∧ i < 2 ^ 63 then .ok (.int i)
    else match parseDouble (toString i) with
      | some x => if x.isFinite then .ok (.double x) else .error s!"number {i} is not a term"
      | none => .error s!"number {i} is not a term"
  | .num lex =>
    match parseDouble lex with
    | some x => if x.isFinite then .ok (.double x) else .error s!"number {lex} is not a term"
    | none => .error s!"number {lex} is not a term"
  | .obj _ =>
    if let some s := str "iri" then .ok (.iri s)
    else if let some n := nat "node" then .ok (.node n)
    else if let some n := nat "bnode" then .ok (.bnode n)
    else if let some n := nat "stmt" then .ok (.stmt n)
    else if let some n := nat "tx" then .ok (.tx n)
    else if let some d := str "$int" then .ok (bigInteger d)
    else if let some lex := str "lex" then .ok (literal lex (str "datatype") (str "lang"))
    else .error s!"{j.compress} is not a term"
  | _ => .error s!"{j.compress} is not a term"

/-- An optional epoch-millisecond bound: a number, or an RFC 3339 date or date-time. -/
def timeOfJ : Json → Except String (Option Int64)
  | .null => .ok none
  | .int i => if -(2 ^ 63) ≤ i ∧ i < 2 ^ 63 then .ok (some (Int64.ofInt i))
              else .error s!"time {i} is not an integer of milliseconds"
  | .num n => .error s!"time {n} is not an integer of milliseconds"
  | .str s =>
    match parseDateTime s with
    | some (ms, _) => .ok (some (Int64.ofInt ms))
    | none => match parseDate s with
      | some d => .ok (some (Int64.ofInt (d * 86400000)))
      | none => .error s!"time {s.quote} is not a date or date-time"
  | j => .error s!"{j.compress} is not a time"

/-- A statement id: a number or `{"stmt": n}` (Rust's `Eid::new(n)`). -/
def eidOfJ (j : Json) : Except String Nat :=
  match j with
  | .int i => if 0 ≤ i ∧ i < 2 ^ 64 then .ok i.toNat else .error s!"{i} is not a statement id"
  | .obj _ => match j.get? "stmt" with
    | some (.int i) => if 0 ≤ i ∧ i < 2 ^ 64 then .ok i.toNat else .error s!"{j.compress} is not a statement id"
    | _ =>
      match j.getStr? "ref" with
      | some name => .error s!"no earlier operation is named {name.quote}"
      | none => .error s!"{j.compress} is not a statement id"
  | _ => .error s!"{j.compress} is not a statement id"

/-- The `STMT` id of a statement number (`Unsupported` for a non-zero origin). -/
def eidId (n : Nat) : Except Error ObjectId :=
  match encodeAlloc .stmt n with
  | .ok x => .ok x
  | .error e => .error (Error.ofCodec .value e)

/-! ## Reports and rows -/

def retKindJ (k : RetKind) : Json := .str k.name

def reportJ (r : TxReport) : Json :=
  let ids (xs : Array ObjectId) : Json := .arr (xs.map fun e => .int e.counter.toNat)
  let kinds (xs : Array (ObjectId × RetKind)) : Json :=
    .arr (xs.map fun (e, k) => .obj #[("eid", .int e.counter.toNat), ("kind", retKindJ k)])
  .obj #[("t", .int r.t.toInt), ("instant", .int r.instant.toInt), ("asserted", ids r.asserted),
    ("existing", ids r.existing), ("retracted", kinds r.retracted),
    ("superseded", .arr (r.superseded.map fun (a, b) =>
      .obj #[("old", .int a.counter.toNat), ("new", .int b.counter.toNat)])),
    ("memberships", ids r.memberships), ("membershipsRetracted", kinds r.membershipsRetracted)]

def eventJ (e : Event) : Json :=
  .obj #[("t", .int e.t.toInt), ("eid", .int e.eid.counter.toNat),
    ("op", .str (match e.op with | .assert => "assert" | .retract => "retract")),
    ("kind", match e.kind with | some k => retKindJ k | none => .null)]

/-! ## Transaction operations -/

def argFail {α : Type} (msg : String) : TxProg α := TxProg.abort (.invalidArgument msg)

def ofArg {α : Type} : Except String α → TxProg α
  | .ok a => pure a
  | .error m => argFail m

def ofErr {α : Type} : Except Error α → TxProg α
  | .ok a => pure a
  | .error e => TxProg.abort e

/-- A required term of an operation, encoded (interning). -/
def termOf (op : Json) (key : String) : TxProg ObjectId := do
  match op.get? key with
  | none => argFail s!"`{key}` is required"
  | some j => TxProg.verb (.encode (← ofArg (termOfJ j)))

/-- A pattern position: `some none` for any, `none` when the term is not stored. -/
def patternOf (op : Json) (key : String) : TxProg (Option (Option ObjectId)) := do
  match op.get? key with
  | none | some .null => pure (some none)
  | some j => return (← TxProg.verb (.lookup (← ofArg (termOfJ j)))).map some

def eidArg (op : Json) (key : String) : TxProg ObjectId := do
  match op.get? key with
  | none => argFail s!"`{key}` is required"
  | some j => ofErr (eidId (← ofArg (eidOfJ j)))

def validOf (op : Json) : Except String Valid := do
  let b (k : String) : Except String (Option Int64) := match op.get? k with
    | some j => timeOfJ j
    | none => .ok none
  pure { vFrom := ← b "validFrom", vTo := ← b "validTo" }

def assertOptsOf (op : Json) : Except String AssertOpts := do
  let on ← match op.getStr? "onExisting" with
    | none | some "return" => pure OnExisting.return_
    | some "confirm" => pure .confirm
    | some other => throw s!"unknown onExisting {other.quote}"
  pure { valid := ← validOf op, onExisting := on }

def patchOf (j : Json) : TxProg Patch := do
  match j with
  | .obj kvs =>
    let mut p : Patch := {}
    for (k, v) in kvs do
      match k with
      | "o" => p := { p with o := some (← ofArg (termOfJ v)) }
      | "validFrom" => p := { p with vFrom := some (← ofArg (timeOfJ v)) }
      | "validTo" => p := { p with vTo := some (← ofArg (timeOfJ v)) }
      | "s" | "p" =>
        let _ ← ofArg (termOfJ v)
        TxProg.abort (.invalidPatch s!"{k} cannot be patched; supersede changes only o, v_from and v_to")
      | other =>
        let _ ← ofArg (termOfJ v)
        TxProg.abort (.invalidPatch s!"unexpected patch field {other}")
    pure p
  | _ => argFail "`patch` must be an object"

def idJ (x : ObjectId) : TxProg Json := do return bridgeTermJ (← TxProg.verb (.decode x))

def eidsJ (xs : Array ObjectId) : Json := .arr (xs.map fun e => .int e.counter.toNat)

/-- One operation of the bridge's `transact`. -/
def opProg (op : Json) : TxProg Json := do
  let some name := op.getStr? "op" | argFail "an operation needs an `op`"
  match name with
  | "assert" => do
    let s ← termOf op "s"; let p ← termOf op "p"; let o ← termOf op "o"
    let a ← TxProg.verb (.assert s p o (← ofArg (assertOptsOf op)))
    pure (.obj #[("eid", .int a.eid.counter.toNat), ("new", .bool a.isNew)])
  | "create" => do
    let s ← termOf op "s"; let p ← termOf op "p"; let o ← termOf op "o"
    let e ← TxProg.verb (.create s p o (← ofArg (validOf op)))
    pure (.obj #[("eid", .int e.counter.toNat), ("new", .bool true)])
  | "retract" => return .bool (← TxProg.verb (.retract (← eidArg op "eid")))
  | "retractMatching" => do
    let s ← patternOf op "s"; let p ← patternOf op "p"; let o ← patternOf op "o"
    match s, p, o with
    | some s, some p, some o => return eidsJ (← TxProg.verb (.retractMatching s p o))
    | _, _, _ => pure (.arr #[])
  | "supersede" => do
    let root ← eidArg op "eid"
    let some pj := op.get? "patch" | argFail "`patch` is required"
    let e ← TxProg.verb (.supersede root (← patchOf pj))
    pure (.obj #[("eid", .int e.counter.toNat)])
  | "confirm" => do
    let e ← TxProg.verb (.confirm (← eidArg op "eid"))
    pure (.obj #[("eid", .int e.counter.toNat)])
  | "meta" => do
    let p ← termOf op "p"; let o ← termOf op "o"
    let e ← TxProg.verb (.metadata p o)
    pure (.obj #[("eid", .int e.counter.toNat)])
  | "upsert" => do
    let p ← termOf op "p"; let o ← termOf op "o"
    idJ (← TxProg.verb (.upsert p o))
  | "newNode" => do idJ (← TxProg.verb .newNode)
  | "newBNode" => do idJ (← TxProg.verb .newBNode)
  | "setVolatile" => do
    let s ← termOf op "s"; let k ← termOf op "key"; let v ← termOf op "value"
    TxProg.verb (.setVolatile s k v)
    pure .null
  | "clearVolatile" => do
    let s ← termOf op "s"; let k ← termOf op "key"
    TxProg.verb (.clearVolatile s k)
    pure .null
  | "addToGraph" => do
    let e ← eidArg op "eid"; let g ← termOf op "graph"
    let (m, added) ← TxProg.verb (.addToGraph e g (← ofArg (assertOptsOf op)))
    pure (.obj #[("eid", .int m.counter.toNat), ("new", .bool added)])
  | "removeFromGraph" => do
    let e ← eidArg op "eid"; let g ← termOf op "graph"
    return .bool (← TxProg.verb (.removeFromGraph e g))
  | "clearGraph" => do return eidsJ (← TxProg.verb (.clearGraph (← termOf op "graph")))
  | "createGraph" => do
    let a ← TxProg.verb (.createGraph (← termOf op "graph"))
    pure (.obj #[("eid", .int a.eid.counter.toNat)])
  | "dropGraph" => do return eidsJ (← TxProg.verb (.dropGraph (← termOf op "graph")))
  | "fail" => TxProg.abort (.custom "body aborted")
  | other => argFail s!"unknown transaction operation {other.quote}"

/-- The operations of a `transact`, in order; their results. -/
def opsProg (ops : Array Json) : TxProg (Array Json) := do
  let mut out := #[]
  for op in ops do out := out.push (← opProg op)
  pure out

/-- Transaction options from JSON. -/
def txOptionsOf : Json → Except String TxOptions
  | .null => .ok {}
  | .obj kvs => kvs.foldlM (init := ({} : TxOptions)) fun o (k, v) =>
    match k, v with
    | "dryRun", .bool b => .ok { o with dryRun := b }
    | "dryRun", _ => .error "dryRun must be a boolean"
    | "maxCascade", .int i => if 0 ≤ i then .ok { o with maxCascade := i.toNat } else .error "maxCascade must be an integer"
    | "maxCascade", _ => .error "maxCascade must be an integer"
    | other, _ => .error s!"unknown transaction option {other.quote}"
  | _ => .error "options must be an object"

/-! ## Reads on a view -/

def rfail {α : Type} (msg : String) : ReadProg α := .fail (.invalidArgument msg)

def rofArg {α : Type} : Except String α → ReadProg α
  | .ok a => pure a
  | .error m => rfail m

/-- The view of a read, from `{"kind", "tx", "instant", "validAt"}`; `null` is now. -/
def viewOfJ (j : Json) : Except String View.ViewSpec := do
  let get (k : String) : Option Json := match j.get? k with
    | some .null | none => none
    | some x => some x
  let tx : View.TxSpec ← match (j.getStr? "kind").getD "now" with
    | "now" => pure .now
    | "history" => pure .history
    | "asOf" =>
      match get "tx", get "instant" with
      | some (.int t), none =>
        if 0 ≤ t then pure (.asOf (.tx (Int64.ofInt (min t (2 ^ 63 - 1)))))
        else throw "tx must be a non-negative integer"
      | some _, none => throw "tx must be a non-negative integer"
      | none, some i => do
        match ← timeOfJ i with
        | some ms => pure (.asOf (.instant ms))
        | none => throw "a time is required"
      | _, _ => throw "an asOf view needs exactly one of tx and instant"
    | other => throw s!"unknown view kind {other.quote}"
  let valid ← match get "validAt" with
    | some d => do
      match ← timeOfJ d with
      | some ms => pure (ValidSel.at ms)
      | none => throw "a time is required"
    | none => pure .unfiltered
  pure { tx, valid }

def rterm (x : ObjectId) : ReadProg Json := do return bridgeTermJ (← ReadProg.query (.decode x))

/-- One read of the bridge on the program's view. -/
def readProg (op : String) (args : Json) : ReadProg Json := do
  match op with
  | "triples" => do
    let look (k : String) : ReadProg (Option (Option ObjectId)) := do
      match args.get? k with
      | none | some .null => pure (some none)
      | some j => return (← ReadProg.query (.lookup (← rofArg (termOfJ j)))).map some
    let s ← look "s"; let p ← look "p"; let o ← look "o"
    match s, p, o with
    | some s, some p, some o =>
      let rows ← ReadProg.query (.triples s p o)
      let mut out := #[]
      for r in rows do
        let ms (x : Option Int64) : Json := match x with | some v => .int v.toInt | none => .null
        out := out.push (.obj #[("eid", .int (ObjectId.mk r.eid).counter.toNat),
          ("s", ← rterm ⟨r.s⟩), ("p", ← rterm ⟨r.p⟩), ("o", ← rterm ⟨r.o⟩),
          ("tAdd", .int r.tAdd.toInt), ("tRet", ms r.tRet), ("validFrom", ms r.vFrom),
          ("validTo", ms r.vTo),
          ("retKind", match r.retKind.bind RetKind.ofCode? with | some k => retKindJ k | none => .null)])
      pure (.arr out)
    | _, _, _ => pure (.arr #[])
  | "events" =>
    let since := match args.get? "since" with
      | some (.int i) => if 0 ≤ i then Int64.ofInt (min i (2 ^ 63 - 1)) else 0
      | _ => 0
    return .arr ((← ReadProg.query (.events since)).map eventJ)
  | "graphs" => do
    let gs ← ReadProg.query .graphs
    let mut out := #[]
    for g in gs do out := out.push (← rterm g)
    pure (.arr out)
  | "graphMembers" => do
    let some gj := args.get? "graph" | rfail "`graph` is required"
    if gj == .null then rfail "`graph` is required" else
    match ← ReadProg.query (.lookup (← rofArg (termOfJ gj))) with
    | some g => return eidsJ (← ReadProg.query (.graphMembers g))
    | none => pure (.arr #[])
  | "values" => do
    let req (k : String) : ReadProg (Option ObjectId) := do
      match args.get? k with
      | none | some .null => rfail s!"`{k}` is required"
      | some j => ReadProg.query (.lookup (← rofArg (termOfJ j)))
    let s ← req "s"; let k ← req "key"
    match s, k with
    | some s, some k => do
      let vs ← ReadProg.query (.values s k)
      let mut out := #[]
      for x in vs do out := out.push (← rterm x)
      pure (.arr out)
    | _, _ => pure (.arr #[])
  | "dependents" => do
    let ej ← match args.get? "eid" with
      | none | some .null => rfail "`eid` is required"
      | some j => pure j
    let n ← rofArg (eidOfJ ej)
    match eidId n with
    | .ok e => return eidsJ (← ReadProg.query (.dependents e))
    | .error e => .fail e
  | other => rfail s!"unknown read operation {other.quote}"

/-- The queries of a speculation (`with`), each on the speculative now view. -/
def queriesProg (qs : Array Json) : ReadProg Json := do
  let mut out := #[]
  for q in qs do
    let some op := q.getStr? "op" | rfail "a query needs an `op`"
    out := out.push (← readProg op q)
  pure (.arr out)

/-- An error as the bridge reports it. -/
def errorJ (e : Error) : Json := .obj #[("code", .str e.code), ("message", .str (toString e))]

end Tiramemsu.Shell
