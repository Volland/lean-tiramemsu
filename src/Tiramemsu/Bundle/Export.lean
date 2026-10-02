/-
Fact bundles (Rust `tm-core/bundle.rs`): a belief with its layers and evidence as a portable
value, exported from any view and imported idempotently.

Export:
1. the root's dependents in the view (layers, citing statements, memberships), then the
   downward closure over every candidate's statement references (only visible ones);
2. exclusions: a transaction subject or object, a reserved predicate a user write would be
   refused (`sys:inGraph` excepted), a reference to an invisible statement; propagated to every
   statement referencing an excluded one; an excluded root is `Unsupported`;
3. members: the surviving dependents and their downward closure;
4. order: references first, ties by eid, reference-cycle members last in eid order;
5. terms: values, local statement ids, anonymous nodes labelled by first appearance.
Verified module: imports only `Init`, `Std` and verified modules.
-/
import Tiramemsu.View.Read

namespace Tiramemsu.Bundle

open Tiramemsu.Store Tiramemsu.Codec Tiramemsu.Engine Tiramemsu.View

--# @lat: [[query#Fact Bundles]]

/-- A subject or object of a bundle statement. -/
inductive BTerm where
  | value (v : Value)
  /-- A bundle-local statement id. -/
  | stmt (n : Nat)
  /-- A bundle-local anonymous node label. -/
  | node (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One bundle statement: its local id (its position), content and valid time. -/
structure BStmt where
  local_ : Nat
  s : BTerm
  p : Value
  o : BTerm
  vFrom : Option Int64 := none
  vTo : Option Int64 := none
  deriving Repr, DecidableEq, Inhabited

/-- A bundle: ordered statements and the root's local id. -/
structure Bundle where
  root : Nat
  statements : List BStmt
  deriving Repr, DecidableEq, Inhabited

/-- The program monad of bundle reads: engine errors over read programs. -/
abbrev BM := ExceptT Error RProg

def liftR {α : Type} (p : RProg α) : BM α := ExceptT.lift p

/-- The statement references of a row (subject and object that are statement ids). -/
def refs (r : TripleRow) : List Int64 :=
  [r.s, r.o].filter fun x => (ObjectId.mk x).tagBits == Tag.stmt.toUInt64

def tagOf (x : Int64) : Option Tag := (ObjectId.mk x).tag.toOption

/-- Topological order of `n` items (references first), ties by smallest index; items on a
reference cycle are left out. -/
def topological (n : Nat) (refsOf : Nat → List Nat) : List Nat :=
  let deps := (List.range n).map fun i => (refsOf i).eraseDups
  go (n + 1) [] deps
where
  go : Nat → List Nat → List (List Nat) → List Nat
    | 0, out, _ => out
    | fuel + 1, out, deps =>
      match (List.range n).find? fun i => !out.contains i && (deps.getD i []).all out.contains with
      | some i => go fuel (out ++ [i]) deps
      | none => out

/-- Why a statement cannot be bundled. -/
inductive Exclusion where
  | transaction
  | engine (p : String)
  | invisible (e : Int64)
  | excluded (e : Int64)
  deriving Repr, DecidableEq, Inhabited

def stmtText (e : Int64) : String := renderSkolem .stmt (ObjectId.mk e).counter.toNat

def Exclusion.feature : Exclusion → String
  | .transaction => "bundle root that references a transaction"
  | .engine p => s!"bundle root with the engine predicate {p}"
  | .invisible e => s!"bundle root that references {stmtText e}, which is not in the view"
  | .excluded e => s!"bundle root that references {stmtText e}, which cannot be bundled"

def decodeB (x : Int64) : BM Value := do
  match ← liftR (Term.decode (m := RProg) ⟨x⟩) with
  | .ok v => return v
  | .error e => throw (Error.ofCodec .value e)

/-- Exports the bundle of `root` from a view. -/
def exportBundle (vs : ViewSpec) (root : ObjectId) : BM Bundle := do
  let v ← liftR (resolve vs)
  if !(← liftR (visible v root.raw)) then throw (.notLive root)
  -- 1. candidates
  let deps ← liftR (dependentsIn v root.raw)
  let fuel := (← liftR walkFuel) + deps.length + 1
  let (order, rows, invisible) ← expand v fuel deps 0 [] []
  -- 2. exclusions
  let mut excluded : List (Int64 × Exclusion) := []
  for e in order do
    let some r := rows.lookup e | continue
    if tagOf r.s == some .tx || tagOf r.o == some .tx then
      excluded := excluded ++ [(e, .transaction)]
      continue
    let p ← match ← decodeB r.p with
      | .iri s => pure s
      | other => pure other.lexical
    let sTag := (tagOf r.s).getD .iri
    if p != Vocab.sysInGraph && (checkReserved p sTag).isOk == false then
      excluded := excluded ++ [(e, .engine p)]
      continue
    if let some x := invisible.lookup e then
      excluded := excluded ++ [(e, .invisible x)]
  let excl := propagate rows order (order.length + 1) excluded
  if let some why := excl.lookup root.raw then throw (.unsupported why.feature)
  -- 3. members
  let isEx (e : Int64) : Bool := (excl.lookup e).isSome
  let members0 := deps.filter fun e => !isEx e
  let members := closure rows (rows.length + 1) members0 0
  -- 4. order
  let sortedM := members.mergeSort fun a b => decide (a.toInt ≤ b.toInt)
  let idx (e : Int64) : Option Nat := sortedM.idxOf? e
  let refIdx (i : Nat) : List Nat :=
    match rows.lookup (sortedM.getD i 0) with
    | some r => (refs r).filterMap idx
    | none => []
  let topo := topological sortedM.length refIdx
  let order := topo ++ (List.range sortedM.length).filter fun i => !topo.contains i
  let localOf (e : Int64) : Nat := (order.idxOf? ((idx e).getD 0)).getD 0
  -- 5. terms
  let mut anon : List (Int64 × Nat) := []
  let mut out : List BStmt := []
  for (k, i) in order.zipIdx.map (fun (i, k) => (k, i)) do
    let e := sortedM.getD i 0
    let some r := rows.lookup e | continue
    let mut ts : List BTerm := []
    for x in [r.s, r.o] do
      match tagOf x with
      | some .stmt => ts := ts ++ [.stmt (localOf x)]
      | some .node | some .bnode =>
        match anon.lookup x with
        | some n => ts := ts ++ [.node n]
        | none =>
          ts := ts ++ [.node anon.length]
          anon := anon ++ [(x, anon.length)]
      | _ => ts := ts ++ [.value (← decodeB x)]
    out := out ++ [{ local_ := k, s := ts.getD 0 default, p := ← decodeB r.p, o := ts.getD 1 default,
                     vFrom := r.vFrom, vTo := r.vTo }]
  return { root := localOf root.raw, statements := out }
where
  /-- Breadth-first: loads each candidate and adds its visible references. -/
  expand (v : Store.View) : Nat → List Int64 → Nat → List (Int64 × TripleRow) → List (Int64 × Int64) →
      BM (List Int64 × List (Int64 × TripleRow) × List (Int64 × Int64))
    | 0, order, _, rows, inv => return (order, rows, inv)
    | fuel + 1, order, i, rows, inv => do
      match order[i]? with
      | none => return (order, rows, inv)
      | some e =>
        let some r ← liftR (lookupRow v e) | throw (.notLive ⟨e⟩)
        let rows := rows ++ [(e, r)]
        let mut order := order
        let mut inv := inv
        for x in refs r do
          if order.contains x || (inv.lookup e).isSome then continue
          if ← liftR (visible v x) then order := order ++ [x]
          else inv := inv ++ [(e, x)]
        expand v fuel order (i + 1) rows inv
  lookupRow (v : Store.View) (e : Int64) : RProg (Option TripleRow) := do
    match ← RProg.lift (.triple e) with
    | some r => return if v.admits r then some r else none
    | none => return none
  propagate (rows : List (Int64 × TripleRow)) (order : List Int64) :
      Nat → List (Int64 × Exclusion) → List (Int64 × Exclusion)
    | 0, ex => ex
    | fuel + 1, ex =>
      let more := order.filterMap fun e =>
        if (ex.lookup e).isSome then none
        else (rows.lookup e).bind fun r => ((refs r).find? fun x => (ex.lookup x).isSome).map (e, ·)
      if more.isEmpty then ex else propagate rows order fuel (ex ++ more.map fun (e, x) => (e, .excluded x))
  closure (rows : List (Int64 × TripleRow)) : Nat → List Int64 → Nat → List Int64
    | 0, ms, _ => ms
    | fuel + 1, ms, i =>
      match ms[i]? with
      | none => ms
      | some e =>
        let rs := ((rows.lookup e).map refs).getD []
        closure rows fuel (rs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) ms) (i + 1)

end Tiramemsu.Bundle
