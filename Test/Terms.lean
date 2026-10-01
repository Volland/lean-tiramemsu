/-
Term-dictionary refinement: seeded sequences of interns, lookups, decodes, commits and
rollbacks run in lock step on the pure `Dict` model (the proven one), on `ModelStore` and on
`SqliteStore` with the writer cache unbounded, at capacity 1 and off; every result and the
final `term` tables must be equal. Includes NUL and non-BMP strings, the rolled-back-term
scenario and the scenarios of the term-dictionary spec.
-/
import Test.Util

namespace Test.Terms

open Test Tiramemsu.Sqlite Tiramemsu.Store Tiramemsu.Storage Tiramemsu.Term Tiramemsu.Codec

--# @lat: [[codec#Tests]]

/-! ## Values -/

structure G where
  g : StdGen

def G.nat (s : G) (lo hi : Nat) : Nat × G := let (n, g) := randNat s.g lo hi; (n, ⟨g⟩)

def strs : Array String := #["urn:x:a", "a\x00b", "𝄞 clef", "longer than seven", "héllo wörld",
  "NUL\x00inside a long one", "€€€", "abcdefgh", "x"]
def iris : Array String := #["https://example.org/alice", "urn:x:abcdefghij", "http://ex/p",
  "http://www.opengis.net/ont/geosparql#wktLiteral", "urn:tiramemsu:node:12"]
def dbls : Array UInt64 := #[0, 0x8000000000000000, 1, 0x7FF8000000000000, 0x7FF0000000000001,
  0x3FF0000000000000, 0x7FF0000000000000, 0xFFEFFFFFFFFFFFFF, 0x000FFFFFFFFFFFFF]

def randValue (s : G) : Value × G :=
  let (k, s) := s.nat 0 9
  let (i, s) := s.nat 0 8
  let v : Value := match k with
    | 0 | 1 => .iri iris[i % iris.size]!
    | 2 => .str strs[i % strs.size]!
    | 3 => .langStr strs[i % strs.size]! (if i % 2 == 0 then "EN-gb" else "de")
    | 4 => .typed s!"POINT({i} 2)" "http://www.opengis.net/ont/geosparql#wktLiteral"
    | 5 => .double ⟨dbls[i % dbls.size]!⟩
    | 6 => .decimal (#["0.10", "1.5", "-0.0", "123456789.000000001", "x"][i % 5]!)
    | 7 => .int ((i : Int) - 4)
    | 8 => .typed (toString i) "http://www.w3.org/2001/XMLSchema#integer"
    | _ => .int (2 ^ 59 + i)
  (v, s)

/-! ## The three implementations -/

/-- The pure model with transactions: the state at `begin`, restored on rollback. -/
structure ModelDict where
  d : Dict := Dict.empty
  saved : Option Dict := none

inductive Op where
  | intern (v : Value)
  | lookup (v : Value)
  | decode (k : Nat)
  | commit
  | rollback
  deriving Repr, Inhabited

def randOps (seed n : Nat) : Array Op := Id.run do
  let mut s : G := ⟨mkStdGen seed⟩
  let mut ops := #[]
  for _ in [0:n] do
    let (k, s1) := s.nat 0 19
    let (v, s2) := randValue s1
    let (j, s3) := s2.nat 0 1000
    s := s3
    ops := ops.push (if k < 9 then .intern v else if k < 13 then .lookup v else if k < 17 then .decode j
      else if k < 19 then .commit else .rollback)
  return ops

def showR {α : Type} [Repr α] (r : Except CodecError α) : String := match r with
  | .ok a => s!"ok {reprStr a}"
  | .error e => s!"error {reprStr e}"

/-- Ids seen so far (for decodes), shared by all runs since results must agree. -/
def pickId (ids : Array ObjectId) (k : Nat) : ObjectId :=
  if ids.isEmpty then ⟨(k.toInt64) * 16⟩ else ids[k % ids.size]!

def runModel (ops : Array Op) : Array String × List TermRow := Id.run do
  let mut m : ModelDict := {}
  m := { m with saved := some m.d }
  let mut out := #[]
  let mut ids : Array ObjectId := #[]
  for op in ops do
    match op with
    | .intern v =>
      match m.d.internValue v with
      | .ok (x, d') => m := { m with d := d' }; ids := ids.push x; out := out.push (showR (.ok x : Except CodecError ObjectId))
      | .error e => out := out.push (showR (.error e : Except CodecError ObjectId))
    | .lookup v => out := out.push (showR (m.d.lookupValue v))
    | .decode k => out := out.push (showR (m.d.decode (pickId ids k)))
    | .commit => m := { m with saved := some m.d }; out := out.push "commit"
    | .rollback => m := { d := m.saved.getD Dict.empty, saved := m.saved }; out := out.push "rollback"
  return (out, m.d.rows.map Row.toStore)

/-- Runs the sequence on `SqliteStore` behind a writer cache. -/
def runSqlite (name : String) (cap : Option Nat) (ops : Array Op) : IO (Array String × List TermRow) := do
  let p ← freshPath s!"terms-{name}"
  let st ← match ← openFile p with
    | .ok st => pure st
    | .error e => throw (IO.userError (toString e))
  let cache ← WriterCache.new cap
  let mut out := #[]
  let mut ids : Array ObjectId := #[]
  let begin : IO Unit := do let _ ← (Store.begin st).run
  begin
  for op in ops do
    match op with
    | .intern v =>
      match ← ((intern v : CachedM SqliteM _) cache st).run with
      | .ok r =>
        if let .ok x := r then ids := ids.push x
        out := out.push (showR r)
      | .error e => out := out.push s!"store error {e}"
    | .lookup v =>
      match ← ((lookupValue v : CachedM SqliteM _) cache st).run with
      | .ok r => out := out.push (showR r)
      | .error e => out := out.push s!"store error {e}"
    | .decode k =>
      match ← ((decode (pickId ids k) : CachedM SqliteM _) cache st).run with
      | .ok r => out := out.push (showR r)
      | .error e => out := out.push s!"store error {e}"
    | .commit =>
      let _ ← (Store.commit st).run; cache.commit; begin; out := out.push "commit"
    | .rollback =>
      let _ ← (Store.rollback st).run; cache.rollback; begin; out := out.push "rollback"
  let _ ← (Store.rollback st).run
  cache.rollback
  let rows ← match ← (do dumpTerms (← st.conn) : SqlM _).run with
    | .ok rs => pure rs.toList
    | .error e => throw (IO.userError (toString e))
  st.close
  pure (out, rows)

/-- Runs the sequence on `ModelStore` (no cache). -/
def runModelStore (ops : Array Op) : Array String × List TermRow := Id.run do
  let init : ModelState := { counters := initialMeta.toList }
  let mut s : ModelStore := { ModelStore.ofState init with }
  let step {α : Type} (x : ModelM α) (s : ModelStore) : Option (α × ModelStore) :=
    match x s with
    | .ok (a, s') => some (a, s')
    | .error _ => none
  if let some ((), s') := step WriteStore.begin s then s := s'
  let mut out := #[]
  let mut ids : Array ObjectId := #[]
  for op in ops do
    match op with
    | .intern v =>
      match step (intern v : ModelM _) s with
      | some (r, s') =>
        s := s'
        if let .ok x := r then ids := ids.push x
        out := out.push (showR r)
      | none => out := out.push "store error"
    | .lookup v =>
      match step (lookupValue v : ModelM _) s with
      | some (r, _) => out := out.push (showR r)
      | none => out := out.push "store error"
    | .decode k =>
      match step (decode (pickId ids k) : ModelM _) s with
      | some (r, _) => out := out.push (showR r)
      | none => out := out.push "store error"
    | .commit =>
      if let some ((), s') := step (do WriteStore.commit; WriteStore.begin) s then s := s'
      out := out.push "commit"
    | .rollback =>
      if let some ((), s') := step (do WriteStore.rollback; WriteStore.begin) s then s := s'
      out := out.push "rollback"
  return (out, s.committed.terms)

def firstDiff (a b : Array String) : Option (Nat × String × String) := Id.run do
  for h : i in [0:max a.size b.size] do
    let x := a[i]?.getD "<none>"
    let y := b[i]?.getD "<none>"
    if x != y then return some (i, x, y)
  return none

/-- Committed rows only (the model state after a final rollback equals the last commit). -/
def runSeed (seed nops : Nat) : TestM Unit := do
  let ops := randOps seed nops
  let (mo, mrows) := runModel (ops.push .rollback)
  let (so, srows) := runModelStore (ops.push .rollback)
  match firstDiff mo so with
  | some (i, x, y) => check s!"seed {seed}: ModelStore step {i} ({reprStr ops[i]!})" false s!"model {x}, store {y}"
  | none => check s!"seed {seed}: ModelStore results" true
  for (name, cap) in [("unbounded", none), ("one", some 1), ("off", some 0)] do
    let (qo, qrows) ← runSqlite s!"{name}-{seed}" cap (ops.push .rollback)
    match firstDiff mo qo with
    | some (i, x, y) => check s!"seed {seed}: SQLite ({name}) step {i} ({reprStr ops[i]?})" false s!"model {x}, sqlite {y}"
    | none => check s!"seed {seed}: SQLite ({name}) results" true
    checkEq s!"seed {seed}: SQLite ({name}) term table" (reprStr qrows) (reprStr srows)
  checkEq s!"seed {seed}: model rows equal ModelStore rows" (reprStr mrows) (reprStr srows)

def scenarios : TestM Unit := do
  let p ← freshPath "terms-scenarios"
  let st ← match ← openFile p with
    | .ok st => pure st
    | .error e => throw (IO.userError (toString e))
  let cache ← WriterCache.new none
  let tx {α : Type} (x : CachedM SqliteM α) : IO (Except StoreError α) := (do
    Store.begin st; let a ← x cache st; Store.commit st; cache.commit; pure a : SqlM α).run
  -- datatype interned before the term
  let r ← tx (intern (.typed "POINT(1 2)" "http://www.opengis.net/ont/geosparql#wktLiteral"))
  checkEq "datatype interned before the term" (match r with | .ok (.ok x) => some (x.tag == .ok .typed, x.upayload.toNat) | _ => none) (some (true, 2))
  -- same IRI in two transactions
  let a ← tx (intern (.iri "https://example.org/alice"))
  let b ← tx (intern (.iri "https://example.org/alice"))
  check "same IRI in two transactions" (match a, b with | .ok (.ok x), .ok (.ok y) => x == y | _, _ => false)
  -- same text, different kinds
  let i1 ← tx (intern (.iri "urn:x:abcdefghij"))
  let i2 ← tx (intern (.str "urn:x:abcdefghij"))
  check "same text, different kinds" (match i1, i2 with
    | .ok (.ok x), .ok (.ok y) => x != y && x.tag == .ok .iri && y.tag == .ok .str | _, _ => false)
  -- NUL and non-BMP strings round trip through SQLite
  for s in ["NUL\x00inside a long string", "𝄞 musical symbol G clef"] do
    let x ← tx (intern (.str s))
    match x with
    | .ok (.ok id) =>
      let back ← (((decode id : CachedM SqliteM _) (← WriterCache.new (some 0)) st).run)
      check s!"SQLite round trip of {reprStr s}" (back == .ok (.ok (.str s)))
    | _ => check s!"intern {reprStr s}" false
  -- double and decimal rows
  let _ ← tx (intern (.double ((parseDouble "1E0").getD default)))
  let _ ← tx (intern (.double Double64.canonNaN))
  let _ ← tx (intern (literal "0.10" (some xsdDecimal) none))
  let rows ← (do dumpTerms (← st.conn) : SqlM _).run
  match rows with
  | .ok rs =>
    let find (lex : String) := rs.find? (·.lex == lex)
    check "double row 1.0E0" ((find "1.0E0").any fun r => r.num == some 0x3FF0000000000000)
    check "NaN row has NULL num" ((find "NaN").any fun r => r.num == none)
    check "decimal row 0.1 with the nearest binary64" ((find "0.1").any fun r => r.num == some 0x3FB999999999999A)
  | .error e => check "term rows" false (toString e)
  -- the idempotent intern changes nothing
  let before ← (do dumpTerms (← st.conn) : SqlM _).run
  let _ ← tx (intern (.str "a twenty-byte string"))
  let mid ← (do dumpTerms (← st.conn) : SqlM _).run
  let _ ← tx (intern (.str "a twenty-byte string"))
  let after ← (do dumpTerms (← st.conn) : SqlM _).run
  check "idempotent intern" (match before, mid, after with
    | .ok b, .ok m, .ok a => m.size == b.size + 1 && reprStr m == reprStr a | _, _, _ => false)
  -- the rolled-back term is not served from the cache
  let rb : SqlM Unit := do
    Store.begin st
    let _ ← (intern (.iri "urn:x:rolled-back") : CachedM SqliteM _) cache st
    Store.rollback st
  let _ ← rb.run
  cache.rollback
  let r ← ((lookupValue (.iri "urn:x:rolled-back") : CachedM SqliteM _) cache st).run
  check "rolled-back term is not served from the cache" (r == .ok (.ok none))
  -- unknown IRI and unknown datatype are absent and create nothing
  let n0 ← (do dumpTerms (← st.conn) : SqlM _).run
  let u1 ← ((lookupValue (.iri "urn:never-interned") : CachedM SqliteM _) cache st).run
  let u2 ← ((lookupValue (.typed "x" "urn:never-seen") : CachedM SqliteM _) cache st).run
  let n1 ← (do dumpTerms (← st.conn) : SqlM _).run
  check "unknown IRI and datatype are absent" (u1 == .ok (.ok none) && u2 == .ok (.ok none))
  check "lookups change nothing" (match n0, n1 with | .ok a, .ok b => reprStr a == reprStr b | _, _ => false)
  -- tag mismatch
  let mismatch ← ((decode (termId .str 1) : CachedM SqliteM _) cache st).run
  check "tag mismatch is InvalidTerm" (match mismatch with | .ok (.error (.invalidTerm _)) => true | _ => false)
  -- reader LRU sees committed rows only
  let rc ← ReaderCache.new 2
  let rd ← (do
    let r : Reader ← (SnapshotStore.beginRead : SqliteM Reader) st
    let v ← ((decode (termId .iri 1) : ReaderT ReaderCache ReaderM _) rc) r.conn
    (SnapshotStore.endRead r : SqliteM Unit) st
    pure v : SqlM _).run
  check "reader decode through the LRU" (rd == .ok (.ok (.iri "http://www.opengis.net/ont/geosparql#wktLiteral")))
  st.close
  -- dictionary full
  let full : Dict := { rows := [], next := 2 ^ 60 }
  check "dictionary full" (match full.intern ⟨.iri, "urn:x", none, none⟩ none with
    | .error (.idSpaceExhausted .term) => true | _ => false)

def main (args : List String) : IO UInt32 := do
  let flag (n : String) (d : Nat) : Nat := match args.dropWhile (· != n) with
    | _ :: v :: _ => v.toNat?.getD d
    | _ => d
  let seeds := flag "--seeds" 20
  let nops := flag "--ops" 200
  let ((), r) ← (do
    scenarios
    for s in [0:seeds] do runSeed (s + 1) nops : TestM Unit).run {}
  finish "terms" r

end Test.Terms
