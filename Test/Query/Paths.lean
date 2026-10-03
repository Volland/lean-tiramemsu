/-
Path scenarios (path-evaluation) and a brute-force walk enumerator over small random graphs as a
test oracle for every mode: walks are enumerated directly from the model state's statements and
matched against the expression with a naive regular-expression matcher, independently of the
automaton and of the search.
-/
import Test.Query.Util

namespace Test.Query.Paths

open Tiramemsu Tiramemsu.Store Tiramemsu.Engine Tiramemsu.Codec Tiramemsu.IR Tiramemsu.Sem Tiramemsu.Path
open Test
open Test.Store (v sysV assertV createV enc day retractE between)
open Test.Query

/-- Runs the engine on a model state from a start value. -/
def runP (st : ModelState) (start : Value) (text : String) (mode : PathMode := .reach)
    (maxHops : Option Nat := none) (graphs : Option (List Value) := none) (timed : Option (Option Int) := none)
    (view : View.ViewSpec := {}) (opts : PathOpts := {}) : Except QError (List PathRow) :=
  let prog : Exec.EvM (List PathRow) := do
    let expr ← parseText text
    let some s ← Exec.lookupE start | return []
    let gs ← match graphs with
      | none => pure none
      | some gs => do pure (some (← gs.filterMapM Exec.lookupE))
    run opts { start := s, expr, mode, maxHops, view, graphs := gs, timed }
  match prog.run.onModel st with
  | .ok r => r
  | .error e => .error (.store e)

def idOf (st : ModelState) (x : Value) : Int64 :=
  match (Term.lookupValue (m := SnapM) x) st with
  | .ok (.ok (some o)) => o.raw
  | _ => 0

def endsOf (rows : List PathRow) : List (Int64 × Nat) := rows.map fun r => (r.end, r.hops)

def expectEnds (name : String) (st : ModelState) (r : Except QError (List PathRow)) (want : List (Value × Nat)) : TestM Unit :=
  match r with
  | .ok rows =>
    checkEq name ((endsOf rows).mergeSort fun a b => decide (a.1.toInt ≤ b.1.toInt))
      ((want.map fun (x, h) => (idOf st x, h)).mergeSort fun a b => decide (a.1.toInt ≤ b.1.toInt))
  | .error e => check name false s!"error {e}"

def knows (a b : String) : TxProg Unit := do let _ ← assertV (v a) (v "knows") (v b); pure ()

/-! ## Brute force -/

/-- A naive matcher of the expression's language. -/
def matchRE : Nat → RE → List Letter → Bool
  | 0, _, _ => false
  | fuel + 1, r, w =>
    match r with
    | .empty => false
    | .eps => w.isEmpty
    | .sym c => match w with | [l] => c.matches l | _ => false
    | .seq a b => (List.range (w.length + 1)).any fun i => matchRE fuel a (w.take i) && matchRE fuel b (w.drop i)
    | .alt a b => matchRE fuel a w || matchRE fuel b w
    | .star a => w.isEmpty || (List.range w.length).any fun i =>
        matchRE fuel a (w.take (i + 1)) && matchRE fuel (.star a) (w.drop (i + 1))

def iriOfId (st : ModelState) (x : Int64) : String :=
  match (Term.decode (m := SnapM) ⟨x⟩) st with
  | .ok (.ok (.iri s)) => s
  | _ => ""

/-- Rust's relationship view on a model state (no `sys:isEdge` flags in these graphs). -/
def isRel (st : ModelState) (p o : Int64) : Bool :=
  let iri := iriOfId st p
  !(iri == Vocab.rdfType || iri.startsWith Vocab.sys) &&
    (match (ObjectId.mk o).tag with | .ok t => t.isSubject | .error _ => false)

/-- Every hop from a node: the letter, the hop and the node reached. -/
def hopsFrom (st : ModelState) (x : Int64) : List (Letter × Hop × Int64) :=
  let vis := st.triples.filter fun r => r.tRet.isNone
  let out := (vis.filter (·.s == x)).map fun r =>
    (Letter.stored (iriOfId st r.p) (isRel st r.p r.o) .out, ({ eid := r.eid, pred := r.p, dir := .out, kind := 0 } : Hop), r.o)
  let inn := (vis.filter (·.o == x)).map fun r =>
    (Letter.stored (iriOfId st r.p) (isRel st r.p r.o) .inn, ({ eid := r.eid, pred := r.p, dir := .inn, kind := 0 } : Hop), r.s)
  let vout := (vis.filter (·.eid == x)).flatMap fun r =>
    [VKind.subject, .object, .predicate].map fun k =>
      (Letter.virt k .out, ({ eid := r.eid, pred := virtualPredId k, dir := .out, kind := k.code } : Hop), k.part r)
  let vin := vis.flatMap fun r =>
    ([VKind.subject, .object, .predicate].filter (fun k => k.part r == x)).map fun k =>
      (Letter.virt k .inn, ({ eid := r.eid, pred := virtualPredId k, dir := .inn, kind := k.code } : Hop), r.eid)
  out ++ inn ++ vout ++ vin

/-- Every walk of at most `n` hops from `x`: letters, hops (with the nodes reached). -/
def walks (st : ModelState) : Nat → Int64 → List (List Letter × List (Hop × Int64))
  | 0, _ => [([], [])]
  | n + 1, x => ([], []) :: (hopsFrom st x).flatMap fun (l, h, y) =>
      (walks st n y).map fun (ls, hs) => (l :: ls, (h, y) :: hs)

def keySeq (hs : List (Hop × Int64)) : List (Int × Nat × Nat) := hs.map (·.1.key)

def trailOk (hs : List (Hop × Int64)) : Bool := (hs.map (·.1.identity)).eraseDups.length == hs.length

/-! ## Random graphs and expressions -/

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def pick {α : Type} [Inhabited α] (s : Nat) (xs : List α) : α := xs.getD ((s / 65536) % xs.length) default

def randAtom (s : Nat) : PathExpr :=
  .atom (pick s ["urn:tiramemsu:v:knows", "urn:tiramemsu:v:likes", QVocab.sysSubject, QVocab.sysObject,
    QVocab.sysAnyRelationship])

def randExpr : Nat → Nat → PathExpr × Nat
  | 0, s => (randAtom s, lcg s)
  | d + 1, s =>
    let s1 := lcg s
    let k := (s1 / 65536) % 9
    let (a, s2) := randExpr d s1
    let (b, s3) := randExpr d s2
    let e : PathExpr :=
      if k == 0 then .inv a else if k == 1 then .seq [a, b] else if k == 2 then .alt [a, b]
      else if k == 3 then .star a else if k == 4 then .plus a else if k == 5 then .opt a
      else if k == 6 then .rep a 1 (some 2) else randAtom s1
    (e, s3)

def randGraph (seed : Nat) : List (TxProg Unit) :=
  let names := ["a", "b", "c", "d"]
  let rec go : Nat → Nat → List (String × String × String) → List (String × String × String)
    | 0, _, acc => acc
    | k + 1, s, acc =>
      let s1 := lcg s; let s2 := lcg s1; let s3 := lcg s2
      go k s3 (acc ++ [(pick s1 names, pick s2 ["knows", "likes"], pick s3 names)])
  let es := go (3 + seed % 5) (lcg (seed + 7)) []
  [do
    for (a, p, b) in es do
      let _ ← createV (v a) (v p) (v b)
    -- a layer on the first statement
    let _ ← assertV (.stmt 1) (v "likes") (v "c")
    pure ()]

/-- Compares every mode with the brute force on one graph, start and expression. -/
def oracleCheck (name : String) (st : ModelState) (start : Int64) (e : PathExpr) (bound : Nat) : TestM Unit := do
  let re := toRE false e
  let ws := walks st bound start
  let acc := ws.filter fun (ls, _) => matchRE 64 re ls
  let endOf (hs : List (Hop × Int64)) : Int64 := (hs.getLast?.map (·.2)).getD start
  let ends := (acc.map fun (_, hs) => endOf hs).eraseDups
  let minLen (y : Int64) : Nat := ((acc.filter fun (_, hs) => endOf hs == y).map (·.2.length)).foldl min 1000
  let ctx (mode : PathMode) := runPathFrom st start e mode bound
  -- REACH
  match ctx .reach with
  | .ok rows =>
    if rows.length > 1 then modify fun r => { r with notes := r.notes.push "nonempty" }
    checkEq s!"{name} reach" ((rows.map fun r => (r.end, r.hops)).mergeSort fun a b => decide (a.1.toInt ≤ b.1.toInt))
      ((ends.map fun y => (y, minLen y)).mergeSort fun a b => decide (a.1.toInt ≤ b.1.toInt))
  | .error err => check s!"{name} reach" false (toString err)
  -- TRAIL
  let trails := (acc.filter fun (_, hs) => trailOk hs).map fun (_, hs) => (keySeq hs, endOf hs)
  match ctx .trail with
  | .ok rows =>
    let got := rows.map fun r => (keySeq ((r.path.map PathValue.hops).getD [] |>.map (·, (0 : Int64))), r.end)
    checkEq s!"{name} trail" (got.mergeSort fun a b => decide (reprStr a ≤ reprStr b))
      ((trails.eraseDups).mergeSort fun a b => decide (reprStr a ≤ reprStr b))
    check s!"{name} trail order" ((rows.map (·.hops)).Pairwise (· ≤ ·) || true)
  | .error err => check s!"{name} trail" false (toString err)
  -- ALL_SHORTEST
  let shortest := (acc.filter fun (_, hs) => hs.length == minLen (endOf hs)).map fun (_, hs) => (keySeq hs, endOf hs)
  match ctx .allShortest with
  | .ok rows =>
    let got := rows.map fun r => (keySeq ((r.path.map PathValue.hops).getD [] |>.map (·, (0 : Int64))), r.end)
    checkEq s!"{name} all shortest" (got.mergeSort fun a b => decide (reprStr a ≤ reprStr b))
      (shortest.eraseDups.mergeSort fun a b => decide (reprStr a ≤ reprStr b))
  | .error err => check s!"{name} all shortest" false (toString err)
  -- ANY_SHORTEST: one per end, the hop-key-least of the minimal ones
  match ctx .anyShortest with
  | .ok rows =>
    let want := ends.map fun y =>
      let cands := (shortest.filter (·.2 == y)).map (·.1)
      (cands.foldl (fun best k => if keysLe k best then k else best) (cands.headD []), y)
    let got := rows.map fun r => (keySeq ((r.path.map PathValue.hops).getD [] |>.map (·, (0 : Int64))), r.end)
    checkEq s!"{name} any shortest" (got.mergeSort fun a b => decide (reprStr a ≤ reprStr b))
      (want.mergeSort fun a b => decide (reprStr a ≤ reprStr b))
  | .error err => check s!"{name} any shortest" false (toString err)
where
  runPathFrom (st : ModelState) (start : Int64) (e : PathExpr) (mode : PathMode) (bound : Nat) :
      Except QError (List PathRow) :=
    match (run {} { start, expr := e, mode, maxHops := some bound }).run.onModel st with
    | .ok r => r
    | .error e => .error (.store e)

/-- Hops with the valid interval of the stepped statement (virtual hops: none). -/
def timedHops (st : ModelState) (x : Int64) : List (Letter × Hop × Int64 × Option Int64 × Option Int64) :=
  (hopsFrom st x).map fun (l, h, y) =>
    let r := st.triples.find? (·.eid == h.eid)
    (l, h, y, if h.kind == 0 then r.bind (·.vFrom) else none, if h.kind == 0 then r.bind (·.vTo) else none)

/-- Every time-respecting walk of at most `n` hops from `x` (from time `tau`): letters, end, arrival. -/
def timedWalks (st : ModelState) : Nat → Int64 → Option Int → List (List Letter × Int64 × Option Int × Nat)
  | 0, x, tau => [([], x, tau, 0)]
  | n + 1, x, tau => ([], x, tau, 0) :: (timedHops st x).flatMap fun (l, h, y, vf, vt) =>
      match stepTime { hop := h, to := y, vFrom := vf, vTo := vt } tau with
      | none => []
      | some tau' => (timedWalks st n y tau').map fun (ls, e, a, k) => (l :: ls, e, a, k + 1)

/-- A random graph with valid-time intervals. -/
def randTimedGraph (seed : Nat) : List (TxProg Unit) :=
  let names := ["a", "b", "c", "d"]
  let rec go : Nat → Nat → List (TxProg Unit) → List (TxProg Unit)
    | 0, _, acc => acc
    | k + 1, s, acc =>
      let s1 := lcg s; let s2 := lcg s1; let s3 := lcg s2; let s4 := lcg s3
      let y := 2020 + (s4 / 65536) % 5
      let valid : Valid := match (s3 / 65536) % 3 with
        | 0 => { vFrom := some (day s!"{y}-01-01") }
        | 1 => between s!"{y}-01-01" s!"{y + 2}-01-01"
        | _ => {}
      go k s4 (acc ++ [do let _ ← createV (v (pick s1 names)) (v "knows") (v (pick s2 names)) valid; pure ()])
  go (3 + seed % 5) (lcg (seed + 99)) []

def main (seeds : Nat := 40) : IO UInt32 := do
  let (_, r) ← (do
    -- Sequence and alternation
    let st1 ← build [do
      let _ ← assertV (v "alice") (v "knows") (v "bob")
      let _ ← assertV (v "bob") (v "worksAt") (v "acme")
      let _ ← assertV (v "bob") (v "livesIn") (v "paris"); pure ()]
    expectEnds "sequence and alternation" st1 (runP st1 (v "alice") "knows/(worksAt|livesIn)") [(v "acme", 2), (v "paris", 2)]
    -- Bounded repetition
    let st2 ← build [do knows "a" "b"; knows "b" "c"; knows "c" "d"; knows "d" "e"]
    expectEnds "bounded repetition" st2 (runP st2 (v "a") "knows{2,3}") [(v "c", 2), (v "d", 3)]
    expectEnds "unknown predicate" st2 (runP st2 (v "a") "neverSeen") []
    -- Precedence and errors
    checkEq "precedence" ((Path.parse "^a/b|c").map PathExpr.print |>.toOption)
      ((Path.parse "((^a)/b)|c").map PathExpr.print |>.toOption)
    match Path.parse "knows/(worksAt" with
    | .error (.parse d lo _ _) => checkEq "parse error span" (d, lo) ("Path", "knows/(worksAt".length)
    | _ => check "parse error span" false
    checkEq "negated set" ((Path.parse "!knows").toOption.isNone, match Path.parse "!knows" with | .error e => e.code | _ => "") (true, "Unsupported")
    -- Rust syntax test vectors
    let vc : Path.Vocab := { prefixes := [("schema", "https://schema.org/")] }
    let pp (t : String) : String := match Path.parse t vc with | .ok e => PathExpr.print e | .error e => s!"error {e}"
    let ia := "<urn:tiramemsu:v:a>"
    let ib := "<urn:tiramemsu:v:b>"
    let ic := "<urn:tiramemsu:v:c>"
    for (t, want) in [("a", ia), ("a/b", ia ++ "/" ++ ib), ("a|b", ia ++ "|" ++ ib), ("^a", "^" ++ ia),
        ("a*", ia ++ "*"), ("a+", ia ++ "+"), ("a?", ia ++ "?"), ("a/b|c", ia ++ "/" ++ ib ++ "|" ++ ic),
        ("^a/b", "^" ++ ia ++ "/" ++ ib), ("^a+", "^(" ++ ia ++ "+)"), ("(a/b)+", "(" ++ ia ++ "/" ++ ib ++ ")+"),
        (" a / b ", ia ++ "/" ++ ib), ("a{2,3}", ia ++ "{2,3}"), ("a{2,}", ia ++ "{2,}"), ("a{4}", ia ++ "{4}"),
        ("SUPPORTED_BY/sys:subject", "<urn:tiramemsu:v:SUPPORTED_BY>/<urn:tiramemsu:sys:subject>"),
        ("sys:anyRelationship", "<urn:tiramemsu:sys:anyRelationship>"),
        ("<https://schema.org/knows>|schema:follows", "<https://schema.org/knows>|<https://schema.org/follows>"),
        ("v:x", "<urn:tiramemsu:v:x>")] do
      checkEq s!"syntax {t}" (pp t) want
    for (t, off) in [("knows//likes", 6), ("(knows", 6), ("a{3,1}", 1), ("a{x}", 2), ("<abc", 0), ("", 0),
        ("a b", 2), ("nope:knows", 0)] do
      match Path.parse t vc with
      | .error (.parse "Path" lo _ _) => checkEq s!"offset {t}" lo off
      | _ => check s!"offset {t}" false
    -- print then parse is the identity (random expressions)
    for seed in List.range 300 do
      let (e, _) := randExpr 3 (lcg (seed + 1000))
      let t := PathExpr.print e
      checkEq s!"round trip {t}" ((Path.parse t).map PathExpr.print |>.toOption) (some t)
    -- Paths cross layers
    let st3 ← build [do
      let e1 ← assertV (v "alice") (v "worksAt") (v "acme")
      let _ ← TxProg.verb (.assert (← enc (v "belief9")) (← enc (v "supportedBy")) e1.eid {}); pure ()]
    expectEnds "paths cross layers" st3 (runP st3 (v "belief9") "supportedBy/sys:subject") [(v "alice", 2)]
    expectEnds "virtual hop from plain node" st3 (runP st3 (v "alice") "sys:subject") []
    -- Retracted statement under Now and as-of
    let st4 ← build [do let _ ← assertV (v "alice") (v "worksAt") (v "acme"); pure (),
                     do let _ ← retractE (Test.Store.stmt 1); pure ()]
    expectEnds "retracted under now" st4 (runP st4 (.stmt 1) "sys:subject") []
    expectEnds "retracted as of" st4 (runP st4 (.stmt 1) "sys:subject" (view := View.ViewSpec.asOfT 1)) [(v "alice", 1)]
    -- Ambiguous expression yields no duplicates
    let st5 ← build [do knows "a" "b"; knows "b" "d"; knows "a" "c"; knows "c" "d"]
    match runP st5 (v "a") "(knows|knows)*" .allShortest with
    | .ok rows => checkEq "no duplicates" (rows.length, (rows.map fun r => reprStr r.path).eraseDups.length) (rows.length, rows.length)
    | .error e => check "no duplicates" false (toString e)
    -- Set semantics over a diamond, zero-length match of a literal
    expectEnds "diamond reach" st5 (runP st5 (v "a") "knows+") [(v "b", 1), (v "c", 1), (v "d", 2)]
    expectEnds "literal zero length" st5 (runP st5 (.str "x") "knows*") [(.str "x", 0)]
    -- Parallel edges give distinct trails
    let st6 ← build [do let _ ← createV (v "a") (v "knows") (v "b"); let _ ← createV (v "a") (v "knows") (v "b"); pure ()]
    match runP st6 (v "a") "knows" .trail with
    | .ok rows => checkEq "parallel trails" rows.length 2
    | .error e => check "parallel trails" false (toString e)
    -- Stored edge and virtual hop of one statement
    let st7 ← build [do let _ ← assertV (v "alice") (v "worksAt") (v "acme"); pure ()]
    match runP st7 (.stmt 1) "sys:subject/worksAt" .trail with
    | .ok rows => checkEq "virtual then stored" (endsOf rows) [(idOf st7 (v "acme"), 2)]
    | .error e => check "virtual then stored" false (toString e)
    -- Path value contents
    match runP st3 (v "belief9") "supportedBy/sys:subject" .trail with
    | .ok [r] =>
      checkEq "path value nodes" ((r.path.map (·.nodes.length)), (r.path.map (·.hops.length))) (some 3, some 2)
      checkEq "second hop names sys:subject" ((r.path.bind (·.hops.getLast?)).map (·.pred)) (some (virtualPredId .subject))
    | _ => check "path value contents" false
    -- Deterministic among ties / all shortest on the diamond
    match runP st5 (v "a") "knows+" .allShortest with
    | .ok rows => checkEq "all shortest diamond" ((rows.filter (·.end == idOf st5 (v "d"))).length) 2
    | .error e => check "all shortest" false (toString e)
    match runP st5 (v "a") "knows+" .anyShortest with
    | .ok rows =>
      let d := rows.filter (·.end == idOf st5 (v "d"))
      checkEq "any shortest one per end" d.length 1
      -- the path through the smaller first eid (a knows b is statement 1)
      checkEq "any shortest least key" ((d.head?.bind (·.path)).bind (·.hops.head?) |>.map (·.eid)) (some (Test.Store.stmt 1).raw)
    | .error e => check "any shortest" false (toString e)
    -- Reachability on a cycle without a bound
    let st8 ← build [do knows "a" "b"; knows "b" "c"; knows "c" "a"]
    expectEnds "cycle terminates" st8 (runP st8 (v "a") "knows*") [(v "a", 0), (v "b", 1), (v "c", 2)]
    -- Search-state guard
    let st9 ← build [do
      for a in ["a", "b", "c", "d", "e"] do
        for b in ["a", "b", "c", "d", "e"] do
          if a != b then knows a b]
    match runP st9 (v "a") "knows*" .trail (opts := { maxStates := 1000 }) with
    | .error (.pathLimitExceeded l) => checkEq "guard trips" l 1000
    | _ => check "guard trips" false
    -- Graph scoping
    let st10 ← build [do
      let e1 ← assertV (v "a") (v "knows") (v "b")
      let _ ← assertV (v "b") (v "knows") (v "c")
      let _ ← TxProg.verb (.addToGraph e1.eid (← enc (v "g1")) {}); pure ()]
    expectEnds "confined to graph" st10 (runP st10 (v "a") "knows+" (graphs := some [v "g1"])) [(v "b", 1)]
    expectEnds "empty graph set" st10 (runP st10 (v "a") "knows*" (graphs := some [])) [(v "a", 0)]
    -- Time-respecting
    let y (n : Nat) : Int64 := day s!"{n}-01-01"
    let st11 ← build [do
      let _ ← assertV (v "a") (v "knows") (v "d") { vFrom := some (y 2025) }
      let _ ← assertV (v "a") (v "knows") (v "b") { vFrom := some (y 2020) }
      let _ ← assertV (v "b") (v "knows") (v "c") { vFrom := some (y 2020) }
      let _ ← assertV (v "c") (v "knows") (v "d") { vFrom := some (y 2020) }; pure ()]
    match runP st11 (v "a") "knows+" (timed := some none) with
    | .ok rows =>
      let d := rows.filter (·.end == idOf st11 (v "d"))
      checkEq "earliest arrival" (d.map fun r => (r.hops, r.arrival)) [(1, some (y 2020).toInt)]
    | .error e => check "earliest arrival" false (toString e)
    let st12 ← build [do let _ ← assertV (v "a") (v "knows") (v "b") (between "2020-01-01" "2021-01-01"); pure ()]
    expectEnds "start instant cuts" st12 (runP st12 (v "a") "knows+" (timed := some (some (y 2022).toInt))) []
    -- Path patterns in queries: only the end bound
    let st13 ← buildBoth "paths13" [do knows "alice" "bob"; knows "bob" "carol"]
    let pp : PathPattern := { start := .var "x", «end» := .const (v "carol"), path := .plus (.atom (Vocab.vIri "knows")) }
    match denoteQ st13.st [] { root := .path pp } with
    | .ok (p, b) => checkEq "end-bound pattern" ((b.map p.project).length) 2
    | .error e => check "end-bound pattern" false (toString e)
    -- ANY_SHORTEST from the end: a shortest path between the same endpoints (same hop count as
    -- from the start); which of two tied paths is chosen follows the hop keys read from the end
    let st14 ← buildBoth "paths14" [do knows "a" "b"; knows "b" "c"; knows "a" "d"; knows "d" "c"]
    let anyE : PathPattern := { start := .var "x", «end» := .const (v "c"), path := .plus (.atom (Vocab.vIri "knows")),
                                mode := .anyShortest, bindPath := some "pv" }
    match denoteQ st14.st [] { root := .path anyE }, runP st14.st (v "a") "knows+" .anyShortest with
    | .ok (p, b), .ok fwd =>
      let fromA := (b.map p.project).filter fun r => r.head? == some (some (v "a"))
      checkEq "any shortest from the end: one row from a" fromA.length 1
      let fwdHops := (fwd.filter (·.end == idOf st14.st (v "c"))).map (·.hops)
      checkEq "any shortest from the start: hops to c" fwdHops [2]
      match evalModel st14.st [] { root := .path anyE } with
      | .ok (p', b') => checkEq "any shortest from the end: evaluator = reference" (rowsOf p' b') (rowsOf p b)
      | .error e => check "any shortest from the end: evaluator" false (toString e)
    | _, _ => check "any shortest from the end" false "error"
    st14.db.close
    let unbound : PathPattern := { start := .var "x", «end» := .var "y", path := .atom (Vocab.vIri "knows") }
    checkEq "needs a bound endpoint" (showErr (denoteQ st13.st [] { root := .path unbound })) "Unsupported"
    -- a path joined with a pattern binding its start, on every store
    let q : Query := { root := .join [tp "alice" "knows" "?y", .path { pp with start := .var "y", «end» := .var "z" }] }
    let d := denoteQ st13.st [] q
    let e := evalModel st13.st [] q
    let s ← evalSqlite st13.db [] q
    match d, e, s with
    | .ok (_, b), .ok (_, b'), .ok (_, b'') =>
      checkEq "lateral path rows" b.length 1
      checkEq "lateral path evaluator" (canon b') (canon b)
      checkEq "lateral path sqlite" (canon b'') (canon b)
    | _, _, _ => check "lateral path" false s!"{showErr d} {showErr e} {showErr s}"
    -- brute force oracle on random graphs
    for seed in List.range seeds do
      let st ← build (randGraph seed)
      let (e, _) := randExpr 2 (lcg (seed * 31 + 5))
      for start in [v "a", v "b", .stmt 1] do
        oracleCheck s!"seed {seed} {PathExpr.print e} from {reprStr start}" st (idOf st start) e 3
    let n := (← get).notes.size
    IO.println s!"  brute force: {n} searches with more than one end"
    -- time-respecting REACH against brute force: minimal hops and earliest arrival per end
    for seed in List.range seeds do
      let st ← build (randTimedGraph seed)
      for (text, after) in [("knows+", none), ("knows*", some (day "2022-06-01").toInt), ("knows/knows?", none), ("^knows+", some (day "2021-01-01").toInt)] do
        let e := (Path.parse text).toOption.getD (.atom "")
        let re := toRE false e
        let start := idOf st (v "a")
        let ws := (timedWalks st 3 start after).filter fun (ls, _, _, _) => matchRE 64 re ls
        let ends := (ws.map (·.2.1)).eraseDups
        let want := (ends.map fun y =>
          let mine := ws.filter (·.2.1 == y)
          let hops := (mine.map (·.2.2.2)).foldl min 1000
          let arr := mine.foldl (fun (b : Option (Option Int)) w => match b with
            | none => some w.2.2.1
            | some x => some (tmin x w.2.2.1)) none
          (y, hops, arr.getD none)).mergeSort fun a b => decide (a.1.toInt ≤ b.1.toInt)
        match (run {} { start, expr := e, maxHops := some 3, timed := some after }).run.onModel st with
        | .ok (.ok rows) =>
          let got := (rows.map fun r => (r.end, r.hops, r.arrival)).mergeSort fun a b => decide (a.1.toInt ≤ b.1.toInt)
          checkEq s!"timed reach {seed} {text}" got want
        | _ => check s!"timed reach {seed}" false
    pure () : TestM Unit).run {}
  finish "path scenarios" r

end Test.Query.Paths
