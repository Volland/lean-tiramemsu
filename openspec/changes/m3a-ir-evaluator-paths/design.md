## Context

See proposal.md for motivation. M3a starts from:

- M0: the `Store` interface (ordered range scans over `spo`, `pos`, `osp` in the live and history families, eid lookup, appends, the retraction update, counters, savepoints), `ModelStore` (pure lists) and `SqliteStore` (leansqlite), the CI proof gates, the theorem index and the Rust oracle harness.
- M1: `ObjectId` with origin bits, the canonical literal codec and term dictionary (encode is injective on canonical values; decode ∘ encode = id), the Rust-compatible value sort key.
- M2: view selectors and visibility (`visible st v e`), `asOf` = log replay, `dependents` = cascade closure, the verbs inside IO-free `TxM` programs, graph membership verbs, the `Db` shell with a View pinned to one snapshot for its scope.

Constraints: verified modules are total, no `partial`, search loops take explicit fuel with a theorem that the bound suffices (verification#Proof Policy); runtime imports only core + Std; proofs live in `TiramemsuProofs` (D7). SQLite only serves range scans (D3). Results must match the pinned Rust build (D6).

## Goals / Non-Goals

**Goals:**

- One evaluator, generic over `Store`, whose run on `ModelStore` is proven equal to the reference semantics and whose run on `SqliteStore` is refinement-tested against `ModelStore`.
- Join-order independence proven once, as a statement about any operator that consumes the sorted-iterator interface, so the M3b planner needs no proof (D13).
- Path results proven equal to a specification written without automata or search.
- A reference semantics that is itself computable, so it doubles as the test oracle.

**Non-Goals:**

- Leapfrog Triejoin, cyclic-pattern detection and the cost-based planner (M3b). M3a ships a simple greedy order.
- SPARQL and Cypher parsing and lowering (M4, M5). Cypher-only operators (`Unnest`, `RowNumber`, `Lookup`, null-safe keys, volatile pattern opt-in) are added to `query-ir` by M5.
- Proving anything about hardware `Float`, SQLite, the CLI or the JSON form of bundles (trusted base / tested).

## Decisions

### Module layout

```text
Tiramemsu/IR/        Var, TermOrVar, GraphSel, Expr+Op (mutual), Agg, Key, PathExpr, PathMode,
                     Semantics, Params, Scope (certain/possible vars), Validate
Tiramemsu/Sem/       Row, Bag ops, Compat, SortKey order, ExprEval (3-valued), Virtual preds,
                     Denote (reference semantics, computable)
Tiramemsu/Exec/      Scan (index choice, key prefix), Inlj, Pushdown, Order (greedy), Eval, Explain
Tiramemsu/Path/      Syntax (text parser/printer), Letter, Nfa, Dfa, Hop, Fuel,
                     Search/{Reach,Trail,Shortest,Timed}, Engine
Tiramemsu/Prov/      Annot, EvalProv
Tiramemsu/Bundle/    Value, Export, Import, Json
Tiramemsu/Api/       Options, Errors, Db, View, Tx, Explain rendering
Tiramemsu/Cli/Main   `tiramemsu` executable
TiramemsuProofs/Query/{Bag,JoinLaws,Validate,Scan,Inlj,Pushdown,EvalDenote,Stable}
TiramemsuProofs/Path/{Lang,Nfa,Dfa,Spec,Reach,Trail,Shortest,Fuel,Inverse,Graph,Timed}
TiramemsuProofs/Prov/{Erase,Sound,Suffice}
TiramemsuProofs/Bundle/{Export,RoundTrip,Reimport}
```

### Key types

```lean
inductive TermOrVar | var (v : Var) | const (v : Value) | id (o : ObjectId) | param (n : String)
inductive GraphSel  | any | set (gs : List TermOrVar) | var (g : Var)
structure TriplePattern where
  s p o : TermOrVar; eid : Option Var; view : ViewSpec; isoGroup : Option Nat; graph : GraphSel
structure PathPattern where
  start «end» : TermOrVar; path : PathExpr; mode : PathMode; maxHops : Option Nat
  bindPath : Option Var; view : ViewSpec; graph : GraphSel   -- time-respecting search is API-only, as in Rust
mutual
inductive Expr | var | const | param | cmp | sameTerm | and | or | not | bound | inList
               | arith | neg | coalesce | ite | func (f : Func) (args : List Expr)
               | exists (q : Op) (negated : Bool)
inductive Op   | triple (t : TriplePattern) | path (p : PathPattern) | values (vs : List Var) (rows : List (List (Option TermOrVar)))
               | join (xs : List Op) | leftJoin (l r : Op) (c : Option Expr) | union (xs : List Op)
               | filter (c : Expr) (x : Op) | extend (v : Var) (e : Expr) (x : Op)
               | aggregate (g : List Var) (aggs : List Agg) (x : Op)
               | project (vs : List Var) (distinct : Bool) (x : Op)
               | orderLimit (keys : List Key) (skip limit : Option TermOrVar) (x : Op)
end
structure Semantics where matchMode : MatchMode; missing : Missing; graphSet : GraphSet
structure Row where entries : List (Var × Value); sorted : entries.Pairwise (·.1 < ·.1)
abbrev Bag α := List α          -- equality up to `List.Perm`; proofs go through `Multiset`
inductive Tri | t | f | err      -- filter truth value; Unbound errors and Null3VL nulls both map to `err`
```

The reference semantics `denote (σ : Semantics) (st : StoreState) (ps : Params) : Op → Except QError (Bag Row)` is structural recursion over `Op` (expressions recurse into `exists`). Rows hold decoded `Value`s; the evaluator works on `ObjectId`s plus computed values (`XCell := id ObjectId | val Value`) and the bridge theorem uses M1's encode/decode bijection. A `PathPattern` denotes the rows of the path engine; a separate theorem ties the engine to the declarative path specification, so `denote` stays computable.

Alternative rejected: rows as functions `Var → Option Value` (not computable, no oracle); a relational semantics `Op → Row → Prop` only (no oracle, and evaluator proofs would need a separate decidability layer).

### Bag semantics and canonical order

All operators are bag operators, and every theorem is "equal up to permutation" except at an `OrderLimit`, whose output is a list. To make `OrderLimit`, `SAMPLE`, `GROUP_CONCAT` and double `SUM`/`AVG` functions of the multiset (needed for order independence), ties and folds use a canonical row order: the sort key of each cell in variable order, missing first. Rust leaves these orders unspecified, so this is a refinement except for floating-point folds, which are a listed deviation. Alternative rejected: input-order folds (would make join order observable and break D13).

### Index nested-loop join (D13, M3a half)

`Join` of patterns runs as an index nested loop: patterns in a chosen order π; each pattern's positions bound by constants or by earlier patterns form a key prefix; the index order is the one of `spo`, `pos`, `osp` whose prefix covers the bound set (every subset of `{s,p,o}` is a prefix of one rotation), live family under `Now`, history family otherwise, eid lookup when the eid is bound. `SetOfTriples` deduplication is adjacent-duplicate removal in scan order (equal `(s,p,o)` are adjacent in every rotation). Non-pattern join inputs are evaluated with the reference operator and joined by hash on shared certain variables. The M3a order π is greedy (most bound positions, then smallest per-predicate count); M3b replaces it.

The sorted-iterator interface that both INLJ and LFTJ consume:

```lean
class SortedRange (S : Type) where
  scan  : S → IndexOrder → ViewSpec → (pfx : List ObjectId) → Array Triple   -- ascending key order
  seek  : S → IndexOrder → ViewSpec → (pfx : List ObjectId) → (lo : ObjectId) → Option ObjectId  -- least next key ≥ lo
```

Contract (proven for `ModelStore`, trusted for SQLite per verification#Trusted Base): `scan` returns exactly the visible triples matching the prefix, sorted by the order's key, eid last; `seek` returns the least next-column key ≥ `lo` among those triples.

Alternative rejected: proving each planner order correct (planner proof burden every change); hash joins everywhere (loses index seeks, worse than Rust on point lookups).

### Path engine

Letters are `(class, direction)` over a refined alphabet (one stored predicate, "other relationship-view predicate" for the wildcard, `sys:subject`, `sys:object`, `sys:predicate`). `^` is pushed to atoms (reversing sequences), `{m,n}` is unrolled, Thompson NFA (cap 200 000 states) then subset construction (cap 4 096 states, else `Unsupported("path expression too complex")`). Search is BFS over `(node, dfaState)` layers with explicit fuel:

| Mode | Fuel (layers) | Why it suffices |
|---|---|---|
| REACH, ANY/ALL_SHORTEST | `min(maxHops, N·Q)` | a shortest accepting walk never repeats a `(node, state)` pair |
| TRAIL | `min(maxHops, I)` | a trail never repeats one of `I` relationship identities |
| time-respecting REACH | rounds `≤ N·Q·(card T + 1)` | each pair's best time strictly decreases within the finite set `T` |

`N` = start plus distinct nodes of visible statements, `Q` = DFA states, `I` = visible stored eids + 3 × visible statements, `T` = `{after} ∪ {v_from of visible statements}`. The `path_max_states` guard is separate and only ever fails, never truncates.

Alternative rejected: `partial def` BFS (forbidden in verified modules); recursive-CTE-style fixpoint (no path values, slower).

### Provenance

`evalProv` is the evaluator with each row paired with a sorted eid set. Citation rules are in `query-provenance`. Sufficiency is stated against a witness semantics `denoteW q st P` that restricts citing leaves to statements in `P` while non-citing leaves and negative tests (LeftJoin non-match, EXISTS, multi-graph membership tests, REACH paths, virtual predicates) and whole-bag operators (Aggregate input, OrderLimit input) read the full view. Alternative rejected: "re-run on the sub-store of cited statements", which is false for OPTIONAL, NOT EXISTS and aggregates.

### Bundles

Export walks `dependents` (M2) then the downward closure, applies exclusions to a fixed point, orders by references (topological, ties by source eid, cycle members last in eid order) and labels anonymous nodes by first appearance. Import is a `TxM` program: check structure and cycles first, then `assert`/`addToGraph` in order. Both are pure functions on `ModelStore` states, so the round trip is a theorem about M2's verbs.

### Theorem statements (Tier 2)

Each is indexed against the requirement whose "Machine-checked" scenario it discharges. `st` is a `ModelStore` state, `V` a view, `σ` semantic flags, `ps` complete parameters, `~` is `List.Perm`.

| Requirement | Statement (informal) | Lean-ish signature |
|---|---|---|
| query-ir: Structural validation | A validated query never fails with `InvalidQuery` at evaluation | `validate q = .ok () → complete ps q → ∀ st, denote σ st ps q ≠ .error (.invalidQuery _)` |
| query-semantics: Relational operators | n-ary Join is invariant under input permutation, associative, `[]` unit | `xs ~ ys → denote (.join xs) ≈ denote (.join ys)`; `denote (.join [a, .join [b,c]]) ≈ denote (.join [.join [a,b], c])`; `denote (.join [a, .join []]) ≈ denote a` |
| query-semantics: Reference semantics | For every plan the evaluator over `ModelStore` equals `denote` | `validate q = .ok () → ∀ plan, eval (ModelStore.mk st) plan σ ps q ≈ denote σ st ps q` (exact list equality when the root is `OrderLimit`) |
| query-semantics: Stable historical results | Commits after `t` do not change results under `asOf t` | `st ≤ st' → t ≤ st.lastT → denote σ st ps (q.at (asOf t)) = denote σ st' ps (q.at (asOf t))` |
| query-semantics: Aggregation | Aggregates are functions of the multiset of the group | `xs ~ ys → aggregate g aggs xs ≈ aggregate g aggs ys` |
| nested-loop-join: Sorted range-scan interface | `ModelStore` scans return exactly the visible matching triples, sorted | `(scan st ord V pfx).toList = ((visibleTriples st V).filter (pfxMatch ord pfx)).mergeSort (keyLe ord)` |
| nested-loop-join: Join-order independence | INLJ equals the reference natural join for every order | `∀ π : ps.Perm ps', inlj st σ ps' ≈ denote σ st ps (.join (ps.map .triple))` |
| nested-loop-join: Filter push-down and binding passing | Rewrites preserve the denotation | `denote (pushdown q) ≈ denote q`; `certainVars r ⊇ dom b → joinSideways l r ≈ denote (.join [l, r])` |
| nested-loop-join: Index choice | Adjacent dedup = one row per distinct visible `(s,p,o)` | `(dedupAdj (scan …)).map spo = ((visibleTriples …).map spo).dedup` (as sets, `Nodup`) |
| path-evaluation: Automaton compilation | DFA language = expression language, unique run | `compile e = .ok d → (d.accepts w ↔ w ∈ lang e)`; `d.run w` is a function (determinism) |
| path-evaluation: Reachability mode | REACH rows = ends of accepting walks within the bound, hops minimal | `(y,h) ∈ reach st V e x b ↔ (∃ w : Walk st V x y, w.word ∈ lang e ∧ w.len ≤ b) ∧ h = minLen …`; `Nodup (ends)` |
| path-evaluation: Trail mode | TRAIL rows = accepting trails within the bound, each once | `p ∈ trail … ↔ p.IsTrail ∧ p.word ∈ lang e ∧ p.len ≤ b`; `Nodup` |
| path-evaluation: Shortest modes | ANY: one minimal, hop-key-least per end; ALL: every minimal path once | `anyShortest … = ends.map (fun y => lexMin (minimalPaths y))`; `allShortest … ~ (ends.bind minimalPaths)` with `Nodup` |
| path-evaluation: Termination and search bound | The fuel bound is never exhausted | `fuel ≥ bound mode st V d → search fuel = search (fuel+k)` for all `k` |
| path-evaluation: Endpoint binding | From-end evaluation with the inverse expression gives the same rows | `fromEnd st V e y = (fromStart st V e.inverse y).map Row.reverse`; `lang e.inverse = (lang e).map reverseFlip` |
| path-evaluation: Graph-scoped evaluation | Every hop's statement has a visible membership in G; zero-hop rows independent of G | `p ∈ rows (G) ↔ p ∈ rows (none) ∧ ∀ h ∈ p.hops, ∃ g ∈ G, member st V h.stmt g` (hops > 0) |
| path-evaluation: Time-respecting evaluation | Hop rule monotone; REACH arrival earliest; later start reaches no more and arrives no earlier | `τ ≤ τ' → allowed τ' h → allowed τ h ∧ step τ h ≤ step τ' h`; `arrival y = sInf (arrivals of timed walks to y with len ≤ b)`; `a ≤ a' → ends a' ⊆ ends a ∧ arr a ≤ arr a'` |
| query-provenance: Provenance on request | Erasing annotations gives the plain result | `(evalProv σ st ps q).map (·.1) ≈ denote σ st ps q` |
| query-provenance: Provenance soundness | Every cited eid is visible in its leaf's view and matches the leaf under the row's derivation | `(r,E) ∈ evalProv … → e ∈ E → ∃ ℓ ∈ citingLeaves q, visible st ℓ.view e ∧ supports ℓ r e` |
| query-provenance: Provenance sufficiency | The cited set re-derives the row in the witness semantics | `(r,E) ∈ evalProv … → r ∈ denoteW σ st ps q E` |
| fact-bundles: Import is idempotent assert | Import into a fresh store, then export, gives an isomorphic bundle | `exportable st V root → b = export st V root → import fresh b = .ok (st₁, rep) → ∃ ρ, Bundle.Iso (collapse b) (export st₁ now rep.root) ρ` |
| fact-bundles: Re-import changes nothing | Without anonymous labels, a second import writes nothing | `b.labels = [] → import st b = .ok (st₁, _) → import st₁ b = .ok (st₂, rep) → live st₂ = live st₁ ∧ ∀ x ∈ rep, ¬ x.new` |

### Test strategy for unproven parts

- **SqliteStore refinement:** random stores and random IR trees (generator respects validation) run on `ModelStore` and `SqliteStore`; results compared as bags. Same for `View.path`, `dependents`, `bundle`.
- **Rust oracle:** the M0 oracle harness builds each IR test case with the Rust `tm-ir` builder from a shared case file and runs it on the same `.db`; results compared canonically. Paths compared through `View::path_with`; bundles through their JSON text, byte for byte.
- **Path text syntax:** parser tested by print∘parse round trip, the Rust `syntax.rs` test vectors, and error spans compared with Rust.
- **Sort key:** byte equality with Rust `sort_key` on generated values.
- **Float:** double arithmetic cases compared bit-exactly with Rust where the fold order is irrelevant, within `n` ulps otherwise.
- **Search guard, explain, CLI, bundle JSON:** golden tests; JSON round trip `fromJson ∘ toJson = id` as a property test.
- **Recipes:** the Rust `lat.md/recipes.md` queries that do not need SPARQL/Cypher syntax (impact analysis via `dependents` = `(^sys:subject|^sys:object)*`, evidence chains through time, edit lineage, journeys, portable facts) as end-to-end tests.

## Risks / Trade-offs

- [Path proofs are the largest proof effort of v1] → Spec first (`Walk`, `lang`), then automaton, then one mode at a time; REACH and fuel before TRAIL/shortest; time-respecting last. The engine ships with differential tests from day one so proofs never block functionality review.
- [Canonical folds cost a sort per group] → Only for `SAMPLE`, `GROUP_CONCAT` and double sums; integer folds are order-free. Benchmarks are report-only (D14).
- [Double `SUM`/`AVG` can differ from Rust in rounding] → Listed deviation; oracle compares with tolerance on such cases.
- [Greedy join order is weak on skewed or cyclic patterns until M3b] → Report-only benchmarks; the order never affects results (proven).
- [`denote` on paths uses the engine, so a bug in the spec-to-engine theorem statement would be invisible to the oracle] → The path theorems are stated against `Walk`/`lang`, which are independent of the engine; a brute-force walk enumerator over small graphs is also a test oracle.
- [Witness-semantics sufficiency is weaker than "re-run on cited statements"] → Stated explicitly in the spec; it is the strongest property that holds with OPTIONAL, NOT EXISTS and aggregates.
- [Bundle round trip depends on M2's assert semantics (collapse of equal content)] → The theorem is stated modulo `collapse`; exact equality is a corollary for bundles without equal-content duplicates.
