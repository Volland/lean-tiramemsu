## 1. IR types and validation

- [x] 1.1 Add `Tiramemsu/IR/` types: `Var`, `TermOrVar`, `GraphSel`, mutual `Expr`/`Op`, `Agg`, `Key`, `PathExpr`, `PathMode` (case-insensitive parse, `Unsupported` for other names), `Semantics` with SPARQL and Cypher presets, `Params`
- [x] 1.2 Add `IR/Scope`: certain and possible variables per operator, and result column order (root `Project`, else first binding)
- [x] 1.3 Add `IR/Validate` with every `InvalidQuery` rule of `query-ir` "Structural validation"; unit tests per rule
- [x] 1.4 Add parameter resolution (`InvalidQuery` naming a missing parameter) and constant resolution that only looks up the dictionary (unknown constant → empty pattern position, value kept in expressions)
- [x] 1.5 Prove validation soundness (validated query + complete parameters never raises `InvalidQuery`) in `TiramemsuProofs/Query/Validate`; add the theorem-index entry

## 2. Reference semantics

- [x] 2.1 Add `Sem/Row` (sorted entries), `Sem/Bag` operations and compatibility under `Unbound` and `Null3VL`
- [x] 2.2 Add `Sem/SortKey` byte-identical to the Rust sort key; property test against the oracle on generated values
- [x] 2.3 Add `Sem/ExprEval`: three-valued logic, comparisons, exact integer/decimal arithmetic, hardware `Float` for doubles, the SPARQL scalar functions, `EXISTS`
- [x] 2.4 Add virtual-predicate triples (`sys:subject|object|predicate`, `tm:txAdded|txRetracted|addedAt|retractedAt|validFrom|validTo|retractKind`) computed from statement rows
- [x] 2.5 Add `Sem/Denote`: total, computable `denote` for every operator, graph selectors, `SetOfTriples`/`BagOfEids`, isomorphism groups, aggregation with canonical folds, `OrderLimit` with canonical tie-break; path patterns call the path engine (stub returning `Unsupported` until 9.1)
- [x] 2.6 Prove join algebra (permutation invariance, associativity, unit) in `TiramemsuProofs/Query/JoinLaws` via `Multiset`
- [x] 2.7 Prove aggregates are functions of the group multiset
- [x] 2.8 Prove stability of `AsOf(t)` results under later commits, from M2's asOf = log-replay theorem
- [x] 2.9 Scenario tests for every `query-ir` and `query-semantics` scenario on `ModelStore`

## 3. Sorted range scans and index choice

- [x] 3.1 Add the `SortedRange` interface (scan, seek, eid lookup) over the M0 `Store`, with `ModelStore` and `SqliteStore` instances (prepared range statements on covering indexes)
- [x] 3.2 Prove the `ModelStore` scan and seek contract (exact visible matches, sorted, least next key)
- [x] 3.3 Add `Exec/Scan`: index order from bound positions, live/history family, valid-time filter, eid lookup, adjacent `(s,p,o)` dedup for `SetOfTriples`
- [x] 3.4 Prove adjacent dedup yields each distinct visible `(s,p,o)` once
- [x] 3.5 Refinement test: random stores, every order × prefix × view, `ModelStore` vs `SqliteStore` scans equal

## 4. Index nested-loop evaluator

- [x] 4.1 Add `Exec/Inlj`: nested loop over a pattern order with key-prefix binding; hash join on shared certain variables for non-pattern inputs
- [x] 4.2 Add `Exec/Order`: greedy order (bound positions, then per-predicate counts refreshed after commit)
- [x] 4.3 Prove join-order independence: for every permutation, INLJ = reference natural join, in `TiramemsuProofs/Query/Inlj`; theorem-index entry marked as the M3b contract
- [x] 4.4 Add `Exec/Eval` for all operators over `SortedRange`, reusing `Sem` for expressions and aggregates
- [x] 4.5 Prove evaluator = `denote` on `ModelStore` for every plan (exact list under root `OrderLimit`), using the M1 encode/decode bijection for the id/value bridge
- [x] 4.6 Test: every permutation of 2–5-pattern joins on random stores equals `denote`

## 5. Push-down and binding passing

- [x] 5.1 Add `Exec/Pushdown`: conjunct placement by certain variables, constant equalities as key prefixes, sideways binding into right sides only for variables they certainly bind
- [x] 5.2 Prove push-down and binding passing preserve `denote`
- [x] 5.3 Tests for the `nested-loop-join` scenarios, including the `!BOUND` optional case

## 6. Path expressions and automaton

- [ ] 6.1 Add `Path/Letter` and the declarative language `lang : PathExpr → Set Word` (proofs) plus `Walk` over a store view
- [x] 6.2 Add `Path/Syntax`: SPARQL 1.1 property-path parser with `{m,n}`, CURIEs, `@vocab` names, `Parse` errors with spans, `Unsupported` for negated sets; printer; round-trip property test and Rust test vectors
- [x] 6.3 Add `Path/Nfa` (inverse pushed down, repetition unrolled, 200 000-state cap) and `Path/Dfa` (subset construction over the refined alphabet, 4 096-state cap → `Unsupported("path expression too complex")`) — implemented as one module `Path/Automaton` compiling by Brzozowski derivatives (same DFA semantics, no intermediate NFA; see design "Path engine")
- [x] 6.4 Prove DFA language = `lang e` and run uniqueness; prove `lang e.inverse` = reversed, direction-flipped words
- [x] 6.5 Add `Path/Hop`: stored, inverse, virtual and wildcard neighbours over `SortedRange`, one view per evaluation

## 7. Path search modes

- [x] 7.1 Add `Path/Search/Reach` (BFS over `(node, state)` with fuel `min(maxHops, N·Q)`, rows by hops then raw id) — fuel implemented as `path_max_states + 1` layers plus the `maxHops` cut (see design "Path engine")
- [ ] 7.2 Prove REACH = ends of matching walks within the bound, minimal hops, each once; prove the fuel bound sufficient
- [ ] 7.3 Add `Path/Search/Trail` (arena, identity check, fuel `min(maxHops, I)`, hop-key order) and prove it equals the matching trails, each once, with sufficient fuel
- [ ] 7.4 Add `Path/Search/Shortest` (ANY and ALL, layered predecessors, hop-key order) and prove minimality, hop-key-least choice, and exactly-once enumeration
- [x] 7.5 Add the `pathMaxStates` guard (`PathLimitExceeded`, no truncation) and its golden test
- [x] 7.6 Brute-force walk enumerator over small graphs as a test oracle for all modes

## 8. Graph-scoped and time-respecting paths

- [x] 8.1 Add graph-set filtering of hops (membership visible in the hop's view; virtual hops check the stepped statement; zero-hop rows independent of G)
- [ ] 8.2 Prove graph-scoped rows = unscoped rows whose hop statements all have a visible membership in G
- [x] 8.3 Add `Path/Search/Timed`: hop rule, label-correcting REACH with earliest arrival, timed TRAIL, Pareto-pruned shortest modes, arrival reporting
- [ ] 8.4 Prove hop-rule monotonicity, REACH earliest arrival, the timed search bound `N·Q·(card T + 1)`, and antitonicity in the start instant
- [x] 8.5 Tests for every `path-evaluation` scenario, and timed results against brute-force enumeration

## 9. Path patterns in queries

- [x] 9.1 Add `Path/Engine` and wire `PathPattern` into `denote` and `Exec/Eval`: start-bound or end-bound with the inverse expression, `Unsupported` without a bound endpoint, `bindPath`, graph selectors `Set` and `Var`
- [ ] 9.2 Prove evaluation from the end equals the reversed rows from the start
- [x] 9.3 Extend 4.5 to trees containing path patterns

## 10. Query provenance

- [x] 10.1 Add `Prov/EvalProv` with the citation rules of `query-provenance` (set-of-triples siblings, memberships, LeftJoin, Union, distinct merge, aggregate union, path hops) and ascending duplicate-free eid lists
- [ ] 10.2 Prove erasure: rows without eid lists = `denote`
- [ ] 10.3 Define the witness semantics `denoteW` and prove soundness (cited eids visible in a citing leaf's view and supporting the row) and sufficiency (row ∈ `denoteW` restricted to its citations)
- [x] 10.4 Tests for every `query-provenance` scenario, including stale-answer detection

## 11. Fact bundles

- [x] 11.1 Add `Bundle/Value` and `Bundle/Export`: dependents plus downward closure, exclusions to a fixed point, reference order with source-eid ties, cycle members last, anonymous labels by first appearance, `NotLive`/`Unsupported` roots
- [x] 11.2 Add `Bundle/Import` as a `TxM` program: structure and cycle checks before writing, `addToGraph` for memberships, `assert` otherwise, fresh node per label, import report
- [ ] 11.3 Prove the round trip (fresh store, then re-export, equal up to id renaming after collapsing equal content) in `TiramemsuProofs/Bundle/RoundTrip`
- [ ] 11.4 Prove re-import of a label-free bundle changes no live statement and reports nothing new
- [x] 11.5 Add `Bundle/Json` (`tiramemsu-bundle/1`), round-trip property test, byte comparison with the Rust oracle
- [x] 11.6 Tests for every `fact-bundles` scenario, including as-of export and atomic schema failure

## 12. Lean API

- [x] 12.1 Add `Api/Options` (`OpenOptions` with defaults) and `Api/Errors` (Rust variant names and fields)
- [x] 12.2 Add `Db.open`, `Db.transact`, `Db.with`, `Db.now`/`asOf`/`history`, `View.validAt` over the M2 shell; `Tx.importBundle`
- [x] 12.3 Add the view reads (`triples`, `values`, `dependents`, `graphs`, `graphMembers`, `encode`, `decode`, `eventsSince`)
- [x] 12.4 Add `View.execute` (validation first, one snapshot, provenance option), `View.path`, `View.pathWith`, `View.bundle`, `Bundle.toJson`/`fromJson`
- [x] 12.5 Add `View.explain` with text and JSON rendering and golden plans
- [x] 12.6 Tests for every `lean-api` scenario, including cross-opening files with the Rust build and one test per listed deviation

## 13. CLI

- [x] 13.1 Add the `tiramemsu` executable with the commands, view flags and term syntax of `lean-api` "Command-line tool"
- [x] 13.2 Golden tests for JSON-lines output, error JSON with exit status 1, usage errors with exit status 2, and the bundle pipe between two files

## 14. Cross-checks and benchmarks

- [x] 14.1 Refinement suite: random stores and random validated IR trees on `ModelStore` and `SqliteStore`; also paths, dependents and bundles
- [x] 14.2 Differential suite against the pinned Rust build through the M0 oracle harness: shared IR case file built with the Rust `tm-ir` builder; paths via `View::path_with`; bundles by JSON bytes; double folds compared with tolerance where listed
- [x] 14.3 End-to-end tests for the Rust recipes that need no SPARQL or Cypher syntax (impact analysis, evidence chains through time, edit lineage, journeys, portable facts)
- [x] 14.4 Report-only benchmarks against Rust for point and 2-hop lookups, acyclic BGPs and paths (D14)

## 15. Proof gates, documentation and validation

- [ ] 15.1 Add every Tier 2 theorem to the theorem index against its requirement; CI axiom check passes with no `sorry`, `partial`, `native_decide` or user axioms in the new modules
- [ ] 15.2 Update `lat.md/` (architecture and verification sections for the evaluator, paths, provenance and bundles; the listed deviations), linking each section to the new modules
- [ ] 15.3 Run `lat check` and fix all failures
- [ ] 15.4 Run `openspec validate m3a-ir-evaluator-paths --strict` and fix all failures
