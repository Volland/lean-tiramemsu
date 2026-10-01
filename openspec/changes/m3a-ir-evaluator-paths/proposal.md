## Why

After M2 the Lean store can write and time-travel, but nothing can query it: there is no query algebra, no evaluator, no path engine and no public API. M3a adds the Tier 2 query core (D2) so that the evaluator that runs is the one that is proven (D3): the logical IR gets a denotational semantics, joins are proven independent of their order (D13), paths are proven equal to their regular-path specification, and provenance and bundles get their soundness and round-trip theorems. With M3b (Leapfrog Triejoin and the planner) it completes v1 (D4).

## What Changes

- Add the logical IR in `Tiramemsu`: view-scoped triple patterns, path patterns and inline values; Join, LeftJoin, Union, Filter, Extend, Aggregate, Project (distinct), OrderLimit; expressions with EXISTS; named-graph selectors; relationship-isomorphism groups; the three semantic flags; parameters; a structural validator.
- Add the reference semantics `⟦op⟧ : View → Bag Row` as a total, computable Lean definition. It is the specification of every query result and the test oracle for SQLite runs.
- Add the index nested-loop join evaluator over the `Store` range-scan interface (D3), with filter push-down and sideways binding passing, proven equal to the reference natural join for every pattern order (D13). Define the sorted-iterator interface and the order-independence statement that M3b's LFTJ will also be proven against.
- Add the path engine: path text parser, Thompson NFA → DFA over predicate/direction letters (stored, virtual `sys:subject|object|predicate`, wildcard), BFS over the product with explicit, proven-sufficient fuel; REACH, TRAIL, ANY_SHORTEST, ALL_SHORTEST; graph-scoped and time-respecting (earliest-arrival) search; DFA over 4 096 states is `Unsupported`.
- Add query provenance: an annotated evaluator that cites the supporting statement eids of each row, proven sound and sufficient.
- Add fact bundles: export from a view, idempotent import, JSON form `tiramemsu-bundle/1`; round-trip and re-import proven on the model.
- Add the Lean API (`Db`, `View`, `Tx`, `OpenOptions`) mirroring the Rust facade for everything up to M3, plus a small `tiramemsu` CLI executable.
- Add Tier 2 proofs in `TiramemsuProofs` (D7), each indexed against its requirement; add refinement tests (`ModelStore` vs `SqliteStore`) and differential tests against the pinned Rust build (D6).
- Listed deviations from Rust (D6): `explain()` returns the Lean physical plan instead of SQLite `EXPLAIN QUERY PLAN`; the `tm_path` SQL table function is absent (D8); there is no host abstraction (`open_with_host`, `capabilities`, `query_engine`, `MissingCapability`); double `SUM`/`AVG` fold in a canonical order and may differ from Rust in the last bits; the `PathLimitExceeded` state count is Lean's own; bundle N-Triples export arrives with the SPARQL writer in M4; Cypher-only IR operators (`Unnest`, `RowNumber`, `Lookup`, null-safe join keys, volatile pattern opt-in) arrive with M5.

## Capabilities

### New Capabilities

- `query-ir`: the logical algebra (patterns with per-pattern views, operators, expressions, path patterns, graph selectors, isomorphism groups, semantic flags, parameters), validation rules and result column order.
- `query-semantics`: the denotational reference semantics over bags of rows, virtual predicates, three-valued filter logic, aggregation, ordering, and the trusted hardware-float boundary. Proven: join algebra laws, evaluator = denotation, stable historical results.
- `nested-loop-join`: the sorted range-scan interface, index choice, index nested-loop evaluation, filter push-down and binding passing. Proven: equal to the reference natural join for every pattern order (D13); push-down sound.
- `path-evaluation`: path expression language and text syntax, layer hops, automaton compilation, the four modes, endpoint binding, hop limits, search guard, graph scoping, time-respecting search, ordering. Proven: results = regular-path reachability specification; fuel bound sufficient; time-respecting search monotone and earliest-arrival.
- `query-provenance`: rows annotated with the eids of their supporting statements. Proven: annotations do not change rows; every cited eid is visible and supports the row; the cited set re-derives the row.
- `fact-bundles`: bundle export, exclusions, value and order, anonymous nodes, idempotent import, cycles, JSON form. Proven: export→import round-trip into a fresh store up to id renaming; re-import is a no-op.
- `lean-api`: the public Lean `Db`/`View`/`Tx` API, open options, IR execution, paths, bundles, explain, errors, listed deviations, and the CLI.

### Modified Capabilities

None. No specs are archived yet; M3a builds on capabilities introduced by M0–M2 (`Store` interface, codec, `temporal-views`, `retraction-cascade`, `named-graph-membership`, `memory-verbs`, `speculative-transactions`, `connection-concurrency`) without changing their requirements.

## Impact

- New runtime modules under `Tiramemsu/IR/`, `Tiramemsu/Sem/`, `Tiramemsu/Exec/`, `Tiramemsu/Path/`, `Tiramemsu/Prov/`, `Tiramemsu/Bundle/`, `Tiramemsu/Api/`, and the `tiramemsu` executable; proofs under `TiramemsuProofs/Query/`, `/Path/`, `/Prov/`, `/Bundle/`. Runtime stays Lean core + Std (D7).
- Depends on M0 (Store interface and contract, proof gates, oracle harness), M1 (codec, term dictionary, value order) and M2 (views, dependents, verbs, graph membership, `Db` shell, `TxM`).
- No new external dependency; SQLite is still reached only through leansqlite range scans and writes (D3, D8).
- Extends the theorem index and the CI axiom check with Tier 2 theorems; adds report-only query and path benchmarks against Rust (D14).
- Unblocks M3b (LFTJ proves against the same order-independence statement), M4 (SPARQL lowers to this IR) and M5 (Cypher).
