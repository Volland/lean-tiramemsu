## Why

After v1 (M0–M3) the Lean core is only reachable through the Lean API, the CLI and (after M4) SPARQL. Every Rust user who talks to tiramemsu through Cypher, including the Node.js and Python packages that M6 switches over, needs the same Cypher surface on the Lean build, with the same results on the same files (D6). M5 delivers it as a tested front end (proof Tier 3, D2) on top of the proven IR, path engine and memory verbs, so Cypher gains the proven core without a formal semantics of openCypher (overview Non-Goals).

## What Changes

- New hand-written openCypher parser in Lean (core + Std only, D7) with byte spans into the original text, covering the Rust subset plus the tiramemsu extensions (`USE` time clauses, `MATCH REPEATABLE ELEMENTS` / `DIFFERENT RELATIONSHIPS`, `` `@id` ``).
- Semantic analysis (scopes, variable kinds including the dual-view relationship-in-node-position rule, aggregates, parameters, write checks) with `Parse` / `Unsupported` errors before anything runs.
- Lowering of graph patterns, label and property-map tests, relationship isomorphism, variable-length and shortest patterns and every time view to the proven M3 IR and path engine; no SQL is generated (D3).
- A tested Cypher interpreter for what the IR does not model (Cypher values with lists and maps, expressions, functions, projection, aggregation, ordering, `UNWIND`, `UNION`, `CALL` subqueries, procedures), running over IR result rows.
- Cypher writes (`CREATE`, `MERGE`, `SET`, `REMOVE`, `DELETE`, `DETACH DELETE`) compiled to the M2 memory verbs (create, assert, upsert, supersede, retract with cascade) in one transaction, under the M2 predicate-schema checks.
- The dual view: every statement eid is also a `:Statement` node, so Cypher reads and writes layers; ids are shared with SPARQL through the skolem IRIs.
- The Rust temporal syntax: `USE AS OF <t | datetime>`, `USE VALID AT`, `USE HISTORY`, per-`CALL` scopes, and statement time properties (`txAdded`, `txRetracted`, `addedAt`, `retractedAt`, `validFrom`, `validTo`, `` `tm:retractKind` ``); volatile values as `Now`-only virtual properties.
- Conformance: differential tests against the pinned Rust build on shared `.db` files (reads, writes, errors, generated queries), the openCypher TCK 2024.3 as second oracle with a tracked expected-failure list, the cross-dialect SPARQL/Cypher corpus, and a deviation registry.
- Listed deviations from Rust (D6), initial set: **DV-C1** `Parse` error message text is not byte-identical (error kind and span start offset are); **DV-C2** regular-expression Unicode property classes `\p{…}` / `\P{…}` fail with `Unsupported` instead of matching.
- No breaking change: M5 only adds surfaces. Benchmarks stay report-only (D14).

## Capabilities

### New Capabilities

- `cypher-read`: read queries over the property-graph projection of statements: `MATCH`/`OPTIONAL MATCH`/`WHERE`/`WITH`/`RETURN`/`UNWIND`/`ORDER BY`/`SKIP`/`LIMIT`, aggregates, `UNION`, `CALL` and `EXISTS` subqueries, variable-length and shortest patterns via the path engine, relationship isomorphism, the Rust function registry, `` `@id` `` / `elementId()` / `id()`, volatile virtual properties, the value model, and parse / semantic / runtime errors.
- `cypher-write`: Cypher write clauses mapped onto the memory verbs in one atomic transaction: `DELETE` retracts with cascade, `SET` asserts or supersedes, cardinality-one and unique-key semantics, `MERGE` as upsert or atomic match-or-create, schema and namespace checks.
- `cypher-dual-view`: a relationship is also a `:Statement` node, so Cypher reaches and writes layers; one id space with SPARQL.
- `cypher-temporal-clauses`: `USE AS OF` / `VALID AT` / `HISTORY` for a query or a `CALL` scope, override rules against the handle view, statement time properties, and valid-time `SET`.
- `cypher-conformance`: differential tests against the pinned Rust build, the openCypher TCK with tracked expected failures, cross-dialect SPARQL/Cypher agreement on one store, generated-query differential runs, and the deviation registry.

### Modified Capabilities

None. M0–M4 capabilities are consumed unchanged.

## Impact

- New runtime modules `Tiramemsu/Cypher/**` (parser, sema, lowering, interpreter, writes, values, regex, temporal and Unicode tables); new API entry points `View.cypher`, `Tx.cypher`, `Db.cypherWrite`, and a `cypher` CLI subcommand.
- Generated data modules: IANA tz offsets and Unicode case mapping, both pinned to the versions used by the pinned Rust build (chrono-tz and Rust `std`), so named zones and `toLower`/`toUpper` agree.
- Test assets: vendored openCypher TCK 2024.3 features, expected-failure list seeded from the Rust allowlist, the cross-dialect corpus and fixtures (needs M4 for the SPARQL side), the Cypher mode of the M0 differential harness.
- Depends on: M2 memory verbs, transactions, predicate schema, vocabulary, volatile state; M3a IR, evaluator, path engine; M3b planner; M4 for the cross-dialect suite only. No change to the file format, the trusted base or the proof library.
