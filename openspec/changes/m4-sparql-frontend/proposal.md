## Why

v1 (M0–M3) gives a verified core reachable only through the Lean API and the IR; every Rust user, agent recipe and test talks to tiramemsu in SPARQL. M4 adds the SPARQL front end in Lean so the Lean build answers the same SPARQL text with the same results as the pinned Rust build (D4, D6), executing through the proven M3 evaluator rather than SQL codegen (D3).

## What Changes

- A SPARQL 1.1 lexer and parser written in Lean (no external parser), total by construction, accepting the full SPARQL 1.1 query and update grammar plus the SPARQL 1.2 triple-term, reifier and annotation syntax. Parse errors carry line, column and byte offset.
- Static checks and lowering of queries to the M3 logical IR: `SELECT`, `ASK`, `CONSTRUCT` (and `DESCRIBE` rejected as in Rust), all graph-pattern operators, expressions, aggregates, subqueries, solution modifiers, property paths (recursive ones on the M3 path engine), named graphs as `sys:inGraph` tags, predeclared prefixes from the database vocabulary.
- Temporal dataset syntax exactly as Rust: `tm:` time IRIs in `FROM`, `FROM NAMED`, `USING`, `USING NAMED` and `SERVICE`, nesting innermost-first, and the statement-time virtual predicates (`tm:txAdded`, `tm:txRetracted`, `tm:addedAt`, `tm:retractedAt`, `tm:validFrom`, `tm:validTo`, `tm:retractKind`).
- RDF 1.2 annotations mapped to statement ids and layers (reifiers bind eids; `rdf:reifies` is virtual).
- SPARQL Update mapped onto the M2 memory verbs: insert = idempotent assert, delete = retract with cascade (never a physical delete), one request = one transaction; graph operations as membership statements.
- Results: SPARQL 1.1 JSON (with skolem IRIs and the optional non-standard `"provenance"` member), N-Triples / RDF 1.2 N-Triples for `CONSTRUCT`; query provenance option built on the M3a provenance evaluator.
- Conformance: differential tests against the pinned Rust build on shared `.db` files over the Rust SPARQL corpus and recipes, generated-query differential testing, and the W3C SPARQL test suite as a second oracle with a tracked expected-failure list derived from Rust's.
- A deviation register listing every deliberate difference from Rust and from W3C (D6). Proof tier 3 is tested, not proven (D2); only properties inherited from M2/M3 proofs are stated as machine-checked.

## Capabilities

### New Capabilities
- `sparql-query`: SPARQL query forms, parsing and errors, prefixes and vocabulary, pattern and expression semantics, property paths via the M3 path engine, named graphs as tags, result terms, SPARQL JSON and N-Triples output, the provenance option, and execution through the proven evaluator.
- `sparql-update`: `INSERT DATA`, `DELETE DATA`, `DELETE/INSERT … WHERE`, graph operations and their mapping onto memory verbs, transaction and report semantics, constraint checks, unsupported operations.
- `sparql-rdf12-annotations`: RDF 1.2 triple terms, reifiers and annotation syntax mapped to statement ids and layers, in queries, updates and `CONSTRUCT` output.
- `sparql-temporal-dataset`: `tm:` time IRIs in dataset clauses and `SERVICE`, view scoping rules, valid-time filtering, and the statement-time virtual predicates.
- `sparql-conformance`: differential testing against the pinned Rust build, the W3C SPARQL suite with its expected-failure list, and the deviation register.

### Modified Capabilities
<!-- none: there are no archived specs yet -->

## Impact

- New runtime modules under `Tiramemsu/Sparql/` (Lean core + Std only, D7); a few lemmas in `TiramemsuProofs/Sparql/` that instantiate M2/M3 theorems for the SPARQL path (no new proof tier).
- Depends on M2 (verbs, transactions, views, predicate schema, graph membership), M3a (IR, evaluator, path engine, provenance) and M3b (join planner). Does not change the file format, the IR, or any proven definition.
- Lean API and CLI gain a SPARQL entry point and a SPARQL entry point with options; the JSON bridge operations that carry SPARQL arrive with M6 (D9).
- Test infrastructure: a Rust oracle runner (pinned commit, D6) driven over shared `.db` files; a copy of the W3C SPARQL test data pinned by commit; CI jobs for the differential and W3C suites. Benchmarks for SPARQL are report-only (D14).
