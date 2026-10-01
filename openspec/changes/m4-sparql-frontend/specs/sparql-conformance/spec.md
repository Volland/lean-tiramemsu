## Purpose

Defines how the Lean SPARQL front end, which is tested rather than proven, is held to the pinned Rust build and to the W3C SPARQL test suite, and how every deliberate difference from either is registered.

## ADDED Requirements

### Requirement: Differential testing against the pinned Rust build

A conformance harness SHALL run the same fixtures and SPARQL requests on the pinned Rust build and on the Lean build over the same database files and SHALL fail on any difference not covered by the deviation register. Fixtures SHALL be applied through the memory verbs of each build with a deterministic clock and SHALL produce identical `triple`, `tx` and `term` tables in both. Requests SHALL run on copies of a file written by Rust and, for a sample of at least one request per corpus category, on a file written by Lean, so each build reads the other's files. `NOW()` SHALL be fixed to the same instant in both.

#### Scenario: Fixture reproducibility across builds
- **WHEN** a fixture is applied by the Rust build and by the Lean build to fresh databases
- **THEN** their `triple`, `tx` and `term` tables are identical

#### Scenario: Unregistered difference fails the run
- **WHEN** a request returns one more row on the Lean side than on the Rust side and no register entry covers it
- **THEN** the harness fails and reports the fixture, the request text and the rows present on only one side

#### Scenario: Cross-file reading
- **WHEN** the Lean build runs the corpus sample on a file written by Rust, and Rust runs it on a file written by Lean
- **THEN** both results equal the results on each build's own file

### Requirement: Differential corpus

The corpus SHALL contain at least: every request of the Rust `tm-sparql` golden files with their expected results and errors; every SPARQL query and update in the Rust facade test suites for queries, updates, annotations, temporal syntax, named graphs, paths, results and provenance; every SPARQL recipe in the Rust recipes document; and every scenario of the `sparql-query`, `sparql-update`, `sparql-rdf12-annotations` and `sparql-temporal-dataset` specifications. The harness SHALL check at start that each listed source is present and non-empty, and fail naming any missing one.

#### Scenario: Corpus completeness
- **WHEN** the harness starts and the provenance suite has been removed from the corpus
- **THEN** it fails naming the missing provenance source

#### Scenario: Recipe query
- **WHEN** the recipe query that lists who wrote each employment fact through `tm:txAdded` and `sys:author` runs on the recipe fixture in both builds
- **THEN** both results are equal

### Requirement: Generated-query differential testing

A deterministic generator SHALL produce SPARQL requests from the grammar over each fixture's vocabulary, covering every supported operator, function, modifier, path form, time clause, graph clause and annotation form, and both builds SHALL run them. A seed that exposes an unregistered difference SHALL be stored as a regression case. Each CI run SHALL execute at least 10 000 generated requests, with the seed recorded.

#### Scenario: Reproducible failure
- **WHEN** a generated request with seed `s` shows a difference
- **THEN** the report contains `s` and the request text, and rerunning with `s` reproduces the same request

### Requirement: Result comparison

Results SHALL be compared in canonical form: `SELECT` rows as multisets of canonical terms per variable, and also in order on the sort keys when the query has `ORDER BY`; `ASK` by boolean; `CONSTRUCT` as triple sets up to blank-node isomorphism; SPARQL JSON documents byte for byte when the row order is fixed; update requests by their reports and the resulting `triple`, `tx` and `term` tables; provenance as the set of eids per row. Errors SHALL be compared by kind, by `Unsupported` feature text and by typed error code. `Parse` errors SHALL be compared by kind, and by position only for corpus entries that pin a position.

#### Scenario: Order compared only on sort keys
- **WHEN** a query ordered by `?age` returns two rows with equal `?age` in different orders on the two builds
- **THEN** the results compare equal

#### Scenario: Unsupported feature text
- **WHEN** a request fails with `Unsupported { feature: "SERVICE" }` on Rust and `Unsupported { feature: "service" }` on Lean
- **THEN** the harness reports a difference

#### Scenario: Update compared by tables
- **WHEN** `DELETE WHERE { ?p v:tag "x" }` runs on the same fixture in both builds
- **THEN** the reports and the resulting tables are identical

### Requirement: W3C SPARQL test suite as second oracle

A W3C runner SHALL execute the W3C SPARQL test data, pinned by commit, for the same in-scope categories as the pinned Rust runner (SPARQL 1.0 and 1.1 query, update and syntax categories, and the SPARQL 1.2 triple-term syntax and evaluation categories), each test on a fresh database, comparing results up to blank-node isomorphism with the same value-based literal comparison as the Rust runner. A tracked expected-failure list SHALL name every test allowed to fail with its reason and deviation class. The run SHALL fail on any failing test that is not listed and on any listed test that passes.

#### Scenario: Unlisted failure
- **WHEN** a W3C test fails and is not in the expected-failure list
- **THEN** the run fails naming the test

#### Scenario: Listed test now passes
- **WHEN** a test in the expected-failure list passes
- **THEN** the run fails naming the test, so the list is pruned

### Requirement: Expected-failure list derived from Rust

The expected-failure list SHALL start from the pinned Rust runner's expected-deviation list, keeping every entry whose cause is a design decision or a value semantics shared with Rust with the same intent. Entries caused only by the Rust parser library or by Rust SQL-executor limits not stated in a Rust specification SHALL be removed once the Lean build passes them, and each removal SHALL be recorded in the deviation register as a difference from Rust. No entry SHALL be added without a deviation-register entry that explains it.

#### Scenario: Shared design deviation kept
- **WHEN** the W3C test that expects `DROP GRAPH` to delete member statements runs
- **THEN** it fails on both builds, and the Lean list keeps it with the class `design`

#### Scenario: Parser quirk removed
- **WHEN** a W3C syntax test listed by Rust because its parser library rejects valid syntax passes on the Lean build
- **THEN** the entry is absent from the Lean list and the deviation register records that Lean accepts the text and Rust does not

### Requirement: Deviation register

Every deliberate difference of the Lean build from the pinned Rust build or from the W3C suite SHALL be listed in one register with an identifier, against whom it deviates (Rust, W3C or both), a class, a description and the tests that show it. The classes SHALL be: `design` (shared with Rust: canonical numeric and boolean literal collapse, relative IRIs rejected without `BASE`, the default graph as the union of all statements, graph deletes that retract memberships only, every reifier a stored statement, unsupported functions and forms); `value-semantics` (shared with Rust: decimal arithmetic and aggregates as `xsd:double`, string functions dropping language tags, `AVG` of an empty group unbound, `xsd:date` without timezone); `parser-quirk` and `rust-executor-limit` (the Lean build follows SPARQL where Rust does not); and `error-detail` (parse positions and messages). Both harnesses SHALL fail on a difference no entry covers and on an entry that no longer matches any difference.

#### Scenario: Numeric value collapsing is registered
- **WHEN** the W3C test expecting `"01"^^xsd:integer` and `"1"^^xsd:integer` to stay distinct under `DISTINCT` runs
- **THEN** it fails on both builds, and the register lists canonical numeric collapse as a `design` deviation against W3C naming that test

#### Scenario: Stale entry
- **WHEN** a register entry names a test whose results no longer differ
- **THEN** the harness fails naming the entry

### Requirement: Conformance runs in CI

The differential harness, the generated-query run and the W3C runner SHALL run in CI on every change to the SPARQL front end, the IR, the evaluator or the store, and any failure SHALL fail the build. The Rust oracle SHALL be built from the pinned commit only. SPARQL performance measurements SHALL be reported and SHALL NOT fail the build before the bindings milestone.

#### Scenario: Oracle pin
- **WHEN** the oracle is built from a commit other than the pinned one
- **THEN** the conformance job fails before running any request
