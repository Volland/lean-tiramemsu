## Purpose

How the tested (Tier 3) Cypher front end is held to its contract: differential runs against the pinned Rust build on shared database files, the openCypher TCK as a second oracle, cross-dialect agreement with SPARQL on one store, and a registry that lists every deviation from Rust.

## ADDED Requirements

### Requirement: Read differential against the pinned Rust build
The test suite SHALL run every Cypher read query of its corpus (all spec scenarios, the cross-dialect corpus, the TCK queries that both builds accept, and generated queries) on the Lean build and on the pinned Rust build over the same `.db` file and parameters, and compare canonical results: same column names in order; same rows as a multiset, or as a sequence for the sort keys when the query orders; for an error, the same error kind and, for `Parse`, the same span start offset. Any mismatch not covered by a listed deviation MUST fail the build.

#### Scenario: Equal results
- **WHEN** `MATCH (a:Person)-[r:worksAt]->(c) RETURN a, r, c.name ORDER BY c.name` runs on both builds over the same fixture file
- **THEN** both canonical results are equal and the check passes

#### Scenario: Error kind and span compared
- **WHEN** `MATCH (n:Person RETURN n` is compiled by both builds
- **THEN** both fail with `Parse` at byte 6, and the differing message texts do not fail the check (deviation DV-C1)

#### Scenario: Unlisted mismatch
- **WHEN** a query returns one extra row on the Lean side and no deviation covers it
- **THEN** the build fails, naming the query, the fixture and the extra row

### Requirement: Write differential
The test suite SHALL run Cypher write sequences on both builds from identical starting files, with a deterministic clock and the same open options, and SHALL require equal `RETURN` rows, equal transaction reports, and byte-equal contents of the statement, term, tx and volatile tables afterwards. A file written by either build's Cypher writes SHALL be opened and queried by the other with equal results.

#### Scenario: SET ladder on both builds
- **WHEN** the same sequence of `CREATE`, `SET`, `MERGE`, `REMOVE` and `DETACH DELETE` queries runs on both builds
- **THEN** the reports per query and the final table contents are equal

#### Scenario: Cross-opened file
- **WHEN** the Lean build writes a file through Cypher and the Rust build runs the read corpus on it
- **THEN** the results equal those of the Lean build on the same file

### Requirement: Generated-query differential
The test suite SHALL generate random well-formed Cypher queries from a grammar covering the supported subset (patterns, variable-length and shortest patterns, dual-view uses, time clauses, expressions, aggregation, subqueries, writes) over the conformance fixtures, run them on both builds, and compare as in the read and write differentials. Generation SHALL be seeded and reproducible, and every failing seed SHALL be kept as a regression query.

#### Scenario: Reproducible failure
- **WHEN** a generated query with seed s diverges between the builds
- **THEN** the report prints s and the query text, rerunning with s reproduces the same query, and the query is added to the regression corpus

### Requirement: Comparison rules
Canonical values SHALL compare: Integers exactly; Floats bit-exactly, except results of transcendental functions (`sin`, `cos`, `tan`, `cot`, `asin`, `acos`, `atan`, `atan2`, `exp`, `log`, `log10`, `haversin`), which SHALL agree within one unit in the last place; DateTimes by instant and offset; nodes, relationships and statements by element id; lists, maps and paths structurally. Results of `rand`, `randomUUID`, `timestamp`, argument-less `date()`/`datetime()`/`localdatetime()` and their `.statement`, `.transaction` and `.realtime` forms SHALL be compared by type only.

#### Scenario: Offset mismatch detected
- **WHEN** one build returns DateTime 2026-03-01T12:00:00.000+02:00 and the other 2026-03-01T10:00:00.000Z for the same cell
- **THEN** the cell is a mismatch

#### Scenario: Nondeterministic function
- **WHEN** `RETURN rand() AS r, randomUUID() AS u` runs on both builds
- **THEN** the check passes when both return a Float and a String

### Requirement: openCypher TCK with tracked expected failures
The test suite SHALL run the openCypher TCK at the same release and commit as the pinned Rust build, every scenario end to end through the Cypher entry points, with setup through the write entry point and side effects computed by diffing the store before and after. Scenarios expected to fail SHALL be listed one per line with a reason referencing a spec requirement or deviation. The run MUST fail on an unexpected failure and on an unexpected pass. The list SHALL start equal to the Rust build's list at the pin, and any difference from it SHALL name a deviation in the registry.

#### Scenario: Unexpected pass
- **WHEN** a scenario on the expected-failure list passes
- **THEN** the run fails and names the scenario, so the list is only changed by an explicit edit

#### Scenario: Parity with Rust
- **WHEN** the TCK runs on both builds
- **THEN** the sets of failing scenarios are equal, or every difference names a listed deviation

### Requirement: Cross-dialect agreement on one store
The test suite SHALL hold named fixtures, applied through the API only with a deterministic clock, covering at least: a social and employment graph with labels and literals; parallel edges; layers two levels deep; a superseded fact; a retraction with cascade; a cardinality-one replacement; valid-time episodes; and every literal type. It SHALL hold at least 40 SPARQL/Cypher query pairs, each with a fixture, a comparison mode (`bag` or `set`), an ordering mode, a column mapping and an optional view, spread over: one- and multi-hop patterns; labels and `rdf:type`; literal filters; optional parts; `EXISTS`/`NOT EXISTS`; `UNION`; grouping; ordering with `SKIP`/`LIMIT`; subqueries; as-of by transaction and by instant; valid-at; history; per-scope time; statement time properties; variable-length patterns and property paths; and the dual view versus reifiers. Both sides SHALL run on the same Lean store and normalise to canonical values, where IRIs and the skolem forms parse to one identifier, SPARQL unbound and Cypher `null` coincide, and SPARQL transaction IRIs and Cypher Integers from `txAdded` coincide. Unequal normalised results MUST fail the build.

#### Scenario: Corpus completeness
- **WHEN** the suite starts
- **THEN** it checks that there are at least 40 pairs and one pair per listed category, and fails naming any missing category

#### Scenario: Dual view equals reifier
- **WHEN** Cypher `MATCH (a)-[r:WORKS_AT]->(c), (b:Belief)-[:SUPPORTED_BY]->(r) RETURN r, b` and SPARQL `SELECT ?r ?b WHERE { ?a v:WORKS_AT ?c ~ ?r . ?b a v:Belief ; v:SUPPORTED_BY ?r }` run on the layers fixture
- **THEN** the normalised `r` and `b` columns are equal

#### Scenario: Per-scope time agrees
- **WHEN** SPARQL `SELECT ?before ?after WHERE { SERVICE <urn:tiramemsu:tm:asOf/3> { v:alice v:worksAt ?before } v:alice v:worksAt ?after . FILTER (?before != ?after) }` and the Cypher `CALL { USE AS OF 3 … }` equivalent run on the superseded-fact fixture
- **THEN** both return `(v:acme, v:globex)`

### Requirement: Documented dialect divergences
The corpus SHALL include divergence pairs that assert each side's exact result rather than equality, covering relationship isomorphism versus homomorphism (and convergence under `REPEATABLE ELEMENTS`), parallel edges as a bag of eids versus a set of triples (and convergence in `set` mode), multi-valued properties as a Cypher list versus SPARQL rows, and trail semantics of variable-length patterns versus set semantics of property paths.

#### Scenario: Isomorphism divergence
- **WHEN** on a single `knows` edge SPARQL `SELECT * WHERE { ?x v:knows ?y . ?z v:knows ?y }` and Cypher `MATCH (x)-[:knows]->(y)<-[:knows]-(z) RETURN *` run
- **THEN** SPARQL returns 1 row and Cypher 0, and with `MATCH REPEATABLE ELEMENTS` Cypher returns 1

#### Scenario: Parallel edges
- **WHEN** a fixture creates `(v:alice v:called v:bob)` twice and both dialects list `called` pairs
- **THEN** Cypher returns 2 rows and SPARQL 1, and the pair passes in `set` mode

### Requirement: Deviation registry
Every known behavioural difference between the Lean and the pinned Rust Cypher SHALL be listed in one registry with an identifier, the affected requirement, the exact difference and a test that pins it. The registry SHALL start with DV-C1 (`Parse` message text differs; kind and span start agree) and DV-C2 (regular-expression `\p{…}` / `\P{…}` classes are `Unsupported` on the Lean build). The differential, TCK and cross-dialect harnesses SHALL accept a mismatch only when a registry entry covers it, and a registry entry whose test no longer observes the difference MUST fail the build.

#### Scenario: Covered deviation
- **WHEN** `RETURN 'α' =~ '\\p{Greek}' AS g` runs on both builds
- **THEN** Rust returns `true`, Lean fails with `Unsupported`, and the check passes because DV-C2 covers it

#### Scenario: Stale entry
- **WHEN** a registry entry's pinning test finds both builds agree
- **THEN** the build fails, asking for the entry to be removed

### Requirement: Store-independent results
Every Cypher conformance check that runs on the Lean build SHALL run on both the pure model store and the SQLite store and require identical results, reports and errors.

#### Scenario: Model and SQLite agree
- **WHEN** the spec scenario suite runs on the model store and on the SQLite store
- **THEN** every query yields identical results on both
