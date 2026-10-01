## Purpose

The public Lean API (`Db`, `View`, `Tx`) and the `tiramemsu` command-line tool through which applications and later bindings use the store and the proven query core, mirroring the Rust facade with every deviation listed.

## ADDED Requirements

### Requirement: Opening a database
`Db.open path options` SHALL open or create a database file in the Rust format 1, so a file written by either build SHALL be readable and writable by the other. `OpenOptions` SHALL offer `readers` (default 4), `clock` (system clock, injectable), `busyTimeout` (5 s), `termCacheCapacity` (16 384), `optimizeEvery` (1000 commits), `pathMaxHops` (15) and `pathMaxStates` (1 000 000), with the Rust meanings. Opening a newer format SHALL fail with `FormatVersion`, and a SQLite file with user tables but no `meta` table with `ForeignFile`.

#### Scenario: Open a Rust-written file
- **WHEN** a file written by the pinned Rust build is opened with `Db.open`
- **THEN** every statement, term and transaction reads back as the Rust build reads it

#### Scenario: Rust opens a Lean-written file
- **WHEN** a file written by the Lean build is opened by the pinned Rust build
- **THEN** the Rust build reads the same statements and accepts new writes

### Requirement: Transactions and speculation
`Db.transact options body` SHALL run a transaction body (a program over `Tx` operations) atomically on the writer and return the transaction report; a failing body SHALL leave no trace. `Db.with body query` SHALL run the body speculatively, run the query on the speculative state, and discard every write. `Tx` SHALL offer the memory verbs and graph-membership operations of the store, plus `importBundle`.

#### Scenario: Failed transaction leaves no trace
- **WHEN** a transaction body asserts two statements and then fails
- **THEN** no transaction row, statement or term from it is visible afterwards

#### Scenario: Speculative query
- **WHEN** `Db.with` asserts `(alice worksAt globex)` and its query reads alice's employer
- **THEN** the query sees `globex` and the database afterwards does not

### Requirement: Views
`Db.now`, `Db.asOf (tx t | instant ms)` and `Db.history` SHALL return views, and `View.validAt ms` SHALL add a valid-time selector. Creating or deriving a view SHALL do no I/O. Every read on a view SHALL use the store's snapshot rules for views.

#### Scenario: As of an instant
- **WHEN** `Db.asOf (instant ms)` is used with `ms` between the instants of transactions 3 and 4
- **THEN** the view equals `Db.asOf (tx 3)`

#### Scenario: Valid-time view
- **WHEN** `Db.now.validAt d` reads a statement valid `[d1, d2)` with `d1 ≤ d < d2`
- **THEN** the statement is visible, and with `d = d2` it is not

### Requirement: View reads
A view SHALL offer `triples (s? p? o?)`, `values s key` (statements, else volatile values under `Now` only), `dependents eid`, `graphs`, `graphMembers g`, `encode value` (a dictionary lookup that never inserts), `decode id` and `eventsSince t`, with the meanings of the corresponding Rust `View` methods.

#### Scenario: Encode never inserts
- **WHEN** `encode` is called on an IRI absent from the dictionary
- **THEN** it returns none and the dictionary is unchanged

#### Scenario: Dependents on a past view
- **WHEN** `dependents e1` is read on `Db.asOf (tx 150)`
- **THEN** it returns what stood on `e1` at transaction 150

### Requirement: IR execution
`View.execute query params options` SHALL validate the query, then evaluate it in one snapshot of the view's store and return the result columns, the rows as decoded values, and, when `options.provenance` is set, each row's cited eids. Validation and parameter errors SHALL be raised before any read. A pattern view of a query SHALL take precedence over the handle's view; the handle's view is the default only for front-end lowering.

#### Scenario: Execute a two-pattern join
- **WHEN** `Join[(?a worksAt ?c), (?c locatedIn ?city)]` is executed on `Db.now`
- **THEN** the result has columns `?a, ?c, ?city` and one row per matching pair

#### Scenario: Invalid query fails before reading
- **WHEN** a query whose `Extend` rebinds a variable is executed
- **THEN** it fails with `InvalidQuery` and no statement is read

### Requirement: Path API
`View.path start text mode maxHops` SHALL evaluate the path text from `start` in the view, and `View.pathWith start text args` SHALL additionally take a graph set and a time-respecting option with an optional start instant. Each result SHALL be a path row (start, end, hops, path value when the mode returns one, arrival). The defaults SHALL be `REACH`, no hop bound, no graph set, not time-respecting.

#### Scenario: Reach from the API
- **WHEN** `a knows b` and `b knows c` are live and `View.path a "knows+" REACH none` runs on `Db.now`
- **THEN** it returns ends `b` (1 hop) and `c` (2 hops)

#### Scenario: Time-respecting call
- **WHEN** `View.pathWith` is called with time-respecting enabled from 2024
- **THEN** each row carries its arrival, or none when it is −∞

### Requirement: Bundle API
`View.bundle root` SHALL export the fact bundle of `root` in the view; `Tx.importBundle bundle` SHALL import it in the caller's transaction and return the import report; `Bundle.toJson` and `Bundle.fromJson` SHALL write and read the `tiramemsu-bundle/1` form.

#### Scenario: Portable fact between two files
- **WHEN** a bundle is exported from database A, written to JSON, read back and imported into database B
- **THEN** B holds the fact and its layers with fresh eids

### Requirement: Explain
`View.explain query params` SHALL return the physical plan the Lean evaluator will run: per join, the pattern order, and per pattern the index order or eid lookup, the key prefix, the index family and the pushed filters; per path, the mode, the automaton size and the evaluation direction. The plan SHALL be deterministic for the same query, view and statistics, and SHALL be available as text and as JSON. This SHALL replace the Rust `EXPLAIN QUERY PLAN` output (listed deviation).

#### Scenario: Explain a chain join
- **WHEN** `Join[(alice knows ?b), (?b worksAt ?c)]` is explained
- **THEN** the plan lists the two patterns in evaluation order, with `spo` and its key prefix for each

### Requirement: Typed errors
Every failure SHALL be a value of one error type whose variants carry the Rust names and fields used by these operations, including `InvalidQuery`, `Unsupported`, `Parse` (with dialect and byte span), `PathLimitExceeded`, `NotLive`, `InvalidTerm`, `FormatVersion`, `ForeignFile`, `Sqlite` and `Custom`, plus every store-operation error of the write verbs.

#### Scenario: Path limit error
- **WHEN** a path evaluation exceeds `pathMaxStates`
- **THEN** it fails with `PathLimitExceeded` carrying the limit

### Requirement: Listed deviations from the Rust facade
The Lean API SHALL differ from the Rust facade only in the following, each covered by a test asserting the Lean behaviour:
- `explain` returns the Lean physical plan instead of SQLite `EXPLAIN QUERY PLAN`;
- the `tm_path` SQL table function and SQL UDFs are absent, and paths are reachable through `View.path`, `View.pathWith` and path patterns;
- there is no host abstraction: `open_with_host`, `capabilities`, `query_engine` and `MissingCapability` are absent;
- double `SUM` and `AVG` fold in the canonical value order and can differ from Rust in the last bits;
- the search-state count behind `PathLimitExceeded` is the Lean engine's own, so the limit can trip at a different point than in Rust;
- the Rust test hooks (`read_sql`, `set_query_hook`, term-cache probes) are absent;
- bundle N-Triples export, SPARQL and Cypher methods, and the Cypher-only IR operators arrive with later milestones.

#### Scenario: No table function
- **WHEN** a SQL client calls `tm_path` on a file opened by the Lean build
- **THEN** SQLite reports that no such table function exists

### Requirement: Command-line tool
The `tiramemsu` executable SHALL take a database path and one command: `info`, `assert s p o [--valid-from t] [--valid-to t]`, `retract eid`, `triples [--s t] [--p t] [--o t]`, `values s key`, `dependents eid`, `path start expr [--mode m] [--max-hops n] [--graph g]… [--time-respecting[=t]]`, `bundle eid`, and `import-bundle file` (`-` for standard input). Read commands SHALL accept `--as-of <t or RFC 3339>`, `--history` and `--valid-at <date or date-time>`. Terms SHALL be written as `<iri>`, a CURIE over the database prefixes, a quoted literal with optional `@lang` or `^^datatype`, a bare number or boolean, or a skolem IRI `<urn:tiramemsu:K:n>` for `K` in `node`, `bnode`, `stmt`, `tx`, also accepted in the short form `K:n`. Output SHALL be one JSON value per line on standard output; an error SHALL print its kind and message as JSON on standard error and exit with status 1; a usage error SHALL exit with status 2. Each write command SHALL be one transaction.

#### Scenario: Assert then read
- **WHEN** `tiramemsu m.db assert v:alice v:worksAt v:acme` runs, then `tiramemsu m.db triples --s v:alice`
- **THEN** the second prints one JSON line for the statement, with its eid

#### Scenario: Bundle between files
- **WHEN** `tiramemsu a.db bundle stmt:5 | tiramemsu b.db import-bundle -` runs
- **THEN** `b.db` holds the fact and its layers, and the import report is printed

#### Scenario: Usage error
- **WHEN** `tiramemsu m.db path` runs without a start
- **THEN** the tool prints usage to standard error and exits with status 2
