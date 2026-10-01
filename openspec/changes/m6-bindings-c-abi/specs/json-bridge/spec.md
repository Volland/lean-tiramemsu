## Purpose

Defines the JSON call surface of the Lean build, which the C ABI exports and the Node.js and Python packages wrap: one database, one call taking an operation name and JSON arguments, and one set of JSON forms for views, terms, results and errors, compatible with the Rust bridge.

## ADDED Requirements

### Requirement: One call surface

The bridge SHALL open a database from a path and an options object and run operations by name with a JSON argument object. It SHALL accept the reads `sparql`, `cypher`, `triples`, `path`, `events`, `graphs`, `graphMembers`, `values`, `dependents` and `bundle`, the writes `transact`, `cypherWrite` and `with`, and `optimize` and `info`. An unknown operation SHALL fail with `InvalidArgument`. Open SHALL accept only the options `readers`, `busyTimeoutMs`, `termCacheCapacity`, `optimizeEvery`, `pathMaxHops` and `pathMaxStates`, each a non-negative integer, SHALL reject any other key or a non-object with `InvalidArgument`, and SHALL create no file when it rejects its options. `info` SHALL return `path`, `readers` and `pathMaxHops`; `optimize` SHALL refresh the planner statistics and return `null`.

#### Scenario: Unknown operation
- **WHEN** the operation `nope` is called with `{}`
- **THEN** it fails with `InvalidArgument`

#### Scenario: Unknown open option
- **WHEN** a database is opened with `{"bogus": 1}`
- **THEN** the open fails with `InvalidArgument` and no database file exists afterwards

#### Scenario: Reader count
- **WHEN** a database is opened with `{"readers": 2}` and `info` is called
- **THEN** the result has `readers` equal to 2

### Requirement: JSON text rules

Arguments and results SHALL be RFC 8259 JSON text in UTF-8; empty argument text SHALL mean `null` arguments, and text that is not JSON or nests deeper than 128 levels SHALL fail with `InvalidArgument`. A JSON number without fraction or exponent whose value fits a signed or unsigned 64-bit integer SHALL be read as an integer; every other number SHALL be read as the nearest double. Output SHALL print every integer without a fraction or exponent and every double in shortest round-trip form containing a `.` or an exponent, so a JSON parser recovers the same integer or the same double; a non-finite double in a Cypher result SHALL print as `null`. The order of members in an output object SHALL NOT be part of the contract.

#### Scenario: Not JSON
- **WHEN** `info` is called with the argument text `{`
- **THEN** it fails with `InvalidArgument`

#### Scenario: Whole double in a Cypher result
- **WHEN** a Cypher query returns the float `3.0`
- **THEN** the result text prints it as a number containing `.` or `e`, which Python's `json` reads as a `float`

### Requirement: Views select both clocks

Every read SHALL take `view`, an object `{"kind": "now" | "asOf" | "history", "tx", "instant", "validAt"}`, with an absent or `null` view meaning `now` and an absent `kind` meaning `now`. An `asOf` view SHALL carry exactly one of `tx` (a non-negative integer) and `instant` (epoch milliseconds, or an RFC 3339 date or date-time); otherwise, or for an unknown `kind`, the read SHALL fail with `InvalidArgument`. `validAt` SHALL be allowed on any kind and SHALL be the only way to turn on valid-time filtering. A date given as a time SHALL mean midnight UTC of that date.

#### Scenario: As of a transaction
- **WHEN** alice worksAt acme is asserted in transaction 1, superseded in transaction 2 with `validTo` 2024-01-01, and alice worksAt globex is asserted in transaction 3
- **THEN** a SPARQL query on `{"kind": "asOf", "tx": 1}` returns acme only, and on `{"kind": "now"}` returns acme and globex

#### Scenario: Both clocks together
- **WHEN** the same data is queried on `{"kind": "asOf", "tx": 1, "validAt": "2026-01-01"}`, on `{"kind": "now", "validAt": "2026-01-01"}` and on `{"kind": "now", "validAt": "2024-02-01"}`
- **THEN** the results are acme, globex, and nothing

#### Scenario: History keeps retracted rows
- **WHEN** `triples` runs on `{"kind": "history"}` for alice worksAt acme
- **THEN** it returns two rows, one with `retKind` `supersede` and `tRet` 2

#### Scenario: As-of without a selector
- **WHEN** a view has `kind` `asOf` and neither `tx` nor `instant`, or both
- **THEN** the read fails with `InvalidArgument`

### Requirement: Terms are exact in both directions

A term SHALL be a JSON string (a plain string), a boolean, an integer (`xsd:integer`), a non-integer number (`xsd:double`), or an object with one of the keys `iri`, `node`, `bnode`, `stmt`, `tx`, `$int`, or `lex` with an optional `datatype` or `lang`. Output SHALL use the bare JSON form for strings, booleans, integers of magnitude at most 2^53 and finite doubles with a fractional part, `{"$int": "<digits>"}` for larger integers, `{"lex", "lang"}` for language-tagged strings, and `{"lex", "datatype"}` with the canonical lexical form for whole doubles, dates, date-times, decimals and other typed literals. Every output term SHALL be accepted back as input and denote the same term. `null`, a list, or an object of no recognised shape SHALL fail with `InvalidArgument`.

#### Scenario: Integer beyond 2^53
- **WHEN** `{"$int": "9007199254740993"}` is asserted as an object and read back with `triples`
- **THEN** the object is `{"$int": "9007199254740993"}`

#### Scenario: Whole double keeps its datatype
- **WHEN** `{"lex": "3", "datatype": "http://www.w3.org/2001/XMLSchema#double"}` is asserted and read back
- **THEN** it is returned as `{"lex": "3.0E0", "datatype": "http://www.w3.org/2001/XMLSchema#double"}`

#### Scenario: Language-tagged string
- **WHEN** `{"lex": "chat", "lang": "fr"}` is asserted and read back
- **THEN** it is returned as `{"lex": "chat", "lang": "fr"}`

#### Scenario: Not a term
- **WHEN** an assert names `null` or a list as its object
- **THEN** the call fails with `InvalidArgument`

### Requirement: Transactions are op lists with named references

`transact` SHALL take `ops`, a list of op objects, and optional `options` with `dryRun` (boolean) and `maxCascade` (integer), apply the ops in order in one transaction, and return the transaction report (`t`, `instant`, `asserted`, `existing`, `retracted`, `superseded`, `memberships`, `membershipsRetracted`) with `results`, one per op, and `refs`. The op names SHALL be `assert`, `create`, `retract`, `retractMatching`, `supersede`, `confirm`, `meta`, `upsert`, `newNode`, `addToGraph`, `removeFromGraph`, `clearGraph`, `createGraph`, `dropGraph`, `importBundle` and `cypher`. An op that creates a statement or imports a bundle SHALL accept `"as": name`, and a later op in the same list SHALL accept `{"ref": name}` as a statement id, subject or object; `refs` SHALL map each name to its eid (for `importBundle`, the imported root). `validFrom` and `validTo` SHALL accept epoch milliseconds or an RFC 3339 date or date-time. An unknown op, an unknown transaction option, a missing required member or a failing op SHALL fail the call, and then nothing SHALL be committed.

#### Scenario: A layer on a statement from the same transaction
- **WHEN** an assert of alice worksAt acme with `"as": "job"` is followed by an assert whose subject is `{"ref": "job"}`
- **THEN** both are committed in transaction 1 and `refs.job` equals the eid in the first result

#### Scenario: Idempotent assert
- **WHEN** the same assert appears twice in one op list
- **THEN** the second result has `new` false

#### Scenario: Failure commits nothing
- **WHEN** a valid assert is followed by an op named `bogus`
- **THEN** the call fails with `InvalidArgument` and `triples` returns no rows

#### Scenario: Retract cascades to layers
- **WHEN** a statement with a confidence layer is retracted
- **THEN** `retracted` lists the statement as `explicit` and the layer as `cascade`, and `events` holds two retract events

#### Scenario: Retract of an unknown eid
- **WHEN** `retract` names an eid that does not exist
- **THEN** that op's result is `false` and the transaction commits

#### Scenario: Dry run
- **WHEN** a transaction is submitted with `{"dryRun": true}`
- **THEN** the report lists the assert and `triples` afterwards returns no rows

#### Scenario: Import a bundle
- **WHEN** `{"op": "importBundle", "bundle": b, "as": "fact"}` runs with `b` read by `bundle` from another database
- **THEN** the result maps each bundle id to an eid with a `new` flag, and `refs.fact` is the imported root

### Requirement: Speculation keeps nothing

`with` SHALL take `ops` and `queries` (each a read object with its own `op`), apply the ops hypothetically, run every query on the resulting state, return `{"results": [...]}` in query order, and leave the triples and the event log unchanged. If an op or a query fails, the call SHALL fail and still keep nothing.

#### Scenario: What-if
- **WHEN** `with` applies an assert and runs `triples` and an ASK query
- **THEN** both results see the statement, and afterwards `triples` on now and `events` return nothing

### Requirement: Read results

`sparql` SHALL take `text` and an optional boolean `provenance` and return `{"kind": "select", "vars", "rows"}` (each row an object of its bound variables), `{"kind": "ask", "value"}`, `{"kind": "graph", "triples"}` or `{"kind": "update", "report"}`; with `provenance` true a select result SHALL add `provenance`, a list parallel to `rows` of each row's statements as `{"stmt": n}` in ascending order, and any other result kind SHALL fail with `Unsupported`. `cypher` SHALL take `text` and optional `params` and return `{"columns", "rows"}`; a write clause on a read SHALL fail with `Unsupported`. `triples` SHALL take optional `s`, `p`, `o` and return one object per statement with `eid`, `s`, `p`, `o`, `tAdd`, `tRet`, `validFrom`, `validTo` and `retKind`. `events` SHALL take `since` and return `{t, eid, op, kind}` objects. `graphs`, `graphMembers` (`graph`), `values` (`s`, `key`), `dependents` (`eid`, root first) and `bundle` (`eid`, a `tiramemsu-bundle/1` object) SHALL return their lists or object. A read naming a term that is not stored SHALL return an empty result and SHALL NOT fail.

#### Scenario: Unstored term
- **WHEN** `triples` names a subject that was never asserted
- **THEN** it returns `[]`

#### Scenario: Provenance rows
- **WHEN** `sparql` runs `SELECT ?o WHERE { v:a v:p ?o }` with `"provenance": true` where `(v:a v:p v:b)` is statement 1
- **THEN** the result has one row and `"provenance": [[{"stmt": 1}]]`, and without the argument it has no `provenance` member

#### Scenario: Cypher rows
- **WHEN** a Cypher write creates two people linked by KNOWS and a read returns both names
- **THEN** the result has `columns` `["a", "b"]` and one row `["Alice", "Bob"]`

#### Scenario: Dependents and bundle
- **WHEN** a statement with one layer exists and `dependents` and `bundle` are called on its eid
- **THEN** the first returns two eids with the root first, and the second returns an object whose `format` is `tiramemsu-bundle/1` holding two statements

### Requirement: Paths and graphs

`path` SHALL take `start`, `path` text, `mode` (`reach` by default, `trail`, `anyShortest`, `allShortest`), `maxHops`, an optional `graphs` list of terms and an optional `timeRespecting` (`true`, or `{"after": time}`), and return one row per endpoint with `start`, `end`, `hops`, `arrival` (epoch milliseconds, or `null` when the search is not time-respecting or the arrival is unbounded) and `path` (`null` in `reach` mode, otherwise `nodes` and `hops`). With `graphs` the path SHALL be evaluated inside those graphs, a listed term that is not stored naming no graph. An unknown mode or a malformed `graphs` or `timeRespecting` SHALL fail with `InvalidArgument`. The ops `addToGraph`, `removeFromGraph`, `clearGraph`, `createGraph` and `dropGraph` and the reads `graphs` and `graphMembers` SHALL expose named graphs as tags on statements.

#### Scenario: Reachability
- **WHEN** a knows b and b knows c, and `path` runs `knows+` from a
- **THEN** it returns two rows

#### Scenario: Path inside a graph
- **WHEN** a knows b is in graph session12, b knows c is in no graph, and `path` runs `knows+` from a with `"graphs": [session12]`
- **THEN** it returns one row, for b

#### Scenario: Time-respecting path
- **WHEN** a met b valid `[1, 5)` and b met c valid `[3, 9)`, and `path` runs `met+` from a with `"timeRespecting": true`
- **THEN** it returns b with `arrival` 1 and c with `arrival` 3, and with `{"after": 6}` it returns no row

### Requirement: Errors carry a code

Every failure SHALL be `{"code", "message"}`. `code` SHALL be the name of the core error variant (such as `Parse`, `Unsupported`, `NotLive`, `UniqueViolation`, `SubjectTypeMismatch`, `CascadeLimitExceeded`, `PathLimitExceeded`), using the same name as the Rust bridge for every variant both builds share, or `InvalidArgument` when the bridge itself rejected the call. The text form of a failure SHALL be that JSON object.

#### Scenario: Parse error
- **WHEN** `sparql` runs `SELECT ?`
- **THEN** it fails with code `Parse`, and the failure text contains `"code":"Parse"`

#### Scenario: Missing argument
- **WHEN** an `assert` op has no `p` and no `o`
- **THEN** it fails with `InvalidArgument`

#### Scenario: Subject type violation
- **WHEN** `v:confidence` has `sys:subjectType sys:STMT` and a `transact` call asserts `(v:alice v:confidence 0.8)`
- **THEN** it fails with `SubjectTypeMismatch` and nothing from that call is committed

### Requirement: Concurrent calls on one database

Calls on one open database SHALL be allowed from several threads at once. Reads SHALL run in parallel, each on one snapshot that is the state after some committed transaction prefix; write operations SHALL serialize; and a read SHALL never observe part of a transaction.

#### Scenario: Readers during writes
- **WHEN** eight threads repeatedly count statements with `triples` while one thread commits transactions of ten asserts each
- **THEN** every count is a multiple of ten

### Requirement: Conformance with the Rust bridge

For every test of the pinned Rust bridge test suite there SHALL be a case in a language-neutral corpus, and the corpus SHALL be run against the pinned Rust bridge, the Lean bridge and the Lean bridge through the C ABI. Each runner SHALL satisfy the case's expectations, and the Lean and ABI outputs SHALL equal the Rust output after canonicalization: JSON compared structurally with numbers compared by value, the report `instant` and `info.path` ignored, and failures compared by `code` only. A differential fuzzer SHALL compare the two bridges on generated op lists and reads the same way. A missing case or any difference SHALL fail continuous integration.

#### Scenario: A Rust test without a case
- **WHEN** a test name of the pinned Rust bridge test suite has no case in the corpus
- **THEN** the coverage check fails

#### Scenario: Divergent output
- **WHEN** the Lean bridge returns a term in a different form from the Rust bridge for one case
- **THEN** the conformance job fails and names the case and the step

### Requirement: Listed deviations from the Rust bridge

The Lean bridge SHALL differ from the Rust bridge only as listed here, and this list SHALL be published with the packages: error `message` text is not part of the contract, only `code`; the ABI adds the codes `InvalidHandle` and `Internal`; options text that is not JSON fails with `InvalidArgument` in every binding (the Rust Node.js addon threw an error without a code); core error variants that exist only in Rust are never produced.

#### Scenario: Error message wording
- **WHEN** both builds reject the same call
- **THEN** their `code` members are equal, and the conformance check does not compare `message`
