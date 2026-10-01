## Purpose

Lets SPARQL choose transaction time and valid time for a whole request or per group through `tm:` time IRIs in the standard `FROM`, `USING` and `SERVICE` clauses, exactly as the Rust build does, and read statement-time metadata through `tm:` virtual predicates.

## ADDED Requirements

### Requirement: Time IRI grammar

The system SHALL recognise, under `urn:tiramemsu:tm:`, the time IRIs `asOf/<t>` (unsigned decimal transaction number), `asOf/<instant>` (the largest transaction whose instant is at or before it; the empty view if none), `validAt/<instant>` and `history`, where `<instant>` is an `xsd:dateTime` or `xsd:date` lexical form. A date SHALL mean 00:00:00 UTC, a date-time without timezone SHALL be read as UTC, and instants SHALL resolve at millisecond precision. They SHALL be recognised in `FROM`, `FROM NAMED`, `USING`, `USING NAMED` and as the IRI of `SERVICE` and `SERVICE SILENT`. Any other `tm:` IRI in those positions SHALL fail with a `Parse` error of dialect SPARQL naming the IRI and saying it is not a valid time IRI.

#### Scenario: As of a transaction number
- **WHEN** `(v:alice v:worksAt v:acme)` was asserted in tx 3 and retracted in tx 7 and `SELECT ?c FROM <urn:tiramemsu:tm:asOf/5> WHERE { v:alice v:worksAt ?c }` runs on the current view
- **THEN** one row `c = v:acme` is returned

#### Scenario: As of a wall-clock instant with offset
- **WHEN** tx 3 committed at 2026-09-01T10:00:00Z and tx 4 at 2026-09-01T13:00:00Z, and `FROM <urn:tiramemsu:tm:asOf/2026-09-01T14:00:00+02:00>` is used
- **THEN** the query sees the state as of tx 3

#### Scenario: Instant before the first transaction
- **WHEN** `SELECT * FROM <urn:tiramemsu:tm:asOf/1970-01-02> WHERE { ?s ?p ?o }` runs on a database whose first transaction is later
- **THEN** zero rows are returned and no error is raised

#### Scenario: Malformed time IRI
- **WHEN** `SELECT * FROM <urn:tiramemsu:tm:asOf/yesterday> WHERE { ?s ?p ?o }` is submitted
- **THEN** the request fails with a `Parse` error of dialect SPARQL naming `urn:tiramemsu:tm:asOf/yesterday`

### Requirement: Default view without time IRIs

A request with no time IRI SHALL be evaluated in the view it was submitted on; for a plain database handle that is the current state with valid time unfiltered. Valid time SHALL be filtered only when `validAt` is asked for, by the API view or a time IRI.

#### Scenario: Past episodes visible by default
- **WHEN** `(v:alice v:worksAt v:acme)` is live with valid time `[2020-01-01, 2022-01-01)` and `SELECT ?c WHERE { v:alice v:worksAt ?c }` runs on the current view
- **THEN** one row `c = v:acme` is returned

### Requirement: FROM and USING set the request default view

Time IRIs in `FROM` (queries) and `USING` (the `WHERE` of updates) SHALL set the default view of every pattern of the request, including those inside `OPTIONAL`, `UNION`, `MINUS`, `EXISTS` and subqueries. The transaction-time part (`asOf`, `history`) and the valid-time part (`validAt`) SHALL be set independently; a part that is named SHALL override that part of the submitted view, and a part that is not named SHALL be inherited. Two clauses naming the same part with different values SHALL fail with `Unsupported { feature: "conflicting time selectors" }`. A time IRI in `FROM NAMED` or `USING NAMED` SHALL be accepted and have no effect. Time IRIs MAY appear beside graph IRIs in the same clauses.

#### Scenario: Combining asOf and validAt
- **WHEN** `SELECT ?c FROM <urn:tiramemsu:tm:asOf/150> FROM <urn:tiramemsu:tm:validAt/2025-03-01> WHERE { v:alice v:worksAt ?c }` runs
- **THEN** only statements live as of tx 150 whose valid interval contains 2025-03-01T00:00:00Z match

#### Scenario: FROM overrides only the part it names
- **WHEN** a query with `FROM <urn:tiramemsu:tm:asOf/100>` runs on the API view as of tx 200 restricted to valid at 2025-01-01
- **THEN** its patterns read as of tx 100 and valid at 2025-01-01

#### Scenario: Conflicting selectors
- **WHEN** `SELECT * FROM <urn:tiramemsu:tm:asOf/5> FROM <urn:tiramemsu:tm:history> WHERE { ?s ?p ?o }` is submitted
- **THEN** the request fails with `Unsupported { feature: "conflicting time selectors" }`

#### Scenario: FROM reaches EXISTS
- **WHEN** `SELECT ?p FROM <urn:tiramemsu:tm:asOf/5> WHERE { ?p a v:Person FILTER EXISTS { ?p v:worksAt v:acme } }` runs
- **THEN** both the outer pattern and the `EXISTS` pattern read as of tx 5

### Requirement: SERVICE scopes a group in time

`SERVICE <time IRI> { … }` SHALL evaluate every pattern of the group locally, with no federation, in a view derived from the enclosing scope by replacing the part the IRI names and inheriting the other. Groups SHALL nest, innermost winning for the part it names, and SHALL override `FROM`. `SERVICE SILENT` with a time IRI SHALL behave exactly like `SERVICE` and SHALL NOT hide errors. A time `SERVICE` SHALL NOT require a `FROM NAMED` declaration. In the `WHERE` of an update, time `SERVICE` groups SHALL behave as in queries.

#### Scenario: Before and after values of a changed fact
- **WHEN** `(v:alice v:worksAt v:acme)` was live as of tx 150 and later superseded by `(v:alice v:worksAt v:initech)`, and `SELECT ?before ?after WHERE { SERVICE <urn:tiramemsu:tm:asOf/150> { v:alice v:worksAt ?before } v:alice v:worksAt ?after . FILTER(?before != ?after) }` runs
- **THEN** one row `before = v:acme`, `after = v:initech` is returned

#### Scenario: Nested scopes combine parts
- **WHEN** `SELECT ?c WHERE { SERVICE <urn:tiramemsu:tm:asOf/150> { SERVICE <urn:tiramemsu:tm:validAt/2021-06-01> { v:alice v:worksAt ?c } } }` runs
- **THEN** the pattern reads statements live as of tx 150 and valid on 2021-06-01

#### Scenario: Inner scope overrides FROM
- **WHEN** `SELECT ?c FROM <urn:tiramemsu:tm:asOf/10> WHERE { SERVICE <urn:tiramemsu:tm:history> { v:alice v:worksAt ?c } }` runs
- **THEN** the pattern reads every statement ever stored

#### Scenario: SILENT keeps errors
- **WHEN** `SELECT * WHERE { SERVICE SILENT <urn:tiramemsu:tm:asOf/yesterday> { ?s ?p ?o } }` is submitted
- **THEN** the request fails with a `Parse` error naming `urn:tiramemsu:tm:asOf/yesterday`

#### Scenario: Restore a past value through an update
- **WHEN** `(v:alice v:worksAt v:acme)` was live as of tx 150 and has since been retracted, and `INSERT { v:alice v:worksAt ?c } WHERE { SERVICE <urn:tiramemsu:tm:asOf/150> { v:alice v:worksAt ?c } }` is submitted
- **THEN** a new live statement `(v:alice v:worksAt v:acme)` with a new eid is asserted and the old eid stays retracted

### Requirement: GRAPH does not carry time

A `tm:` IRI as the name of a `GRAPH` block, in a query, a `WHERE` pattern, `INSERT DATA`, `DELETE DATA` or a template, SHALL fail before execution with a `Parse` error of dialect SPARQL whose message says time IRIs are not allowed in `GRAPH` and names `SERVICE`. A `GRAPH` block inside a time `SERVICE` group SHALL be read in the group's view, membership and member alike.

#### Scenario: Time IRI in GRAPH
- **WHEN** `SELECT ?c WHERE { GRAPH <urn:tiramemsu:tm:asOf/150> { v:alice v:worksAt ?c } }` is submitted
- **THEN** the request fails with a `Parse` error whose message names `SERVICE`, and nothing is read

#### Scenario: Graph inside a time scope
- **WHEN** `(v:a v:b v:c)` was a member of `<g1>` as of tx 5 and its membership was retracted in tx 6, and `SELECT ?o WHERE { SERVICE <urn:tiramemsu:tm:asOf/5> { GRAPH <g1> { v:a v:b ?o } } }` runs
- **THEN** one row `o = v:c` is returned, and without the `SERVICE` group zero rows

### Requirement: Non-time SERVICE is unsupported

`SERVICE` with an IRI outside `tm:` or with a variable SHALL fail with `Unsupported { feature: "SERVICE" }` before execution, with or without `SILENT`.

#### Scenario: SERVICE variable
- **WHEN** `SELECT * WHERE { SERVICE ?ep { ?s ?p ?o } }` is submitted
- **THEN** the request fails with `Unsupported { feature: "SERVICE" }`

### Requirement: Valid-time filtering is half-open

A `validAt` selector at instant `d` SHALL keep a statement only when its valid start is unbounded or at most `d` and its valid end is unbounded or after `d`. A statement without valid time SHALL be valid at every instant.

#### Scenario: Interval end excluded
- **WHEN** `(v:alice v:worksAt v:acme)` has valid time `[2025-01-01, 2026-03-01)` and `ASK FROM <urn:tiramemsu:tm:validAt/2026-03-01> { v:alice v:worksAt v:acme }` runs
- **THEN** the answer is `false`, and with `validAt/2026-02-28` it is `true`

#### Scenario: Unbounded statements always valid
- **WHEN** `(v:alice v:name "Alice")` has no valid time and `ASK FROM <urn:tiramemsu:tm:validAt/1900-01-01> { v:alice v:name "Alice" }` runs
- **THEN** the answer is `true`

### Requirement: Time IRIs are plain IRIs elsewhere

Outside the dataset clauses and the `SERVICE` IRI, a `tm:` IRI SHALL be an ordinary IRI with no time meaning, in triple patterns, expressions, `BIND`, `VALUES` and templates; the only exception is the `GRAPH` name rule.

#### Scenario: Time IRI as data
- **WHEN** `(v:doc v:ref <urn:tiramemsu:tm:asOf/150>)` was inserted and `SELECT ?x WHERE { v:doc v:ref ?x FILTER(?x = <urn:tiramemsu:tm:asOf/150>) }` runs
- **THEN** one row `x = <urn:tiramemsu:tm:asOf/150>` is returned, evaluated in the current view

### Requirement: Statement-time virtual predicates

With a statement eid as subject, the predicates `tm:txAdded` and `tm:txRetracted` SHALL bind the adding and retracting transactions as `urn:tiramemsu:tx:<t>`; `tm:addedAt` and `tm:retractedAt` SHALL bind the commit instants of those transactions as `xsd:dateTime` with offset `Z`; `tm:validFrom` and `tm:validTo` SHALL bind the valid-interval ends as `xsd:dateTime`; and `tm:retractKind` SHALL bind the retraction kind. They SHALL be computed from the statement, never stored, and read in the pattern's view, so under as of `t` a retraction after `t` is visible as it is in the statement row. An absent value (a live statement's retraction, an unbounded interval end) SHALL produce no solution. A constant object SHALL match by value, and a date-time constant by instant. Transactions bound this way SHALL join with transaction metadata such as `sys:author` and `sys:reason`. These predicates SHALL add no eid to provenance.

#### Scenario: When and by whom a fact was added
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` was added in tx 42 whose metadata has `(tx42 sys:author v:agent7)` and `SELECT ?t ?a WHERE { v:alice v:worksAt v:acme ~ ?r . ?r tm:txAdded ?t . ?t sys:author ?a }` runs
- **THEN** one row `t = <urn:tiramemsu:tx:42>`, `a = v:agent7` is returned

#### Scenario: Live statement has no retraction
- **WHEN** e1 is live and `SELECT ?r ?x WHERE { v:alice v:worksAt v:acme ~ ?r OPTIONAL { ?r tm:txRetracted ?x } }` runs
- **THEN** one row is returned with `x` unbound

#### Scenario: Retraction under history
- **WHEN** e1 was retracted in tx 50 and `SELECT ?x FROM <urn:tiramemsu:tm:history> WHERE { v:alice v:worksAt v:acme ~ ?r . ?r tm:txRetracted ?x }` runs
- **THEN** one row `x = <urn:tiramemsu:tx:50>` is returned

#### Scenario: Learned after it stopped being true
- **WHEN** e1 has valid time `[2020-01-01, 2021-01-01)` and was added by a transaction committed at 2022-05-01T00:00:00Z, and `SELECT ?s WHERE { ?s v:worksAt ?o ~ ?r . ?r tm:addedAt ?a ; tm:validTo ?to FILTER(?a > ?to) }` runs
- **THEN** one row `s = v:alice` is returned, and projecting `?a` gives `"2022-05-01T00:00:00Z"^^xsd:dateTime`

#### Scenario: Valid-from value
- **WHEN** e1 has valid start 2020-01-01T00:00:00Z and `SELECT ?f WHERE { v:alice v:worksAt v:acme ~ ?r . ?r tm:validFrom ?f }` runs
- **THEN** one row `f = "2020-01-01T00:00:00Z"^^xsd:dateTime` is returned
