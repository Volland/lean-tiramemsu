## Purpose

Lets applications and agents change the Lean tiramemsu store with SPARQL 1.1 Update text, mapped onto the memory verbs: insert is an idempotent assert, delete is a retraction with cascade and never a physical delete, and one request is one transaction.

## ADDED Requirements

### Requirement: One request is one transaction on the current view

Update text SHALL be accepted only on the plain current view, outside speculative transactions; on any other view it SHALL fail with `Unsupported { feature: "update on a non-current view" }` and change nothing. A request, including several operations separated by `;`, SHALL be exactly one transaction with one transaction number. Operations SHALL run in order, each seeing the effects of the earlier ones. If any operation fails, the request SHALL leave no trace: no transaction row, no statement, no term.

#### Scenario: Multi-operation request
- **WHEN** `INSERT DATA { v:alice v:worksAt v:acme } ; INSERT DATA { v:bob v:worksAt v:acme }` is submitted
- **THEN** both statements are live with the same `t_add`, and the report carries that single transaction number

#### Scenario: Later operation sees an earlier one
- **WHEN** `INSERT DATA { v:alice v:age 41 } ; INSERT { ?p v:adult true } WHERE { ?p v:age ?a FILTER(?a >= 18) }` is submitted
- **THEN** `(v:alice v:adult true)` is live afterwards

#### Scenario: Failure leaves no trace
- **WHEN** a request inserts `(v:x v:p 1)` and a later operation of it violates a `sys:unique` constraint
- **THEN** the request fails with `UniqueViolation`, `(v:x v:p 1)` is not stored, and no transaction number is consumed

#### Scenario: Historical view rejected
- **WHEN** `INSERT DATA { v:a v:b v:c }` is submitted on the view as of tx 5
- **THEN** the request fails with `Unsupported { feature: "update on a non-current view" }` and nothing is written

### Requirement: Update report

A successful request SHALL return the transaction report: the transaction number, its instant, the newly asserted eids, the eids that already existed for idempotent inserts, every retracted eid with its kind (explicit, cascade, cardinality), and the asserted and retracted graph memberships listed apart from statements. A request that changes nothing SHALL still commit a transaction and return its report.

#### Scenario: New and existing eids
- **WHEN** `(v:alice v:worksAt v:acme)` is live as e1 and `INSERT DATA { v:alice v:worksAt v:acme . v:alice v:age 41 }` is submitted
- **THEN** the report lists e1 as existing, one new eid as asserted and nothing as retracted

#### Scenario: No-op request commits
- **WHEN** `DELETE DATA { v:nobody v:knows v:noone }` is submitted and no such triple is live
- **THEN** the request succeeds, allocates a new transaction number, and the report lists nothing

### Requirement: INSERT DATA asserts idempotently

Each ground triple of `INSERT DATA` SHALL be asserted with the idempotent assert verb and an unbounded valid time; a live statement with the same `(s, p, o)` SHALL be reported as existing and not duplicated. Blank nodes SHALL become new blank nodes, one per distinct label per request. Literals SHALL be stored in canonical form.

#### Scenario: Repeated insert
- **WHEN** `INSERT DATA { v:alice v:worksAt v:acme }` is submitted twice
- **THEN** exactly one live statement with that content exists, and the second report lists its eid as existing

#### Scenario: Blank nodes are fresh per request
- **WHEN** `INSERT DATA { _:b v:name "anon" }` is submitted twice
- **THEN** two distinct blank nodes each have a live `v:name "anon"` statement

#### Scenario: Canonical literal stored
- **WHEN** `INSERT DATA { v:alice v:age "041"^^xsd:integer }` is submitted and `SELECT ?a WHERE { v:alice v:age ?a }` runs
- **THEN** the query returns `"41"^^xsd:integer`

#### Scenario: Machine-checked idempotent insert
- **WHEN** the proofs library builds
- **THEN** the property that running a ground `INSERT DATA` without blank nodes a second time in a row asserts no new statement holds as a theorem whose axioms satisfy the proof policy

### Requirement: DELETE DATA retracts with cascade

Each ground triple of `DELETE DATA` SHALL retract every live statement with that `(s, p, o)`, whatever its valid time, with kind explicit, and the retraction SHALL cascade to every live statement whose subject or object is a retracted eid, recursively, with kind cascade, in the same transaction. Deleting a triple that is not live SHALL be a no-op. Retracted statements SHALL stay visible to historical views.

#### Scenario: All episodes retracted
- **WHEN** `(v:alice v:worksAt v:acme)` is live as two eids with different valid times and `DELETE DATA { v:alice v:worksAt v:acme }` is submitted
- **THEN** both eids are retracted in the same transaction with kind explicit

#### Scenario: Cascade to annotations
- **WHEN** `e1 = (v:alice v:worksAt v:acme)` carries `e2 = (e1 v:confidence 0.8)` and the same `DELETE DATA` is submitted
- **THEN** e1 is retracted with kind explicit and e2 with kind cascade, both with the same `t_ret`, and the view as of the previous transaction still shows both

#### Scenario: Unrelated triples survive
- **WHEN** `(v:alice v:age 41)` is also live
- **THEN** it stays live after the same `DELETE DATA`

#### Scenario: Machine-checked cascade
- **WHEN** the proofs library builds
- **THEN** the property that the eids retracted by `DELETE DATA` equal the dependents closure of the live eids of its triples holds as a theorem whose axioms satisfy the proof policy

### Requirement: Updates never delete rows

No SPARQL update, including `DELETE`, `CLEAR` and `DROP`, SHALL remove a stored row or change any column of a stored statement other than setting its retraction once. Every change SHALL be made through the memory verbs.

#### Scenario: Deleted fact remains in history
- **WHEN** `(v:alice v:worksAt v:acme)` is deleted by `DELETE WHERE { v:alice v:worksAt ?c }` and `SELECT ?c FROM <urn:tiramemsu:tm:history> WHERE { v:alice v:worksAt ?c }` runs
- **THEN** one row `c = v:acme` is returned

#### Scenario: Machine-checked never forget
- **WHEN** the proofs library builds
- **THEN** the property that a successful update request only appends rows and sets the retraction of live rows once holds as a theorem whose axioms satisfy the proof policy

### Requirement: DELETE/INSERT WHERE

For `DELETE … INSERT … WHERE`, `INSERT … WHERE`, `DELETE … WHERE` and `DELETE WHERE { … }`, the system SHALL evaluate the `WHERE` pattern once against the state before the operation, then instantiate the delete template for every solution and retract as `DELETE DATA` does, then instantiate the insert template for every solution and assert as `INSERT DATA` does. Template triples with an unbound variable or a term invalid in its position SHALL be skipped for that solution. Insert-template blank nodes SHALL be fresh per solution.

#### Scenario: Replace a value
- **WHEN** `(v:alice v:worksAt v:acme)` is live and `DELETE { v:alice v:worksAt ?c } INSERT { v:alice v:worksAt v:initech } WHERE { v:alice v:worksAt ?c }` is submitted
- **THEN** the old statement is retracted and `(v:alice v:worksAt v:initech)` is live, both in the reported transaction

#### Scenario: WHERE evaluated before changes
- **WHEN** `(v:a v:next v:b)` and `(v:b v:next v:c)` are live and `DELETE { ?x v:next ?y } INSERT { ?y v:prev ?x } WHERE { ?x v:next ?y }` is submitted
- **THEN** both `v:next` statements are retracted and `(v:b v:prev v:a)` and `(v:c v:prev v:b)` are live

#### Scenario: Unbound template variable skipped
- **WHEN** `INSERT { ?p v:ageCopy ?a } WHERE { ?p v:name ?n OPTIONAL { ?p v:age ?a } }` runs over a person without an age
- **THEN** nothing is asserted for that person and the request succeeds

#### Scenario: Fresh blank node per solution
- **WHEN** `INSERT { ?p v:card _:c . _:c v:owner ?p } WHERE { ?p a v:Person }` runs over two persons
- **THEN** two distinct blank nodes are created

### Requirement: Store constraints and reserved predicates

Every assert and retract made by an update SHALL pass the same checks as the Lean API: predicate schema (`sys:valueType`, `sys:subjectType`, `sys:unique`, `sys:cardinality`), the reserved `sys:` and `tm:` namespaces, the self-reference rule and the cascade limit, failing the whole request with the same typed error. Schema flags, vocabulary and prefix settings SHALL be insertable. Asserting a triple whose predicate is a virtual predicate (`tm:txAdded`, `tm:txRetracted`, `tm:addedAt`, `tm:retractedAt`, `tm:validFrom`, `tm:validTo`, `tm:retractKind`, `sys:subject`, `sys:object`, `sys:predicate`) or `sys:inGraph` SHALL fail with `ReservedNamespace` naming it. Updates SHALL always assert with unbounded valid time.

#### Scenario: Cardinality one replaces
- **WHEN** `v:age` has `sys:cardinality sys:one`, `(v:alice v:age 41)` is live and `INSERT DATA { v:alice v:age 42 }` is submitted
- **THEN** `(v:alice v:age 42)` is live and the old statement is retracted with kind cardinality in the same transaction

#### Scenario: Unique violation aborts
- **WHEN** `v:email` has `sys:unique true`, `(v:alice v:email "a@x.org")` is live and `INSERT DATA { v:bob v:email "a@x.org" }` is submitted
- **THEN** the request fails with `UniqueViolation` and nothing is written

#### Scenario: Valid time cannot be written
- **WHEN** `INSERT { ?r tm:validFrom "2020-01-01T00:00:00Z"^^xsd:dateTime } WHERE { v:alice v:worksAt v:acme ~ ?r }` is submitted
- **THEN** the request fails with `ReservedNamespace` naming `urn:tiramemsu:tm:validFrom` and nothing is written

#### Scenario: Membership predicate is engine-owned
- **WHEN** `INSERT DATA { v:x sys:inGraph v:g }` is submitted
- **THEN** the request fails with `ReservedNamespace` naming `urn:tiramemsu:sys:inGraph`

### Requirement: Graph updates write membership statements

A `GRAPH <g>` block in `INSERT DATA` or an insert template SHALL assert each triple idempotently and assert its membership `(e sys:inGraph g)` idempotently with unbounded valid time; a triple already live keeps its eid and gains at most one membership. A `GRAPH <g>` block in `DELETE DATA` or a delete template SHALL retract only the membership, never the statement, and SHALL be a no-op for a non-member. A delete without `GRAPH` SHALL retract the statement, whose memberships go by cascade. `WITH <g>` SHALL name the graph of template triples outside their own `GRAPH` block and scope the `WHERE` default graph to `g`. `USING` and `USING NAMED` SHALL mean for `WHERE` what `FROM` and `FROM NAMED` mean for queries. A variable graph name in a template SHALL be allowed only when `WHERE` binds it. Statements whose predicate is in `sys:` SHALL NOT become graph members (`ReservedNamespace`). Invalid graph names SHALL fail as they do in queries.

#### Scenario: Insert into a graph
- **WHEN** `INSERT DATA { GRAPH <g1> { v:a v:b v:c } }` and then `INSERT DATA { GRAPH <g2> { v:a v:b v:c } }` are submitted
- **THEN** exactly one live statement `(v:a v:b v:c)` exists with two live memberships, in `g1` and `g2`

#### Scenario: Delete from a graph keeps the statement
- **WHEN** `(v:a v:b v:c)` is in `<g1>` and `DELETE DATA { GRAPH <g1> { v:a v:b v:c } }` is submitted
- **THEN** the membership is retracted, the statement stays live, and the report lists the membership as retracted

#### Scenario: WITH scopes templates and WHERE
- **WHEN** `(v:a v:b v:c)` is in `<g1>`, `(v:d v:e v:f)` is in no graph, and `WITH <g1> DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }` is submitted
- **THEN** the membership of `(v:a v:b v:c)` in `g1` is retracted, both statements stay live, and `(v:d v:e v:f)` is untouched

### Requirement: Graph management operations

`CREATE GRAPH <g>` SHALL assert `(g rdf:type sys:Graph)` and fail with `GraphExists` when already declared. `CLEAR GRAPH <g>` and `CLEAR NAMED` SHALL retract every live membership in that graph or in every graph, and no member statement. `DROP GRAPH <g>` and `DROP NAMED` SHALL do the same and also retract the declaration, leaving other triples about `g` live. Without `SILENT`, `CLEAR GRAPH` and `DROP GRAPH` on a graph with neither a live membership nor a declaration SHALL fail with `GraphNotFound`; with `SILENT` they SHALL be no-ops. `LOAD`, `ADD`, `MOVE`, `COPY`, `CLEAR DEFAULT`, `CLEAR ALL`, `DROP DEFAULT` and `DROP ALL` SHALL fail with `Unsupported` naming the operation (for example `"CLEAR DEFAULT"`, `"DROP ALL"`), with or without `SILENT`, before anything in the request is written.

#### Scenario: CLEAR keeps the statements
- **WHEN** `(v:a v:b v:c)` is in `<g1>` and `CLEAR GRAPH <g1>` is submitted
- **THEN** the membership is retracted and `(v:a v:b v:c)` stays live

#### Scenario: DROP SILENT ALL still rejected
- **WHEN** `DROP SILENT ALL` is submitted
- **THEN** the request fails with `Unsupported { feature: "DROP ALL" }`

#### Scenario: Rejected operation aborts the request
- **WHEN** `INSERT DATA { v:a v:b v:c } ; LOAD <http://example.org/data.ttl>` is submitted
- **THEN** the request fails with `Unsupported { feature: "LOAD" }` and `(v:a v:b v:c)` is not stored

### Requirement: Update parse errors

Update text that is not valid SPARQL 1.1 Update with SPARQL 1.2 syntax SHALL fail with a `Parse` error of dialect SPARQL carrying line, column and byte offset, and nothing SHALL be written. Variables in `INSERT DATA`, and variables or blank nodes in `DELETE DATA` or `DELETE WHERE`, SHALL be parse errors.

#### Scenario: Variable in INSERT DATA
- **WHEN** `INSERT DATA { ?s v:p 1 }` is submitted
- **THEN** the request fails with a `Parse` error of dialect SPARQL and nothing is written

#### Scenario: Blank node in DELETE DATA
- **WHEN** `DELETE DATA { _:b v:p 1 }` is submitted
- **THEN** the request fails with a `Parse` error of dialect SPARQL and nothing is written
