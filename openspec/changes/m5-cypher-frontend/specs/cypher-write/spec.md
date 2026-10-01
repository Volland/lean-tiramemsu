## Purpose

Cypher write clauses on tiramemsu: each clause becomes memory verbs (create, assert, upsert, supersede, retract with cascade) inside one atomic transaction, so Cypher writes never forget and leave the same statements, transaction rows and reports as the pinned Rust build.

## ADDED Requirements

### Requirement: Write entry points and atomicity
The system SHALL run a Cypher query that contains write clauses through a transaction handle, and through a database-level call that opens exactly one transaction for it. The query SHALL run as one transaction with one transaction number on the single writer, and SHALL return its `RETURN` rows together with the transaction report (asserted, existing, retracted and superseded eids). Clauses SHALL apply in order, each seeing the effects of earlier ones. If any clause fails, the query MUST fail and its transaction MUST leave no tx row, statement, term or volatile change. No write clause SHALL physically delete a row: every removal is a retraction, visible to time-travel reads.

#### Scenario: Create and return
- **WHEN** `CREATE (n:Person {name: 'Bob'}) RETURN n.name AS name` runs through the database-level call
- **THEN** the result is one row `"Bob"`, and the report lists two asserted eids (the `rdf:type` and `v:name` statements) under one transaction number

#### Scenario: Later clauses see earlier writes
- **WHEN** `CREATE (n:Temp {k: 1}) WITH n MATCH (m:Temp) RETURN count(m) AS c` runs on a store without `Temp` nodes
- **THEN** `c` is 1

#### Scenario: Failure leaves no trace
- **WHEN** `v:email` is `sys:unique`, `(v:alice v:email "a@x")` is live, and `CREATE (n:Person {name: 'Eve'}) CREATE (m {email: 'a@x'})` runs
- **THEN** the query fails with `UniqueViolation`, no `Eve` node exists, and the last transaction number is unchanged

#### Scenario: Composes with API operations
- **WHEN** one caller transaction asserts `(v:alice v:age 42)` through the API and then runs `MATCH (n) WHERE n.age = 42 SET n:Adult` through its transaction handle
- **THEN** both changes commit under the same transaction number

### Requirement: CREATE nodes
`CREATE` of a node pattern SHALL allocate a new anonymous node id, assert one `rdf:type` statement per label and one statement per inline property, and bind the variable to the node. A property map with `` `@id` `` SHALL use that identity instead and assert labels and properties on it idempotently; no `@id` statement SHALL be written. A node created with no label, property or relationship SHALL be returned but SHALL write nothing, so later queries do not see it.

#### Scenario: Anonymous node
- **WHEN** `CREATE (n:Person {name: 'Bob', age: 30}) RETURN elementId(n) AS id` runs
- **THEN** `id` is `urn:tiramemsu:node:<k>` for a new `k`, and exactly the statements `rdf:type v:Person`, `v:name "Bob"`, `v:age 30` with that subject are live

#### Scenario: Explicit identity
- **WHEN** `` CREATE (n:Person {`@id`: 'v:carol', name: 'Carol'}) `` runs
- **THEN** `(v:carol rdf:type v:Person)` and `(v:carol v:name "Carol")` are live and no statement has predicate `@id`

#### Scenario: Empty node writes nothing
- **WHEN** `CREATE (n) RETURN n` runs on an empty store, then `MATCH (n) RETURN count(n) AS c`
- **THEN** the first returns one node with no asserted eid in the report, and `c` is 0

### Requirement: CREATE relationships
`CREATE` of a relationship SHALL always create a new statement with a new eid, even when an identical live statement exists. Inline relationship properties SHALL be asserted as statements whose subject is the new eid, except that `validFrom` and `validTo` SHALL set the valid-time interval of the new statement and MUST be Date or DateTime values. A path pattern SHALL create every node and relationship in it. A variable-length relationship in `CREATE` MUST fail with `Unsupported`.

#### Scenario: Parallel relationships
- **WHEN** `MATCH (a {name:'Alice'}), (b {name:'Bob'}) CREATE (a)-[:CALLED]->(b)` runs twice
- **THEN** two live `CALLED` statements from Alice to Bob exist with different eids

#### Scenario: Properties become layer statements
- **WHEN** `MATCH (a {name:'Alice'}), (c {name:'Acme'}) CREATE (a)-[r:worksAt {confidence: 0.8}]->(c)` runs and the new eid is e
- **THEN** `(e v:confidence 0.8)` is live

#### Scenario: Valid time on creation
- **WHEN** `CREATE (a)-[r:worksAt {validFrom: date('2025-01-01')}]->(c) RETURN r.validFrom AS f` runs for bound `a` and `c`
- **THEN** `f` is DateTime 2025-01-01T00:00:00.000Z, the statement's valid interval starts at that instant, and no `v:validFrom` statement exists

### Requirement: Value encoding on write
Written Cypher values SHALL be encoded canonically: Integer inline when it fits the inline integer range, otherwise as an `xsd:integer` literal; Float as a double; String as a string; Boolean as a boolean; Date as a date; DateTime as an `xsd:dateTime` keeping its offset (a named zone becomes its offset at that instant; offsets are never normalised to UTC); LocalDateTime as an `xsd:dateTime` without timezone. A list SHALL write one statement per distinct element. `null` and `[]` SHALL write nothing. A map, node, relationship or path value, or a list containing `null` or a list, MUST fail with `Eval`.

#### Scenario: List property
- **WHEN** `CREATE (n:Doc {tags: ['a', 'b']}) RETURN n.tags AS t` runs
- **THEN** `v:tags "a"` and `v:tags "b"` are live for the node and `t` is `["a", "b"]`

#### Scenario: Map value rejected
- **WHEN** `CREATE (n {meta: {x: 1}})` runs
- **THEN** it fails with `Eval` and nothing is written

#### Scenario: Offsets and named zones
- **WHEN** `CREATE (n {a: datetime('2025-03-01T10:00:00+02:00'), b: datetime('2025-07-01T09:00:00[Europe/Kyiv]'), c: localdatetime('2025-03-01T10:00:00')})` runs
- **THEN** the stored objects are `"2025-03-01T10:00:00+02:00"^^xsd:dateTime`, `"2025-07-01T09:00:00+03:00"^^xsd:dateTime` and `"2025-03-01T10:00:00"^^xsd:dateTime`

### Requirement: MERGE with a unique key
When a `MERGE` node pattern's property map has a key whose predicate is `sys:unique true`, the system SHALL upsert by the first such key in map order: bind the live subject with that value if one exists, otherwise create an anonymous node and assert the key statement. It SHALL then assert the pattern's labels and remaining properties idempotently. `ON CREATE SET` SHALL apply only when the node was created and `ON MATCH SET` only when it existed.

#### Scenario: Upsert creates, then matches
- **WHEN** `v:email` is `sys:unique` and `MERGE (n:Person {email: 'a@x'}) ON CREATE SET n.created = true ON MATCH SET n.seen = true RETURN n` runs twice
- **THEN** the first run creates a node with `v:created true`, the second returns the same node with `v:seen true`, and the second report lists the email statement as existing

#### Scenario: Existing subject gains the label
- **WHEN** `(v:alice v:email "al@x")` is live with no label and `MERGE (n:Person {email: 'al@x'}) RETURN n` runs
- **THEN** `v:alice` is returned and `(v:alice rdf:type v:Person)` becomes live

### Requirement: MERGE by pattern
Without a unique key, `MERGE` SHALL match the whole pattern against the transaction's current state: with matches it SHALL bind one row per match, otherwise it SHALL create the whole pattern as `CREATE` does and bind one row. The match-or-create SHALL be atomic with respect to other writers. A `null` property value in the pattern MUST fail with `Eval`; a `MERGE` relationship MUST have exactly one type.

#### Scenario: Merge twice
- **WHEN** `v:name` is not unique and `MERGE (n:City {name: 'Lviv'})` runs twice
- **THEN** exactly one `City` named `"Lviv"` exists

#### Scenario: Merge a relationship
- **WHEN** `MATCH (a {name:'Alice'}), (b {name:'Bob'}) MERGE (a)-[r:knows]->(b) RETURN r` runs twice
- **THEN** one live `knows` statement from Alice to Bob exists and both runs return its eid

#### Scenario: Concurrent merges
- **WHEN** two threads run `MERGE (n:City {name: 'Kyiv'})` on the same database at once
- **THEN** exactly one such node exists after both commit

### Requirement: SET property
`SET x.key = value` on a node, relationship or statement node SHALL consider the live property statements of `x` for the key at transaction time `Now`, ignoring valid time, and apply the first matching rule: (1) `null` or `[]`: retract them all; (2) a list: retract those whose object is not in the list and assert each element; (3) none exist: assert; (4) one has the value: keep it and retract the others; (5) the predicate is `sys:cardinality sys:one`: assert, replacing old values without carrying their annotations; (6) exactly one exists: supersede it with the new object, replaying its annotations; (7) otherwise: retract all and assert. Values that denote the same instant with different offsets SHALL be different values here.

#### Scenario: Same value is a no-op
- **WHEN** `(v:alice v:age 42)` is live as e5 and `MATCH (n {name:'Alice'}) SET n.age = 42` runs
- **THEN** e5 is still live and reported as existing, and nothing is retracted

#### Scenario: Change supersedes and keeps annotations
- **WHEN** e5 = `(v:alice v:title "Dr")` has `(e5 v:source "cv")` and `SET n.title = 'Prof'` runs for alice
- **THEN** e5 and its annotation are retracted with kind `supersede`, and a new e9 = `(v:alice v:title "Prof")` is live with `(e9 v:source "cv")` and `(e9 sys:supersedes e5)`

#### Scenario: Cardinality one drops annotations
- **WHEN** `v:age` is `sys:one`, `(v:alice v:age 41)` has an annotation, and `SET n.age = 42` runs for alice
- **THEN** the old statement and annotation are retracted with kind `cardinality`, and the new statement has no annotation

#### Scenario: Several values replaced
- **WHEN** alice has `v:nick "al"` and `v:nick "ally"` and `SET n.nick = 'ali'` runs
- **THEN** both are retracted with kind `explicit` and only `v:nick "ali"` is live

#### Scenario: Null removes
- **WHEN** `MATCH (n {name:'Alice'}) SET n.age = null` runs
- **THEN** no live `v:age` statement of `v:alice` remains

#### Scenario: Same instant, other offset
- **WHEN** `(v:m v:at "2026-03-01T12:00:00+02:00"^^xsd:dateTime)` is live and `` MATCH (n {`@id`: 'v:m'}) SET n.at = datetime('2026-03-01T10:00:00Z') `` runs
- **THEN** the statement is superseded, and `n.at` reads back as DateTime 2026-03-01T10:00:00.000Z

### Requirement: SET and REMOVE with maps and labels
`SET x += map` SHALL apply `SET x.k = v` per entry. `SET x = map` SHALL do the same and also retract every live non-`sys:` property statement of `x` whose key is not in the map. `SET n:A:B` SHALL assert each label idempotently, and `REMOVE n:A` SHALL retract every live `(n rdf:type A)`. `REMOVE x.key` SHALL retract every live property statement of `x` for the key with cascade. `SET x = <node or relationship>` MUST fail with `Unsupported`. Cypher writes SHALL never write volatile values.

#### Scenario: Merge and replace properties
- **WHEN** alice has name "Alice" and age 41, `SET n += {age: 42, city: 'Lviv'}` runs, and then `SET n = {name: 'Alicia'}` runs
- **THEN** after the first, name, age 42 and city are live; after the second only `v:name "Alicia"` remains among her properties, with labels and relationships unchanged

#### Scenario: Labels
- **WHEN** `MATCH (n {name:'Alice'}) SET n:Admin REMOVE n:Person RETURN labels(n) AS l` runs on a `Person`
- **THEN** `l` is `["Admin"]`

#### Scenario: REMOVE cascades
- **WHEN** e5 = `(v:alice v:age 42)` has `(e5 v:source "form")` and `REMOVE n.age` runs for alice
- **THEN** e5 is retracted with kind `explicit` and the annotation with kind `cascade` in the same transaction

#### Scenario: SET writes a statement, not volatile
- **WHEN** volatile `(v:alice, v:lastSeen)` exists and `SET n.lastSeen = datetime('2026-10-01T00:00:00Z')` runs for alice
- **THEN** a `v:lastSeen` statement is asserted and the volatile entry is unchanged

### Requirement: DELETE relationships and statements
`DELETE r` for a relationship, or a statement in node form, SHALL retract that statement with cascade. Deleting a retracted statement, a variable deleted earlier in the same query, or `null` SHALL be a no-op.

#### Scenario: Delete a relationship
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` has e2 = `(e1 v:confidence 0.8)` and `MATCH (:Person {name:'Alice'})-[r:worksAt]->() DELETE r` runs in tx t
- **THEN** e1 is retracted with kind `explicit` and e2 with kind `cascade`, both at t, and a query as of t−1 still returns the relationship and its confidence

#### Scenario: Delete null
- **WHEN** `OPTIONAL MATCH (n:Nobody) DELETE n` runs
- **THEN** it succeeds and retracts nothing

### Requirement: DELETE nodes
`DELETE n` for a node SHALL retract, with cascade, every live statement with subject `n` that is presented as a property or label. Before commit, if a live statement presented as a relationship still has `n` as subject or object, the query MUST fail with `DeleteConnectedNode` naming the node and listing those eids, leaving no trace; relationships deleted by the same query SHALL NOT count. `DETACH DELETE n` SHALL retract, with cascade, every live statement whose subject or object is `n`, and SHALL never fail for connected relationships.

#### Scenario: Connected node
- **WHEN** `v:alice` has a live `worksAt` relationship and `MATCH (n {name:'Alice'}) DELETE n` runs
- **THEN** it fails with `DeleteConnectedNode` naming `v:alice` and listing the `worksAt` eid, and her name is still live

#### Scenario: Relationships deleted in the same query
- **WHEN** `MATCH (n {name:'Alice'})-[r]-() DELETE r, n` runs
- **THEN** it succeeds and every property, label and relationship of `v:alice` is retracted

#### Scenario: Detach delete
- **WHEN** `v:alice` has a label, a name, e1 = `(v:alice v:worksAt v:acme)` with `(e1 v:confidence 0.8)` and `(v:bob v:knows v:alice)`, and `MATCH (n {name:'Alice'}) DETACH DELETE n` runs
- **THEN** all five statements are retracted in one transaction, and `v:acme` and `v:bob` keep their other statements

### Requirement: Schema and namespace checks
Every statement written by a Cypher clause SHALL pass the same checks as the API: `sys:valueType`, `sys:unique`, `sys:cardinality`, the reserved-namespace rule and the cascade limit. A violation MUST fail the query with `ValueTypeMismatch`, `UniqueViolation`, `ReservedNamespace` or `CascadeLimitExceeded`, leaving no trace.

#### Scenario: valueType mismatch
- **WHEN** `v:age` has `sys:valueType xsd:integer` and `CREATE (n {age: 'old'})` runs
- **THEN** it fails with `ValueTypeMismatch`

#### Scenario: Reserved predicate
- **WHEN** `` MATCH (n {name:'Alice'}) SET n.`sys:reason` = 'x' `` runs
- **THEN** it fails with `ReservedNamespace`

#### Scenario: Cascade limit
- **WHEN** a `DETACH DELETE` would cascade more statements than the transaction's cascade limit
- **THEN** it fails with `CascadeLimitExceeded` and the store is unchanged

### Requirement: Writes and time clauses
Writes SHALL apply to the current state. A write query whose top-level time clause selects anything but transaction time `Now` with unfiltered valid time MUST fail with `Unsupported` before execution. Historical `CALL { USE … }` reads inside a write query SHALL be allowed; writing to a statement bound from a historical scope SHALL follow the verb rules (retracting a retracted statement is a no-op, superseding it fails with `NotLive`).

#### Scenario: Top-level AS OF with a write
- **WHEN** `USE AS OF 5 MATCH (n) SET n.x = 1` runs through a transaction handle
- **THEN** it fails with `Unsupported`

#### Scenario: Restore a past value
- **WHEN** alice's title was "Dr" as of tx 5 and is "Prof" now, and `` CALL { USE AS OF 5 MATCH (a {`@id`: 'v:alice'}) RETURN a.title AS old } MATCH (n {`@id`: 'v:alice'}) SET n.title = old `` runs
- **THEN** alice's live title is "Dr"

### Requirement: Unsupported write features
`FOREACH`, `CALL { … } IN TRANSACTIONS`, dynamic labels or keys in write clauses, and write clauses inside `EXISTS { }` MUST fail with `Unsupported` before execution.

#### Scenario: FOREACH in a write query
- **WHEN** `MATCH (n) FOREACH (x IN [1,2] | CREATE (:T {v: x}))` runs through a transaction handle
- **THEN** it fails with `Unsupported` naming `FOREACH`, and nothing is written
