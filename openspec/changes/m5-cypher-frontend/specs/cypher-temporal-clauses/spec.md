## Purpose

Cypher time syntax for the bitemporal store: `USE AS OF`, `USE VALID AT` and `USE HISTORY` select the transaction-time and valid-time view of a whole query or of one `CALL { }` scope, and statement time metadata is readable as properties, with the same meaning as the SPARQL temporal datasets and the Rust build.

## ADDED Requirements

### Requirement: Default time view
A query without a time clause SHALL evaluate every pattern, property read and label test under the view of its handle; the now view SHALL be transaction time `Now` with valid time unfiltered. Valid-time filtering SHALL never be applied implicitly.

#### Scenario: Past episode visible by default
- **WHEN** `(v:alice v:worksAt v:acme)` is live with valid interval [2020-01-01, 2022-01-01) and `MATCH (a)-[:worksAt]->(c) RETURN c` runs on the now view
- **THEN** `v:acme` is returned

### Requirement: USE AS OF a transaction
`USE AS OF <t>` with an integer literal or Integer parameter SHALL evaluate the scope over statements with `t_add ≤ t` and (`t_ret` null or `t_ret > t`). `t < 1` SHALL give the empty view, and `t` beyond the last transaction SHALL give the latest committed state. A non-integer literal MUST fail with `Parse`, a non-integer parameter with `Eval`.

#### Scenario: Superseded value
- **WHEN** `(v:alice v:worksAt v:acme)` was asserted in tx 3 and superseded in tx 7 by `(v:alice v:worksAt v:globex)`
- **THEN** `` USE AS OF 5 MATCH ({`@id`: 'v:alice'})-[:worksAt]->(c) RETURN c `` returns `v:acme`, and with `USE AS OF 7` returns `v:globex`

#### Scenario: Before the first transaction and parameters
- **WHEN** `USE AS OF 0 MATCH (n) RETURN count(n) AS c` runs, and `USE AS OF $t MATCH (n:Person) RETURN count(n)` runs with `t = 5`
- **THEN** `c` is 0, and the second equals `USE AS OF 5 MATCH (n:Person) RETURN count(n)`

#### Scenario: Float literal
- **WHEN** `USE AS OF 5.5 MATCH (n) RETURN n` is compiled
- **THEN** it fails with a `Parse` error spanning `5.5`

### Requirement: USE AS OF an instant
`USE AS OF <datetime>` with a `datetime(…)` expression or DateTime parameter SHALL resolve, within the query's snapshot, to the largest transaction whose commit instant is at or before the given instant (the offset only locates the instant), then behave as `USE AS OF` that transaction; an instant before every transaction SHALL give the empty view.

#### Scenario: Instant between commits
- **WHEN** tx 3 committed at 2026-09-01T10:00:00Z and tx 4 at 12:00:00Z
- **THEN** `USE AS OF datetime('2026-09-01T11:00:00Z')` and `USE AS OF datetime('2026-09-01T13:00:00+02:00')` both give the results of `USE AS OF 3`

#### Scenario: Instant before any transaction
- **WHEN** `USE AS OF datetime('1999-01-01T00:00:00Z') MATCH (n) RETURN count(n) AS c` runs
- **THEN** `c` is 0

### Requirement: USE VALID AT
`USE VALID AT <instant>` with a `date(…)` or `datetime(…)` expression or a Date or DateTime parameter SHALL keep only statements whose half-open valid interval `[v_from, v_to)` contains the instant, a missing bound meaning unbounded; a date SHALL mean 00:00:00 UTC of that day. Any other argument MUST fail (`Parse` for a literal, `Eval` for a parameter).

#### Scenario: Half-open interval
- **WHEN** `(v:alice v:worksAt v:acme)` is valid over [2025-01-01, 2026-03-01)
- **THEN** `USE VALID AT date('2026-03-01') MATCH (a)-[:worksAt]->(c) RETURN c` returns no rows and the same with `date('2026-02-28')` returns `v:acme`

#### Scenario: Unbounded statement
- **WHEN** a statement has no valid interval
- **THEN** every `USE VALID AT` query that matches it includes it

#### Scenario: Integer argument
- **WHEN** `USE VALID AT 1700000000000 MATCH (n) RETURN n` is compiled
- **THEN** it fails with a `Parse` error

### Requirement: USE HISTORY
`USE HISTORY` SHALL evaluate the scope over every statement ever asserted, live or retracted, each eid once, and property reads SHALL consider all historical values.

#### Scenario: All versions
- **WHEN** alice worked at acme (tx 3 to tx 7) and works at globex (from tx 7), and `` USE HISTORY MATCH ({`@id`: 'v:alice'})-[r:worksAt]->(c) RETURN c, r.txAdded AS added, r.txRetracted AS gone ORDER BY added `` runs
- **THEN** the rows are `(v:acme, 3, 7)` and `(v:globex, 7, null)`

### Requirement: Selector combination and override
A `USE` clause SHALL accept at most one transaction-time selector (`AS OF` or `HISTORY`) optionally followed by `VALID AT`; two transaction-time selectors MUST fail with `Parse`. Each selector given SHALL replace the inherited one (from the handle, or the enclosing scope), and each selector not given SHALL be inherited.

#### Scenario: AS OF with VALID AT
- **WHEN** `USE AS OF 5 VALID AT date('2021-06-01') MATCH (a)-[:worksAt]->(c) RETURN c` runs
- **THEN** only relationships believed at tx 5 and valid on 2021-06-01 are returned

#### Scenario: Conflicting selectors
- **WHEN** `USE AS OF 5 HISTORY MATCH (n) RETURN n` is compiled
- **THEN** it fails with a `Parse` error

#### Scenario: Override of the handle view
- **WHEN** `USE AS OF 7 MATCH (a)-[:worksAt]->(c) RETURN c` runs on the view as of tx 3 restricted to valid time 2021-06-01
- **THEN** the result equals `USE AS OF 7 VALID AT date('2021-06-01') MATCH (a)-[:worksAt]->(c) RETURN c` on the now view

### Requirement: USE placement
A time `USE` clause SHALL be accepted only as the first clause of a query, of a `UNION` branch, or of a `CALL { }` body (after its importing `WITH`, if any). Elsewhere it MUST fail with a `Parse` error spanning it. `USE <graph name>` MUST fail with `Unsupported`.

#### Scenario: USE mid-query
- **WHEN** `MATCH (n) USE AS OF 3 RETURN n` is compiled
- **THEN** it fails with a `Parse` error spanning `USE AS OF 3`

#### Scenario: Graph name
- **WHEN** `USE memory MATCH (n) RETURN n` is compiled
- **THEN** it fails with `Unsupported`

### Requirement: Per-scope time through CALL
A `USE` inside a `CALL { }` body SHALL set the view of every pattern, property read and label test in that body; patterns outside keep the enclosing view, and a nested `CALL` without `USE` inherits its enclosing body's view. Imported variables SHALL keep their identity, and their properties read inside the body SHALL be read under the body's view.

#### Scenario: What changed since tx 150
- **WHEN** alice worked at acme as of tx 150 and at globex now, and `` MATCH (a {`@id`: 'v:alice'})-[:worksAt]->(after) CALL { WITH a USE AS OF 150 MATCH (a)-[:worksAt]->(before) RETURN before } WITH before, after WHERE before <> after RETURN before, after `` runs
- **THEN** one row `(v:acme, v:globex)` is returned

#### Scenario: Property read under the scope's view
- **WHEN** alice's name was "Alicia" as of tx 5 and is "Alice" now, and `` MATCH (a {`@id`: 'v:alice'}) CALL { WITH a USE AS OF 5 RETURN a.name AS old } RETURN a.name AS now, old `` runs
- **THEN** the row is `"Alice", "Alicia"`

#### Scenario: Nested scope inherits
- **WHEN** `CALL { USE AS OF 5 CALL { MATCH (n:Person) RETURN count(n) AS c } RETURN c } RETURN c` runs
- **THEN** `c` is the number of `Person` nodes as of tx 5

### Requirement: Statement time properties
On a relationship or a statement node, `txAdded` and `txRetracted` SHALL be `t_add` and `t_ret` as Integers (`null` while live), `addedAt` and `retractedAt` the commit instants of those transactions as DateTime with offset `Z` (`null` while live), and `validFrom` and `validTo` the valid bounds as DateTime (`null` when unbounded). The CURIE keys `` `tm:txAdded` ``, `` `tm:txRetracted` ``, `` `tm:addedAt` ``, `` `tm:retractedAt` ``, `` `tm:validFrom` ``, `` `tm:validTo` `` SHALL be equivalent, and `` `tm:retractKind` `` SHALL be `"explicit"`, `"cascade"`, `"supersede"`, `"cardinality"` or `null`. On statements these names SHALL denote metadata even when a stored property has the same resolved name, which stays reachable by its CURIE or IRI; on statements neither the metadata nor such a stored property SHALL appear in `keys()` or `properties()`; a relationship property map SHALL test them as metadata. On ordinary nodes they SHALL be ordinary keys.

#### Scenario: Metadata of a live relationship
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` was added in tx 3, committed at 2026-03-10T00:00:00Z, valid from 2025-01-01 unbounded, and `MATCH ()-[r:worksAt]->() RETURN r.txAdded, r.txRetracted, r.addedAt, r.retractedAt, r.validFrom, r.validTo` runs
- **THEN** the row is `3, null, 2026-03-10T00:00:00.000Z, null, 2025-01-01T00:00:00.000Z, null`

#### Scenario: Retraction metadata in history
- **WHEN** e2 was retracted by cascade in a transaction committed at 2026-03-12T00:00:00Z and `` USE HISTORY MATCH ()-[r]->() WHERE r.txRetracted IS NOT NULL RETURN r.retractedAt AS at, r.`tm:retractKind` AS k `` runs
- **THEN** the row for e2 is `2026-03-12T00:00:00.000Z, "cascade"`

#### Scenario: Shadowed stored property and keys
- **WHEN** e1 has `(e1 v:txAdded "custom")` and `(e1 v:confidence 0.9)` and `` MATCH ()-[r:worksAt]->() RETURN r.txAdded, r.`v:txAdded`, keys(r) `` runs
- **THEN** the row is `3, "custom", ["confidence"]`: on a statement neither the metadata nor a stored property under one of the six names is listed

#### Scenario: Ordinary node key
- **WHEN** `(v:alice v:validFrom "someday")` is live and `` MATCH (n {`@id`: 'v:alice'}) RETURN n.validFrom `` runs
- **THEN** the value is `"someday"`

#### Scenario: Learned late
- **WHEN** e3 is valid [2025-01-01, 2025-06-01) and added at 2026-03-10, and `MATCH ()-[r]->() WHERE r.addedAt > r.validTo RETURN r` runs
- **THEN** e3 is returned and statements with a later or `null` `validTo` are not

### Requirement: Time metadata is read-only except valid time
`SET` of `validFrom` or `validTo` on a statement SHALL supersede it with that bound patched (`null` meaning unbounded), and the variable SHALL refer to the new eid for the rest of the query. `SET` or `REMOVE` of `txAdded`, `txRetracted`, `addedAt` or `retractedAt` on a statement MUST fail with `Unsupported`. An empty or inverted interval MUST fail with `InvalidPatch`.

#### Scenario: Close an open interval
- **WHEN** e1 is valid from 2025-01-01, unbounded, and `MATCH ()-[r:worksAt]->() SET r.validTo = date('2026-03-01') RETURN elementId(r) AS id, r.validTo AS t` runs
- **THEN** e1 is retracted with kind `supersede`, a new statement valid over [2025-01-01, 2026-03-01) is live, `id` is its element id, and `t` is 2026-03-01T00:00:00.000Z

#### Scenario: Transaction time is read-only
- **WHEN** `MATCH ()-[r:worksAt]->() SET r.txAdded = 1` or `MATCH ()-[r:worksAt]->() REMOVE r.retractedAt` runs
- **THEN** it fails with `Unsupported` and nothing is written

#### Scenario: Inverted interval
- **WHEN** e1 starts 2025-01-01 and `SET r.validTo = date('2024-01-01')` runs on it
- **THEN** it fails with `InvalidPatch` and nothing changes
