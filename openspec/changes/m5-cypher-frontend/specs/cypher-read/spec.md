## Purpose

Read-only Cypher over the tiramemsu statement store: which openCypher constructs are accepted, what they mean on the property-graph projection of bitemporal statements, how values are returned, and how invalid or unsupported input fails. Results equal those of the pinned Rust build on the same file.

## ADDED Requirements

### Requirement: Read entry point and result table
The system SHALL run a Cypher query with a parameter map on a view handle and return a table of ordered column names and rows of Cypher values. Every pattern SHALL be evaluated under the handle's time selection unless a time clause overrides it. A query run on a view handle that contains `CREATE`, `MERGE`, `SET`, `REMOVE`, `DELETE` or `DETACH DELETE` MUST fail with `Unsupported` naming that clause before anything executes.

#### Scenario: Read on the now view
- **WHEN** `(v:alice rdf:type v:Person)` and `(v:alice v:name "Alice")` are live and `MATCH (p:Person) RETURN p.name AS name` runs on the now view
- **THEN** the result has the single column `name` and the single row `["Alice"]`

#### Scenario: Write clause on a view handle
- **WHEN** `CREATE (n:Person {name: 'Bob'})` runs on a view handle
- **THEN** it fails with `Unsupported` naming `CREATE`, and the last transaction number is unchanged

#### Scenario: Handle view is the default
- **WHEN** `(v:alice v:name "Alice")` was asserted in tx 1 and retracted in tx 2, and `MATCH (n) WHERE n.name = 'Alice' RETURN n` runs on the view as of tx 1 and on the now view
- **THEN** the as-of run returns one row and the now run returns none

### Requirement: Property-graph projection of statements
Each visible statement SHALL be presented either as a property of its subject or as a relationship. A literal object SHALL make a property; an IRI, anonymous node, blank node or statement object SHALL make a relationship. A predicate with a visible `sys:isEdge true` SHALL always be a relationship and one with `sys:isEdge false` SHALL always be a property, the flag read in the view of the pattern being matched. `rdf:type` statements SHALL be presented only as labels.

#### Scenario: Literal object is a property
- **WHEN** only `(v:alice v:age 42)` is stored and `MATCH ()-[r]->() RETURN count(r) AS c` runs
- **THEN** `c` is 0, and `MATCH (a) RETURN a.age` returns 42

#### Scenario: Node object is a relationship
- **WHEN** `(v:alice v:knows v:bob)` is stored and `MATCH (a) WHERE a.knows IS NOT NULL RETURN a` runs
- **THEN** zero rows are returned, and `MATCH (a)-[:knows]->(b) RETURN b` returns `v:bob`

#### Scenario: isEdge true on a literal
- **WHEN** `(v:tag sys:isEdge true)` and `(v:alice v:tag "urgent")` are live and `MATCH (a)-[:tag]->(t) RETURN t, a.tag` runs
- **THEN** one row has `t = "urgent"` and `a.tag = null`

#### Scenario: isEdge false on an IRI
- **WHEN** `(v:homepage sys:isEdge false)` and `(v:alice v:homepage <https://alice.example/>)` are live
- **THEN** `a.homepage` for `v:alice` is the string `"https://alice.example/"`, and `MATCH ()-[r:homepage]->() RETURN r` returns zero rows

#### Scenario: rdf:type is never a relationship
- **WHEN** only `(v:alice rdf:type v:Person)` is stored and `MATCH ()-[r]->() RETURN r` runs
- **THEN** zero rows are returned

### Requirement: Node patterns and labels
A node pattern SHALL match IRIs, anonymous nodes and blank nodes that are the subject of a visible statement or the object of a visible relationship. An unlabelled, unconstrained node pattern MUST NOT match statements, transactions, class IRIs that occur only as `rdf:type` objects, or nodes mentioned only by `sys:` statements, unless the dual view binds them. `:A:B` SHALL require every label and `:A|B` at least one, each label meaning a visible `rdf:type` statement. Inline property maps SHALL require a visible property equal (by Cypher equality) to each value. Label and property-map tests SHALL be existence tests that never multiply rows.

#### Scenario: Label conjunction and disjunction
- **WHEN** `v:alice` is `Person` and `Employee`, `v:bob` is `Person`, `v:acme` is `Company`
- **THEN** `MATCH (n:Person:Employee) RETURN n` returns only `v:alice`, and `MATCH (n:Person|Company) RETURN count(n) AS c` returns 3

#### Scenario: Duplicate label statements
- **WHEN** `(v:alice rdf:type v:Person)` exists as two live eids with different valid intervals and `MATCH (n:Person) RETURN n` runs
- **THEN** exactly one row is returned

#### Scenario: Numeric property map compares by value
- **WHEN** `(v:x v:score 30)` is stored as an integer and `MATCH (n {score: 30.0}) RETURN n` runs
- **THEN** `v:x` is returned

#### Scenario: Unlabelled scan excludes non-nodes
- **WHEN** the store holds `(v:alice rdf:type v:Person)`, e1 = `(v:alice v:worksAt v:acme)`, `(e1 v:confidence 0.8)` and `(tx1 sys:author v:agent7)`, and `MATCH (n) RETURN n` runs
- **THEN** exactly `v:alice` and `v:acme` are returned

### Requirement: Node identity
The reserved property key `` `@id` `` in a node pattern SHALL match the node with that identity, given as a declared CURIE, an absolute IRI or a skolem IRI (`urn:tiramemsu:node:<n>`, `urn:tiramemsu:bnode:<n>`, `urn:tiramemsu:stmt:<n>`). `elementId(x)` SHALL return the node's IRI, or the skolem IRI of an anonymous node, blank node or statement. `id(x)` SHALL return the raw ObjectId as an Integer. An identity that resolves to nothing visible SHALL match no rows.

#### Scenario: Match by CURIE and render back
- **WHEN** `` MATCH (n {`@id`: 'v:alice'}) RETURN elementId(n) AS e `` runs
- **THEN** `e` is the full IRI of `v:alice`

#### Scenario: Skolem IRI round trip
- **WHEN** an anonymous node has element id `urn:tiramemsu:node:7` and `` MATCH (n {`@id`: 'urn:tiramemsu:node:7'}) RETURN id(n) = id(n) AS same, elementId(n) AS e `` runs
- **THEN** one row is returned with `same = true` and `e = "urn:tiramemsu:node:7"`

### Requirement: Relationship patterns
A relationship pattern SHALL match one visible relationship statement per row: for `(a)-[r:T]->(b)` subject `a`, predicate `T`, object `b`, with `<-` reversing the roles. An undirected pattern SHALL match each statement once per orientation, and a self-loop once. `[:A|B]` SHALL match either type. An untyped pattern SHALL match every relationship except `sys:` predicates. Two live statements with equal subject, predicate and object SHALL be two rows. An inline relationship property map SHALL test properties whose subject is the relationship's eid.

#### Scenario: Undirected match
- **WHEN** only `(v:alice v:knows v:bob)` is stored and `MATCH (a)-[:knows]-(b) RETURN a, b` runs
- **THEN** the rows are `(v:alice, v:bob)` and `(v:bob, v:alice)`

#### Scenario: Parallel edges
- **WHEN** two live statements `(v:alice v:called v:bob)` exist and `MATCH (:Person)-[r:called]->() RETURN count(r) AS c` runs with `v:alice` a `Person`
- **THEN** `c` is 2

#### Scenario: Untyped pattern hides sys predicates
- **WHEN** `(e10 sys:supersedes e1)` is live and `MATCH ()-[r]->() RETURN type(r)` runs
- **THEN** no row has type `sys:supersedes`

#### Scenario: Relationship property map
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` has `(e1 v:role "cto")`, e2 = `(v:bob v:worksAt v:acme)` has `(e2 v:role "dev")`, and `MATCH (p)-[:worksAt {role: 'cto'}]->() RETURN p` runs
- **THEN** only `v:alice` is returned

### Requirement: Relationship isomorphism
Within one `MATCH` or `OPTIONAL MATCH` clause, across all its comma-separated patterns and including the relationships inside variable-length and shortest matches, no two relationship positions SHALL bind the same eid. The constraint SHALL NOT span separate clauses. `MATCH DIFFERENT RELATIONSHIPS` SHALL mean the default. `MATCH REPEATABLE ELEMENTS` SHALL evaluate the clause under homomorphism, and combining it with a variable-length pattern MUST fail with `Unsupported`.

#### Scenario: No reuse within a clause
- **WHEN** only `(v:a v:knows v:b)` is stored
- **THEN** `MATCH (x)-[:knows]-(y)-[:knows]-(z) RETURN count(*) AS c` and `MATCH (x)-[r1:knows]->(y), (p)-[r2:knows]->(q) RETURN count(*) AS c` both return `c = 0`

#### Scenario: Separate clauses may reuse
- **WHEN** `MATCH (x)-[r1:knows]->(y) MATCH (p)-[r2:knows]->(q) RETURN count(*) AS c` runs on the same store
- **THEN** `c` is 1

#### Scenario: Repeatable elements
- **WHEN** `MATCH REPEATABLE ELEMENTS (x)-[:knows]-(y)-[:knows]-(z) RETURN count(*) AS c` runs on the same store
- **THEN** `c` is 2

#### Scenario: Repeatable elements with variable length
- **WHEN** `MATCH REPEATABLE ELEMENTS (a)-[*]->(b) RETURN b` is compiled
- **THEN** it fails with `Unsupported`

### Requirement: Variable-length relationships
`-[r:T*m..n]->` (with the forms `*`, `*n`, `*m..`, `*..n`, `*m..n`; default minimum 1) SHALL match trails of `m` to `n` relationships of the given types (any relationship-view statement when untyped), in the written direction, with no relationship eid repeated, and SHALL bind `r` to the list of relationships in order. An unbounded upper limit SHALL stop at the database's configured maximum hop count (default 15) without an error; an explicit upper bound SHALL be honoured. A variable-length or shortest pattern MUST fail with `Unsupported` unless one endpoint is anchored: bound by an earlier clause, or constrained by an identity, a label, a property map, a fixed-length relationship of the same clause, or the end of another anchored path; a property map on it MUST fail with `Unsupported`; `n < m` SHALL match nothing. Exceeding the search-state limit MUST fail with `PathLimitExceeded` and never return a truncated result.

#### Scenario: Bounded reachability
- **WHEN** `v:a knows v:b`, `v:b knows v:c`, `v:c knows v:d` are stored and `` MATCH ({`@id`: 'v:a'})-[:knows*1..2]->(x) RETURN x `` runs
- **THEN** the rows are `v:b` and `v:c`

#### Scenario: Zero-length match
- **WHEN** `` MATCH (s {`@id`: 'v:a'})-[:knows*0..1]->(x) RETURN x `` runs on the same store
- **THEN** the rows are `v:a` and `v:b`

#### Scenario: Trail on a cycle
- **WHEN** only `v:a knows v:b` and `v:b knows v:a` are stored and `` MATCH ({`@id`: 'v:a'})-[rs:knows*]->(x) RETURN size(rs) AS n `` runs
- **THEN** the rows are `n = 1` and `n = 2`, and the search terminates

#### Scenario: Default hop cap
- **WHEN** a `knows` chain of 20 relationships starts at `v:n0` and `` MATCH ({`@id`: 'v:n0'})-[:knows*]->(x) RETURN count(x) AS c `` runs with default options
- **THEN** `c` is 15

#### Scenario: Unbound endpoints
- **WHEN** `MATCH (a)-[:knows*]->(b) RETURN a, b` runs as the first clause
- **THEN** it fails with `Unsupported`, while `MATCH (a:Person)-[:knows*]->(b) RETURN a, b` runs

### Requirement: Shortest path patterns
`shortestPath((a)-[:T*m..n]-(b))` SHALL return, for each bound pair, one path of minimum length, choosing the lexicographically smallest relationship sequence by eid. `allShortestPaths(…)` SHALL return every path of minimum length. The minimum length MUST be 0 or 1, otherwise the query fails with `Unsupported`; a shortest-path pattern over more than one relationship pattern MUST fail with `Unsupported`. Pairs with no path SHALL produce no row.

#### Scenario: One shortest path
- **WHEN** `v:a knows v:b`, `v:b knows v:d`, `v:a knows v:c`, `v:c knows v:d` are stored and `` MATCH p = shortestPath(({`@id`: 'v:a'})-[:knows*]->({`@id`: 'v:d'})) RETURN length(p) AS l `` runs
- **THEN** exactly one row with `l = 2` is returned

#### Scenario: All shortest paths
- **WHEN** the same query uses `allShortestPaths`
- **THEN** two rows with `l = 2` are returned

#### Scenario: Minimum length above one
- **WHEN** `MATCH p = shortestPath((a)-[*2..5]->(b)) RETURN p` is compiled
- **THEN** it fails with `Unsupported`

### Requirement: Named paths
A path variable `p = …` over a fixed-length, variable-length or shortest pattern SHALL bind a Path value of the matched nodes and relationships in pattern order. `nodes(p)`, `relationships(p)` and `length(p)` SHALL return its nodes, its relationships and its relationship count.

#### Scenario: Two-hop path
- **WHEN** `v:a knows v:b` and `v:b knows v:c` are stored and `MATCH p = (x)-[:knows]->()-[:knows]->(z) RETURN length(p) AS l, [n IN nodes(p) | elementId(n)] AS ids` runs
- **THEN** `l` is 2 and `ids` lists the element ids of `v:a`, `v:b`, `v:c` in that order

### Requirement: Property access
`x.key` SHALL read the visible property statements of `x` for the resolved key: `null` if none, the value if there is one distinct value, and otherwise the list of distinct values ordered by the lowest eid holding each. `keys(x)` SHALL list the resolved names of keys with at least one value, and `properties(x)` SHALL map each to its `x.key`. A property of `null` SHALL be `null`. Labels, types and keys SHALL resolve through the vocabulary current at compile time, also under a historical time clause.

#### Scenario: Missing and multi-valued
- **WHEN** `v:alice` has `v:nick "al"` (tx 1) and `v:nick "ally"` (tx 2) and no `v:email`
- **THEN** `n.nick` is `["al", "ally"]` and `n.email` is `null`

#### Scenario: keys and properties
- **WHEN** `v:alice` has `v:name "Alice"` and `v:age 42` and `RETURN keys(n), properties(n)` runs for her
- **THEN** `keys(n)` contains exactly `"age"` and `"name"`, and `properties(n)` is `{age: 42, name: "Alice"}`

### Requirement: Volatile values as virtual properties
When the pattern's view is transaction time `Now` with valid time unfiltered, `x.key` on a node SHALL fall back to the volatile value of `(x, key)` when no property statement for that key is visible, and `keys(x)` / `properties(x)` SHALL include volatile keys. Under any other view volatile values SHALL be absent. Statements in node form SHALL never show volatile values.

#### Scenario: Volatile value now
- **WHEN** volatile `(v:alice, v:lastSeen)` is 2026-09-29T10:00Z, no `v:lastSeen` statement exists, and `` MATCH (n {`@id`: 'v:alice'}) RETURN n.lastSeen AS s `` runs on the now view
- **THEN** `s` is DateTime 2026-09-29T10:00:00.000Z

#### Scenario: Statement wins
- **WHEN** `(v:alice v:lastSeen "2020-01-01T00:00:00Z"^^xsd:dateTime)` is also live
- **THEN** `s` is DateTime 2020-01-01T00:00:00.000Z

#### Scenario: Absent in the past
- **WHEN** the first query runs with `USE AS OF` the latest transaction, with `USE HISTORY`, or with `USE VALID AT date('2026-01-01')`
- **THEN** `s` is `null`

### Requirement: WHERE and three-valued logic
`WHERE` SHALL keep rows whose condition is `true` and drop `false` and `null`. Comparisons with `null` SHALL be `null`; `AND`, `OR`, `XOR`, `NOT` SHALL follow Cypher's three-valued tables; `IS NULL` / `IS NOT NULL` SHALL never be `null`. `x IN list` SHALL be `true` on a match, `null` if no match but `x` or an element is `null`, else `false`. Incomparable types SHALL be `null` under ordering comparisons and `false` under `=`. `STARTS WITH`, `ENDS WITH`, `CONTAINS` and `=~` (whole-string regular expression match) SHALL be supported.

#### Scenario: Three-valued connectives
- **WHEN** `RETURN null OR true AS a, null AND false AS b, null AND true AS c, NOT null AS d, null XOR true AS e` runs
- **THEN** the row is `true, false, null, null, null`

#### Scenario: IN with null
- **WHEN** `RETURN 2 IN [1, null] AS a, 1 IN [1, null] AS b, 3 IN [1, 2] AS c` runs
- **THEN** the row is `null, true, false`

#### Scenario: Null comparison drops the row both ways
- **WHEN** `v:alice` has no `v:age`
- **THEN** neither `WHERE n.age > 30` nor `WHERE NOT (n.age > 30)` keeps her row

#### Scenario: Regular expression
- **WHEN** `RETURN 'Alice' =~ 'Al.*' AS a, 'Alice' =~ 'li' AS b` runs
- **THEN** the row is `true, false`

### Requirement: OPTIONAL MATCH
`OPTIONAL MATCH` SHALL be a left outer join with the incoming rows: when its pattern and attached `WHERE` have no match for a row, the row SHALL be kept with every newly introduced variable `null`.

#### Scenario: Missing part yields nulls
- **WHEN** `v:bob` is a `Person` with no `worksAt` and `MATCH (p:Person) OPTIONAL MATCH (p)-[r:worksAt]->(c) RETURN p, r, c` runs
- **THEN** the row for `v:bob` has `r = null` and `c = null`

#### Scenario: Attached WHERE is a join condition
- **WHEN** `v:alice` works only at `v:acme` (named "Acme") and `MATCH (p {name:'Alice'}) OPTIONAL MATCH (p)-[:worksAt]->(c) WHERE c.name = 'Globex' RETURN p, c` runs
- **THEN** one row with `c = null` is returned

### Requirement: WITH and RETURN projection
`WITH` and `RETURN` SHALL project items with aliases, `DISTINCT`, aggregation and `ORDER BY`/`SKIP`/`LIMIT`. After `WITH` only projected variables SHALL be in scope, and a `WHERE` after `WITH` SHALL filter the projected rows. A column SHALL be named by its alias, else by the item's text as written. `RETURN *` SHALL return all variables in scope ordered by name. `DISTINCT` SHALL use Cypher equivalence, under which `null` equals `null`.

#### Scenario: Filter on an aggregate
- **WHEN** `v:acme` has three employees and `v:globex` one, and `MATCH (p)-[:worksAt]->(c) WITH c, count(p) AS n WHERE n > 1 RETURN c.name, n` runs
- **THEN** one row `("Acme", 3)` is returned

#### Scenario: Column naming and star
- **WHEN** `MATCH (n:Person) RETURN n.name, n.age AS years` and `MATCH (b)<-[r:worksAt]-(a) RETURN *` run
- **THEN** the columns are `n.name`, `years` and `a`, `b`, `r` respectively

#### Scenario: DISTINCT nulls
- **WHEN** two people have no age and `MATCH (n:Person) RETURN DISTINCT n.age AS a` runs
- **THEN** exactly one row has `a = null`

### Requirement: Ordering, SKIP and LIMIT
`ORDER BY` SHALL sort by Cypher value order: numbers numerically across Integer and Float, strings by code point, dates chronologically, date-times by instant regardless of offset, and across types ascending map, node, relationship, list, path, datetime, date, string, boolean, number, with `null` last ascending and first descending. Ties SHALL keep input order. `SKIP` and `LIMIT` SHALL accept non-negative integer literals or parameters; a negative or non-integer value MUST fail.

#### Scenario: Mixed numeric order
- **WHEN** scores 10 (integer), 9.5 (double) and 100 (integer) exist and `RETURN n.score ORDER BY n.score` runs over them
- **THEN** the order is 9.5, 10, 100

#### Scenario: Nulls in descending order
- **WHEN** ages 30, null, 20 exist and `RETURN n.age ORDER BY n.age DESC` runs over them
- **THEN** the order is null, 30, 20

#### Scenario: Negative LIMIT
- **WHEN** `MATCH (n) RETURN n LIMIT -1` is compiled
- **THEN** it fails with a `Parse` error whose span starts at `-1`

### Requirement: UNWIND
`UNWIND e AS x` SHALL produce one row per list element, no row for an empty list or `null`, and one row with the value itself for a non-list value.

#### Scenario: Unwind values
- **WHEN** `UNWIND [1, 2, 3] AS x RETURN x * 10 AS y`, `UNWIND null AS x RETURN x` and `UNWIND [] AS x RETURN x` run
- **THEN** the first returns 10, 20, 30 and the others return no rows

### Requirement: Aggregation
The system SHALL support `count(*)`, `count`, `sum`, `avg`, `min`, `max`, `collect`, `stdev`, `stdevp`, `percentileCont` and `percentileDisc`, each aggregate taking an optional `DISTINCT`. Non-aggregated items of the same projection SHALL be the grouping keys. Aggregates other than `count(*)` SHALL ignore `null`. With no grouping keys and no input rows, one row SHALL be returned with `count` 0, `collect` `[]` and the others `null`. An aggregate in `WHERE`, or nested in an aggregate, MUST fail with a `Parse` error.

#### Scenario: Empty input
- **WHEN** no `Unicorn` exists and `MATCH (n:Unicorn) RETURN count(n) AS c, collect(n) AS l, sum(n.x) AS s` runs
- **THEN** exactly one row `0, [], null` is returned

#### Scenario: Nulls and DISTINCT
- **WHEN** ages 30, 30 and null exist and `RETURN count(n.age) AS a, count(DISTINCT n.age) AS b, count(*) AS c` runs over them
- **THEN** the row is `2, 1, 3`

#### Scenario: Aggregate in WHERE
- **WHEN** `MATCH (n) WHERE count(n) > 1 RETURN n` is compiled
- **THEN** it fails with a `Parse` error whose span starts at `count(n)`

### Requirement: CALL subqueries and UNION
`CALL { … }` without an importing `WITH` SHALL be evaluated once and cross-joined with the incoming rows; with an importing `WITH v1, …` as its first clause it SHALL run once per incoming row. Each result row SHALL be appended to its outer row, and an outer row with no result row SHALL be dropped. A returned variable that shadows an outer one MUST fail with a `Parse` error. `UNION` SHALL combine branches with identical column names and remove duplicates; `UNION ALL` SHALL keep them; differing names MUST fail with a `Parse` error.

#### Scenario: Correlated aggregation
- **WHEN** `v:acme` has 3 employees and `v:initech` none, and `MATCH (c:Company) CALL { WITH c OPTIONAL MATCH (p)-[:worksAt]->(c) RETURN count(p) AS staff } RETURN c.name, staff` runs
- **THEN** the rows are `("Acme", 3)` and `("Initech", 0)`

#### Scenario: Uncorrelated cross product
- **WHEN** 2 `Person` and 3 `Company` nodes exist and `MATCH (p:Person) CALL { MATCH (c:Company) RETURN c } RETURN count(*) AS n` runs
- **THEN** `n` is 6

#### Scenario: UNION and UNION ALL
- **WHEN** two people exist and `MATCH (n:Person) RETURN n.name AS x UNION MATCH (n:Person) RETURN n.name AS x` runs, then the same with `UNION ALL`
- **THEN** the first returns 2 rows and the second 4

### Requirement: Existential subqueries and pattern predicates
`EXISTS { MATCH … [WHERE …] }`, `EXISTS { pattern }` and a bare pattern used as a `WHERE` predicate SHALL be `true` when at least one match exists for the current row and `false` otherwise, never `null`, and SHALL never multiply rows.

#### Scenario: NOT EXISTS
- **WHEN** `v:bob` has no employer and `MATCH (p:Person) WHERE NOT EXISTS { (p)-[:worksAt]->() } RETURN p` runs
- **THEN** `v:bob` is returned and employed people are not

#### Scenario: Pattern predicate does not multiply
- **WHEN** `v:alice` has two `worksAt` relationships and `MATCH (p:Person) WHERE (p)-[:worksAt]->() RETURN p` runs
- **THEN** `v:alice` appears once

### Requirement: Expressions and functions
The system SHALL evaluate literals (integer, float, string, boolean, `null`, list, map), parameters, arithmetic, `+` on strings and lists, comparisons, list indexing and slicing, map projection, simple and searched `CASE`, and list comprehension. It SHALL provide exactly the function set of the pinned Rust build with openCypher semantics: entity functions (`id`, `elementId`, `labels`, `type`, `keys`, `properties`, `startNode`, `endNode`, `nodes`, `relationships`, `length`), list and scalar functions (`coalesce`, `size`, `head`, `last`, `tail`, `range`, `isEmpty`, `nullIf`, `exists`), conversions (`toString`, `toInteger`, `toFloat`, `toBoolean` and their `…OrNull` forms), string functions (`toLower`, `toUpper`, `trim`, `ltrim`, `rtrim`, `substring`, `replace`, `split`, `left`, `right`, `reverse`, `char_length`, `character_length`), numeric functions (`abs`, `ceil`, `floor`, `round`, `sign`, `sqrt`, `exp`, `log`, `log10`, `e`, `pi`, `isNaN`, `rand`, trigonometric `sin`, `cos`, `tan`, `cot`, `asin`, `acos`, `atan`, `atan2`, `degrees`, `radians`, `haversin`), `randomUUID`, and temporal functions (`date`, `datetime`, `localdatetime`, `timestamp`, their `.truncate`, `.statement`, `.transaction`, `.realtime` forms, `datetime.fromEpoch`, `datetime.fromEpochMillis`). Function names SHALL be case-insensitive. Any other function, and pattern comprehension, MUST fail with `Unsupported` naming it.

#### Scenario: CASE and coalesce
- **WHEN** `RETURN CASE WHEN 20 >= 18 THEN 'adult' ELSE 'minor' END AS k, coalesce(null, 'x') AS c` runs
- **THEN** the row is `"adult", "x"`

#### Scenario: List comprehension
- **WHEN** `RETURN [x IN range(1, 5) WHERE x % 2 = 1 | x * x] AS l` runs
- **THEN** `l` is `[1, 9, 25]`

#### Scenario: Unicode case mapping
- **WHEN** `RETURN toUpper('straße') AS u` runs
- **THEN** `u` is `"STRASSE"`

#### Scenario: Unknown function and pattern comprehension
- **WHEN** `RETURN apoc.text.clean('x')` and `MATCH (a) RETURN [(a)-->(b) | b.name]` are compiled
- **THEN** both fail with `Unsupported`, naming `apoc.text.clean` and pattern comprehension

### Requirement: Parameters
`$name` SHALL be bound from the supplied parameter map wherever openCypher allows an expression, including property maps, `SKIP`, `LIMIT`, `UNWIND` and time clauses. A referenced parameter that is not supplied MUST fail compilation with a `Parse` error naming it and spanning its reference. Unreferenced parameters SHALL be ignored.

#### Scenario: Parameter in a property map
- **WHEN** `MATCH (n:Person {name: $who}) RETURN n` runs with `who = "Alice"`
- **THEN** the Alice node is returned

#### Scenario: Missing parameter
- **WHEN** `MATCH (n {name: $who}) RETURN n` runs with an empty map
- **THEN** it fails with a `Parse` error naming `who`, and nothing executes

### Requirement: Result value model
Stored literals SHALL be returned as: integers (including `xsd:integer` beyond 60 bits within 64-bit range) as Integer; booleans as Boolean; doubles and decimals as Float; plain and language-tagged strings as String without the tag; dates as Date; date-times with a timezone as DateTime keeping the stored offset, and without a timezone as LocalDateTime, both at millisecond precision; other datatypes as a String of the lexical form. A node SHALL be a Node with element id, labels and properties; a relationship a Relationship with element id, type, start and end element ids and properties; paths, lists and maps structurally. Every value SHALL have the JSON encoding used by the Rust JSON bridge.

#### Scenario: Scalar types
- **WHEN** `v:x` has `v:i 7`, `v:f 1.5`, `v:b true`, `v:d "2025-03-01"^^xsd:date`, `v:t "2025-03-01T10:00:00+02:00"^^xsd:dateTime`, `v:s "hé"@fr` and the six properties are returned
- **THEN** they are Integer 7, Float 1.5, Boolean true, Date 2025-03-01, DateTime 2025-03-01T10:00:00.000+02:00, String "hé"

#### Scenario: Date-time equality by instant
- **WHEN** `v:x` has `v:a "2026-03-01T12:00:00+02:00"^^xsd:dateTime` and `v:b "2026-03-01T10:00:00Z"^^xsd:dateTime`
- **THEN** `n.a = n.b` is `true`, and `n.a` still reads back with offset +02:00

#### Scenario: LocalDateTime
- **WHEN** `v:x` has `v:l "2026-03-01T09:00:00"^^xsd:dateTime`
- **THEN** `n.l` is LocalDateTime 2026-03-01T09:00:00.000

### Requirement: Built-in procedures
`CALL db.labels()`, `CALL db.relationshipTypes()` and `CALL db.propertyKeys()`, standalone or with `YIELD`, SHALL return the distinct resolved names used by visible statements in the query's view, excluding `sys:` names. Any other procedure MUST fail with `Unsupported` naming it.

#### Scenario: db.labels
- **WHEN** `Person` and `Company` nodes exist and `CALL db.labels() YIELD label RETURN label ORDER BY label` runs
- **THEN** the rows are `"Company"` and `"Person"`

#### Scenario: Unknown procedure
- **WHEN** `CALL dbms.components()` is compiled
- **THEN** it fails with `Unsupported` naming `dbms.components`

### Requirement: Unsupported constructs
The system MUST reject, with `Unsupported` naming the feature and before anything executes: `FOREACH`, `LOAD CSV`, `CALL { … } IN TRANSACTIONS`, `USE <graph name>`, schema commands (`CREATE INDEX`, `CREATE CONSTRAINT`, `DROP …`, `SHOW …`), quantified path patterns, GQL path modes (`WALK`, `TRAIL`, `SIMPLE`, `ACYCLIC`), label expressions with `!`, `&` or `%`, dynamic labels or types, durations, `time`/`localtime`, and regular-expression Unicode property classes `\p{…}` / `\P{…}`.

#### Scenario: FOREACH and LOAD CSV
- **WHEN** `MATCH (n) FOREACH (x IN [1] | SET n.a = x)` and `LOAD CSV FROM 'file:///x.csv' AS row RETURN row` are compiled
- **THEN** they fail with `Unsupported` naming `FOREACH` and `LOAD CSV`

#### Scenario: Negated label
- **WHEN** `MATCH (n:!Person) RETURN n` is compiled
- **THEN** it fails with `Unsupported` naming the label expression

### Requirement: Compile-time errors with spans
Text that is not valid openCypher or a valid tiramemsu extension, and these semantic errors, MUST fail with a `Parse` error carrying the Cypher dialect and the byte span of the offending element in the original text, before anything executes: an undefined variable; a variable used with conflicting kinds (other than the dual-view use of a relationship variable in node position); an aggregate in a disallowed position; a missing parameter; a `UNION` column mismatch. The error kind and the span start offset SHALL equal those of the pinned Rust build.

#### Scenario: Unclosed parenthesis
- **WHEN** `MATCH (n:Person RETURN n` is compiled
- **THEN** it fails with a `Parse` error whose span starts at byte 6

#### Scenario: Span after an extension
- **WHEN** `USE AS OF 3 MATCH (n RETURN n` is compiled
- **THEN** the `Parse` error span starts at byte 18

#### Scenario: Undefined and out-of-scope variables
- **WHEN** `MATCH (n) RETURN m` and `MATCH (p)-[:worksAt]->(c) WITH c RETURN p` are compiled
- **THEN** both fail with a `Parse` error spanning `m` and the final `p` respectively

### Requirement: Runtime errors
Runtime errors defined by openCypher, including arithmetic on incompatible types, integer division or modulo by zero, 64-bit integer overflow and invalid regular expressions, MUST fail the whole query with an `Eval` error. Conversions that openCypher defines as lenient SHALL return `null`.

#### Scenario: Type error and division by zero
- **WHEN** `RETURN 'a' - 1` and `RETURN 1 / 0` run
- **THEN** both fail with `Eval`

#### Scenario: Integer overflow
- **WHEN** `RETURN 9223372036854775807 + 1` runs
- **THEN** it fails with `Eval`

#### Scenario: Lenient conversion
- **WHEN** `RETURN toInteger('x') AS v` runs
- **THEN** `v` is `null`
