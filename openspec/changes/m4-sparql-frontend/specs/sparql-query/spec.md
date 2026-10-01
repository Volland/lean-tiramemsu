## Purpose

Lets applications and agents read the Lean tiramemsu store with SPARQL 1.1 query text, with the same accepted language, results and errors as the pinned Rust build, executed by the proven M3 evaluator. Examples assume the predeclared prefixes and the default `@vocab` `urn:tiramemsu:v:` for `v:`.

## ADDED Requirements

### Requirement: Queries read one view and never write

The system SHALL accept SPARQL query text on any view (current, as of a transaction or instant, history, valid at an instant, speculative) and SHALL evaluate it over exactly the statements that view makes visible. A query SHALL NOT modify the store. Queries and updates SHALL share one entry point, which dispatches on the text.

#### Scenario: Current view hides retracted statements
- **WHEN** `(v:alice v:worksAt v:acme)` was asserted in tx 1 and retracted in tx 2, and `SELECT ?c WHERE { v:alice v:worksAt ?c }` runs on the current view
- **THEN** the result has the variable `c` and zero rows

#### Scenario: Historical view sees the past
- **WHEN** the same text runs on the view as of tx 1
- **THEN** exactly one row `c = v:acme` is returned

#### Scenario: Speculative view sees uncommitted state
- **WHEN** inside a speculative transaction that asserted `(v:bob v:worksAt v:initech)`, `ASK { v:bob v:worksAt v:initech }` runs on the speculative view
- **THEN** the answer is `true`, and on the current view after the speculation ends it is `false`

### Requirement: Execution through the proven evaluator

Every query SHALL be parsed, checked and lowered to the M3 logical IR before any store read, and SHALL be executed only by the M3 evaluator on that IR, followed by the projection, ordering and result-form step of its query form. No query construct SHALL be evaluated outside the IR. The rows of a query SHALL therefore not depend on join order or on the planner's choice between join algorithms.

#### Scenario: Join order does not change results
- **WHEN** the same `SELECT` over a cyclic three-pattern BGP runs with the planner forced to each permutation of its patterns and to both join algorithms
- **THEN** all runs return the same multiset of rows

#### Scenario: Rejected text reads nothing
- **WHEN** a text that fails to parse or is rejected as unsupported is submitted
- **THEN** the store receives no range scan for that request

#### Scenario: Machine-checked execution semantics
- **WHEN** the proofs library builds
- **THEN** the property that running any prepared query on the model store equals the IR denotation of its lowered plan, post-processed by its query form, holds as a theorem whose axioms satisfy the proof policy

### Requirement: Query forms

The system SHALL support `SELECT` (explicit variables, `*`, `(expr AS ?v)`, `DISTINCT`, `REDUCED`), `ASK` and `CONSTRUCT` (including `CONSTRUCT WHERE`). `SELECT *` SHALL project every in-scope variable in first-appearance order and SHALL NOT project hidden variables introduced for blank nodes, triple terms, reifiers or provenance. `ASK` SHALL be true exactly when the pattern has a solution. `DESCRIBE` SHALL fail with `Unsupported { feature: "DESCRIBE" }`.

#### Scenario: Projected expression
- **WHEN** `(v:alice v:age 41)` is live and `SELECT ?p ((?a + 1) AS ?next) WHERE { ?p v:age ?a }` runs
- **THEN** the variables are `p, next` in that order and the only row is `p = v:alice`, `next = 42` as `xsd:integer`

#### Scenario: SELECT star hides internal variables
- **WHEN** `SELECT * WHERE { ?s v:worksAt [] }` runs over one live `v:worksAt` statement
- **THEN** the result variables are exactly `s`

#### Scenario: DESCRIBE is rejected
- **WHEN** `DESCRIBE v:alice` is submitted
- **THEN** the request fails with `Unsupported { feature: "DESCRIBE" }`

### Requirement: Parsing and parse errors

The system SHALL accept the complete SPARQL 1.1 query grammar, including keywords in any letter case and `BASE` resolution of relative IRIs, plus the SPARQL 1.2 triple-term, reifier and annotation syntax. Parsing SHALL terminate on every input without a crash. Invalid text, an undeclared prefix, a relative IRI with no `BASE`, and `BIND` of a variable already in scope SHALL fail with a `Parse` error of dialect SPARQL that carries the 1-based line, the 1-based column in characters, the byte offset of the first token that cannot continue a valid request, and a message naming what was expected or what is wrong.

#### Scenario: Error position
- **WHEN** `SELECT ?s WHERE {\n  ?s v:p ?o\n  FILTER(\n}` is submitted
- **THEN** the request fails with a `Parse` error of dialect SPARQL at line 4, column 1

#### Scenario: Undeclared prefix
- **WHEN** `SELECT ?s WHERE { ?s ex:p ?o }` is submitted and `ex:` is neither declared nor predeclared
- **THEN** the request fails with a `Parse` error whose message says the prefix `ex` was not found

#### Scenario: Relative IRI without BASE
- **WHEN** `SELECT ?o WHERE { <alice> v:knows ?o }` is submitted with no `BASE`
- **THEN** the request fails with a `Parse` error, and with `BASE <http://example.org/>` prepended it parses and `<alice>` denotes `http://example.org/alice`

#### Scenario: BIND over an in-scope variable
- **WHEN** `SELECT ?a WHERE { v:alice v:age ?a BIND(1 AS ?a) }` is submitted
- **THEN** the request fails with a `Parse` error of dialect SPARQL

#### Scenario: Left-associative arithmetic
- **WHEN** `SELECT ((10 - 4 - 3) AS ?x) WHERE {}` runs
- **THEN** the single row has `x = 3`

#### Scenario: Arbitrary input terminates
- **WHEN** one million random byte strings and random token sequences are submitted
- **THEN** each one either parses or fails with a `Parse` error, and none crashes or hangs

### Requirement: Predeclared prefixes and vocabulary

The system SHALL predeclare `rdf:`, `rdfs:`, `xsd:`, `sys:` (`urn:tiramemsu:sys:`), `tm:` (`urn:tiramemsu:tm:`), `v:` (the database's configured `@vocab` IRI) and every entry of the database prefix table, read in the snapshot of the view the text was submitted on. A `PREFIX` declaration in the text SHALL override a predeclared prefix of the same name for that request only.

#### Scenario: Default vocabulary
- **WHEN** the database `@vocab` is the default and `SELECT ?c WHERE { v:alice v:worksAt ?c }` runs without `PREFIX`
- **THEN** `v:worksAt` denotes `urn:tiramemsu:v:worksAt`

#### Scenario: Database prefix table
- **WHEN** the prefix table maps `schema` to `https://schema.org/` and `SELECT ?n WHERE { ?p schema:name ?n }` runs
- **THEN** `schema:name` denotes `https://schema.org/name`

#### Scenario: Changed vocabulary
- **WHEN** `@vocab` was set to `https://ex.org/` and `ASK { v:a v:b v:c }` runs
- **THEN** the pattern uses `https://ex.org/a`, `https://ex.org/b` and `https://ex.org/c`

#### Scenario: Query prefix overrides
- **WHEN** a query declares `PREFIX v: <http://example.org/>` and uses `v:x`
- **THEN** `v:x` denotes `http://example.org/x` for that query only

### Requirement: Triple patterns match a set of triples

A basic graph pattern SHALL be the join of its triple patterns on shared variables, with homomorphism semantics: two patterns MAY match the same statement and distinct variables MAY bind equal values. A triple pattern whose eid is not bound SHALL match each distinct visible `(s, p, o)` once, however many visible eids carry it. A constant that never occurs in the store SHALL make its pattern produce no solution, without error. Multiplicity SHALL otherwise follow SPARQL bag semantics.

#### Scenario: Two-pattern join
- **WHEN** `(v:alice v:worksAt v:acme)`, `(v:acme v:locatedIn v:berlin)` and `(v:bob v:worksAt v:initech)` are live and `SELECT ?p ?city WHERE { ?p v:worksAt ?c . ?c v:locatedIn ?city }` runs
- **THEN** exactly one row `p = v:alice`, `city = v:berlin` is returned

#### Scenario: Two episodes are one triple
- **WHEN** `(v:alice v:worksAt v:acme)` is live as two eids with different valid times and `SELECT (COUNT(*) AS ?n) WHERE { v:alice v:worksAt ?c }` runs
- **THEN** the single row has `n = 1`

#### Scenario: Unknown constant
- **WHEN** `SELECT ?o WHERE { v:neverSeen v:worksAt ?o }` runs and `v:neverSeen` was never stored
- **THEN** zero rows are returned and no error is raised

#### Scenario: Homomorphic matching
- **WHEN** only `(v:alice v:knows v:bob)` is live and `SELECT ?a ?c WHERE { ?a v:knows ?b . ?c v:knows ?d }` runs
- **THEN** exactly one row `a = v:alice`, `c = v:alice` is returned

### Requirement: Graph pattern operators

The system SHALL evaluate `OPTIONAL` as a left join whose join condition includes the `FILTER`s written directly in the optional group; `UNION` as bag union with branch-only variables unbound; `MINUS` with SPARQL 1.1 semantics (a left row is removed only by a compatible right row sharing at least one bound variable); `FILTER EXISTS` and `FILTER NOT EXISTS` correlated with the current row; `BIND` extending each row and leaving its variable unbound on an expression error; `VALUES` inline and trailing as joined inline data with `UNDEF` unbound; and nested `SELECT` subqueries with their own modifiers, of which only the projected variables are visible outside.

#### Scenario: Filter inside OPTIONAL is a join condition
- **WHEN** `(v:alice v:name "Alice")` and `(v:alice v:age 41)` are live and `SELECT ?p ?age WHERE { ?p v:name ?n OPTIONAL { ?p v:age ?age FILTER(?age > 50) } }` runs
- **THEN** one row is returned with `p = v:alice` and `age` unbound

#### Scenario: Filter in a nested group inside OPTIONAL
- **WHEN** `(v:bob v:name "Bob")` and `(v:bob v:age 41)` are live and `SELECT ?p ?age WHERE { ?p v:name ?n OPTIONAL { { ?p v:age ?age FILTER(?n = "Bob") } } }` runs
- **THEN** one row is returned with `p = v:bob` and `age` unbound, because the filter of the nested group cannot see `?n` (a registered deviation from Rust, which merges it into the join condition)

#### Scenario: MINUS without shared variables
- **WHEN** `(v:alice a v:Person)`, `(v:bob a v:Person)` and `(v:bob v:banned true)` are live and `SELECT ?p WHERE { ?p a v:Person MINUS { ?x v:banned true } }` runs
- **THEN** both `v:alice` and `v:bob` are returned

#### Scenario: Correlated NOT EXISTS
- **WHEN** the same data is queried with `SELECT ?p WHERE { ?p a v:Person FILTER NOT EXISTS { ?p v:banned true } }`
- **THEN** exactly one row `p = v:alice` is returned

#### Scenario: BIND error leaves the variable unbound
- **WHEN** `(v:bob v:age "unknown")` is live and `SELECT ?p ?y WHERE { ?p v:age ?a BIND(?a * 2 AS ?y) }` runs
- **THEN** one row is returned with `p = v:bob` and `y` unbound

#### Scenario: Trailing VALUES with UNDEF
- **WHEN** `(v:alice v:age 41)` and `(v:bob v:age 30)` are live and `SELECT ?p ?a WHERE { ?p v:age ?a } VALUES (?p ?a) { (UNDEF 30) }` runs
- **THEN** exactly one row `(v:bob, 30)` is returned

#### Scenario: Subquery hides inner variables
- **WHEN** `SELECT ?a WHERE { { SELECT ?p WHERE { ?p v:age ?a } } }` runs
- **THEN** every row has `a` unbound

### Requirement: Filters and expression errors

A `FILTER` SHALL keep a row only when the effective boolean value of its expression is true. An error, including a type error or an unbound variable, SHALL make the filter false for that row and SHALL NOT fail the query. `!`, `&&` and `||` SHALL follow SPARQL's error rules. Numeric comparison SHALL be by value across `xsd:integer`, `xsd:decimal` and `xsd:double`.

#### Scenario: Type error removes the row
- **WHEN** `(v:alice v:age 41)` and `(v:bob v:age "unknown")` are live and `SELECT ?p WHERE { ?p v:age ?a FILTER(?a > 30) }` runs
- **THEN** exactly one row `p = v:alice` is returned and no error is raised

#### Scenario: Error rescued by OR
- **WHEN** the same data is queried with `FILTER(?a > 30 || true)`
- **THEN** both `v:alice` and `v:bob` are returned

#### Scenario: Numeric equality across datatypes
- **WHEN** `(v:alice v:age 41)` is live and `ASK { v:alice v:age ?a FILTER(?a = 41.0) }` runs
- **THEN** the answer is `true`

### Requirement: Aggregates and grouping

The system SHALL support `GROUP BY` over variables and expressions, `HAVING`, and `COUNT` (including `*` and `DISTINCT`), `SUM`, `AVG`, `MIN`, `MAX`, `SAMPLE` and `GROUP_CONCAT` (with and without `SEPARATOR`), each with optional `DISTINCT`, with SPARQL 1.1 semantics. An aggregate query without `GROUP BY` SHALL form one group, even over zero rows. Custom aggregates SHALL fail with `Unsupported { feature: "custom aggregate" }`.

#### Scenario: Count per group with HAVING
- **WHEN** alice and bob work at `v:acme` and carol at `v:initech`, and `SELECT ?c (COUNT(?p) AS ?n) WHERE { ?p v:worksAt ?c } GROUP BY ?c HAVING (COUNT(?p) > 1)` runs
- **THEN** exactly the row `(v:acme, 2)` is returned

#### Scenario: Count over no rows
- **WHEN** `SELECT (COUNT(*) AS ?n) WHERE { ?p v:neverUsed ?o }` runs
- **THEN** one row with `n = 0` is returned

#### Scenario: COUNT DISTINCT star
- **WHEN** `SELECT (COUNT(DISTINCT *) AS ?n) WHERE { VALUES (?x ?y) { (1 2) (1 2) (1 3) } }` runs
- **THEN** one row with `n = 2` is returned

### Requirement: Solution modifiers and ordering

The system SHALL apply `ORDER BY` (`ASC`, `DESC`, expression keys), `LIMIT` and `OFFSET` with SPARQL 1.1 semantics. Ordering SHALL compare values: numbers numerically, strings by code point, date-times by instant; across kinds unbound < blank node < IRI < literal. `DISTINCT` combined with an `ORDER BY` key over a variable that is not projected SHALL fail with `Unsupported { feature: "ORDER BY non-projected variable with DISTINCT" }`.

#### Scenario: Numeric order by value
- **WHEN** `(v:a v:rank 9)` and `(v:b v:rank 10)` are live and `SELECT ?s WHERE { ?s v:rank ?r } ORDER BY ?r` runs
- **THEN** the rows are `v:a` then `v:b`

#### Scenario: Descending with LIMIT and OFFSET
- **WHEN** names `"ann"`, `"bob"`, `"cy"`, `"dee"` are live and `SELECT ?n WHERE { ?p v:name ?n } ORDER BY DESC(?n) LIMIT 2 OFFSET 1` runs
- **THEN** the rows are `"cy"` then `"bob"`

#### Scenario: Unbound sorts first
- **WHEN** `SELECT ?p ?a WHERE { ?p v:name ?n OPTIONAL { ?p v:age ?a } } ORDER BY ?a` runs over one person with an age and one without
- **THEN** the person without an age comes first

### Requirement: Built-in functions

The system SHALL support the SPARQL 1.1 operators and the functions `IN`/`NOT IN`, `BOUND`, `IF`, `COALESCE`, `sameTerm`, `isIRI`/`isURI`, `isBlank`, `isLiteral`, `isNumeric`, `STR`, `LANG`, `LANGMATCHES`, `DATATYPE`, `IRI`/`URI`, `STRDT`, `STRLANG`, `STRLEN`, `SUBSTR`, `UCASE`, `LCASE`, `STRSTARTS`, `STRENDS`, `CONTAINS`, `STRBEFORE`, `STRAFTER`, `CONCAT`, `ENCODE_FOR_URI`, `REGEX`, `REPLACE`, `ABS`, `CEIL`, `FLOOR`, `ROUND`, `YEAR`, `MONTH`, `DAY`, `HOURS`, `MINUTES`, `SECONDS`, `TIMEZONE`, `TZ`, `NOW` and the XSD casts to `xsd:string`, `xsd:integer`, `xsd:decimal`, `xsd:double`, `xsd:boolean`, `xsd:date` and `xsd:dateTime`, with the same results as the pinned Rust build. `UCASE` and `LCASE` SHALL use full Unicode case mapping. `NOW` SHALL return one instant for the whole request. `RAND`, `BNODE`, `UUID`, `STRUUID`, `MD5`, `SHA1`, `SHA256`, `SHA384`, `SHA512`, the SPARQL 1.2 language-direction functions and any custom function IRI SHALL fail with `Unsupported { feature }` naming the function, before any read.

#### Scenario: String functions
- **WHEN** `(v:alice v:name "Alice Smith")` is live and `SELECT (UCASE(STRBEFORE(?n, " ")) AS ?f) WHERE { v:alice v:name ?n }` runs
- **THEN** the single row has `f = "ALICE"`

#### Scenario: Unicode case mapping
- **WHEN** `SELECT (UCASE("straße") AS ?u) WHERE {}` runs
- **THEN** the single row has `u = "STRASSE"`

#### Scenario: TZ and TIMEZONE
- **WHEN** `(v:a v:at "2026-09-01T12:00:00+02:00"^^xsd:dateTime)` and `(v:b v:at "2026-09-01T12:00:00"^^xsd:dateTime)` are live and `SELECT ?s (TZ(?t) AS ?z) (TIMEZONE(?t) AS ?d) WHERE { ?s v:at ?t }` runs
- **THEN** `v:a` has `z = "+02:00"` and `d = "PT2H"^^xsd:dayTimeDuration`, and `v:b` has `z = ""` and `d` unbound

#### Scenario: Unsupported function is named
- **WHEN** `SELECT (MD5(?n) AS ?h) WHERE { ?p v:name ?n }` is submitted
- **THEN** the request fails with `Unsupported { feature: "MD5" }`

#### Scenario: Custom function is named
- **WHEN** `SELECT ?x WHERE { ?x v:age ?a FILTER(<http://example.org/fn>(?a)) }` is submitted
- **THEN** the request fails with `Unsupported` whose feature names `http://example.org/fn`

### Requirement: Canonical literals in queries

Query constants SHALL be encoded with the store's canonical value encoding, so matching, joins and `sameTerm` compare encoded values: numbers and booleans collapse to their value whatever their lexical form, which is a deliberate deviation from RDF 1.1 term identity shared with Rust. A date-time SHALL keep its offset (or its absence) as part of the term at millisecond precision, so two date-times are the same term only when instant and offset both match, while comparison operators and `ORDER BY` compare by instant, a date-time without timezone counting as UTC. Language tags SHALL match case-insensitively and be returned lower-cased.

#### Scenario: Integer lexical forms are one term
- **WHEN** `(v:alice v:age 1)` is live and `ASK { v:alice v:age "01"^^xsd:integer }` runs
- **THEN** the answer is `true`

#### Scenario: Date-time offsets are distinct terms but equal instants
- **WHEN** `ASK { FILTER(sameTerm("2026-03-01T12:00:00+02:00"^^xsd:dateTime, "2026-03-01T10:00:00Z"^^xsd:dateTime)) }` runs, and again with `=` in place of `sameTerm`
- **THEN** the first answer is `false` and the second is `true`

#### Scenario: Language tag case
- **WHEN** `(v:alice v:greeting "Hallo"@DE)` was inserted and `SELECT (LANG(?g) AS ?l) WHERE { v:alice v:greeting ?g FILTER(?g = "Hallo"@de) }` runs
- **THEN** one row with `l = "de"` is returned

### Requirement: Blank nodes and skolem IRIs

Blank nodes in query patterns SHALL act as unprojected variables. A skolem IRI written in a query (`urn:tiramemsu:node:<n>`, `urn:tiramemsu:bnode:<n>`, `urn:tiramemsu:stmt:<n>`, `urn:tiramemsu:tx:<t>`) SHALL denote the same anonymous node, blank node, statement or transaction that results render with that IRI.

#### Scenario: Blank node label is not projected
- **WHEN** alice works at a company located in Berlin and `SELECT * WHERE { ?p v:worksAt _:c . _:c v:locatedIn v:berlin }` runs
- **THEN** the result variables are exactly `p` and the row is `p = v:alice`

#### Scenario: Skolem round trip
- **WHEN** a query returns an anonymous node as `urn:tiramemsu:node:7` and `SELECT ?n WHERE { <urn:tiramemsu:node:7> v:name ?n }` runs next
- **THEN** the name of that same node is returned

### Requirement: Property paths

The system SHALL evaluate SPARQL 1.1 property paths. Sequences, alternatives and inverses (`/`, `|`, `^`) SHALL follow the SPARQL 1.1 translation to joins and unions and need no bound endpoint. Paths containing `*`, `+` or `?` SHALL be evaluated by the M3 path engine with endpoint set semantics, in the time scope and graph scope of their block, through virtual hops `sys:subject`, `sys:object`, `sys:predicate` and their inverses, with no hop cap. A recursive path whose endpoints are both unbound by a constant or by a joined pattern SHALL fail with the path engine's `Unsupported`. Negated property sets SHALL fail with `Unsupported { feature: "negated property sets" }`.

#### Scenario: Transitive closure
- **WHEN** `(v:a v:knows v:b)` and `(v:b v:knows v:c)` are live and `SELECT ?x WHERE { v:a v:knows+ ?x } ORDER BY ?x` runs
- **THEN** the rows are `v:b` then `v:c`

#### Scenario: Zero-length path from an unknown constant
- **WHEN** `SELECT ?x WHERE { v:nowhere v:knows* ?x }` runs and `v:nowhere` is in no statement
- **THEN** exactly one row `x = v:nowhere` is returned

#### Scenario: Path through a layer
- **WHEN** `e1 = (v:alice v:worksAt v:acme)` and `(v:belief9 v:supportedBy e1)` are live and `SELECT ?who WHERE { v:belief9 v:supportedBy/sys:subject ?who }` runs
- **THEN** one row `who = v:alice` is returned

#### Scenario: Negated property set rejected
- **WHEN** `SELECT ?x WHERE { v:a !v:knows ?x }` is submitted
- **THEN** the request fails with `Unsupported { feature: "negated property sets" }`

### Requirement: Named graphs as membership tags

A named graph SHALL be a node, and a statement SHALL be a member of graph `g` in a view when the statement and a membership statement `(e sys:inGraph g)` are both visible in that view. With no `FROM`, the default graph SHALL be every visible statement, in a graph or not, each `(s, p, o)` once (a deviation from W3C shared with Rust). `GRAPH <g> { P }` SHALL evaluate `P` over members of `g`; `GRAPH ?g { P }` SHALL yield one solution per solution of `P` and membership, with `?g` bound to the graph, restricted by an earlier binding of `?g`. `FROM <g1> … FROM <gn>` SHALL restrict the default graph to members of any listed graph; `FROM NAMED` SHALL restrict `GRAPH` to the listed graphs. Annotation and reifier patterns inside a `GRAPH` block SHALL use the block's graph. A literal, statement or transaction as a graph name SHALL fail with `InvalidGraphName`; a `tm:` IRI as a graph name SHALL fail as the temporal dataset capability specifies. `GRAPH ?g` over a subquery, or over a block with neither a triple pattern nor a path, SHALL fail with `Unsupported` as in Rust.

#### Scenario: GRAPH with a variable
- **WHEN** `(v:a v:b v:c)` is a member of `<g1>` and of `<g2>` and `SELECT ?g WHERE { GRAPH ?g { v:a v:b v:c } } ORDER BY ?g` runs
- **THEN** the rows are `<g1>` then `<g2>`

#### Scenario: Default graph is the union
- **WHEN** `(v:a v:b v:c)` is in `<g1>` and `(v:d v:e v:f)` is in no graph, and `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o FILTER(?p != sys:inGraph) }` runs
- **THEN** `n = 2`

#### Scenario: FROM restricts the default graph
- **WHEN** the same data is queried with `SELECT ?s FROM <g1> WHERE { ?s ?p ?o }`
- **THEN** exactly one row `s = v:a` is returned

#### Scenario: Recursive path inside a graph
- **WHEN** `(v:a v:knows v:b)` is in `<g1>`, `(v:b v:knows v:c)` is in no graph, and `SELECT ?x WHERE { GRAPH <g1> { v:a v:knows+ ?x } }` runs
- **THEN** exactly one row `x = v:b` is returned

#### Scenario: Literal graph name
- **WHEN** `SELECT * WHERE { GRAPH "g" { ?s ?p ?o } }` is submitted
- **THEN** the request fails with `InvalidGraphName`

### Requirement: Result terms

Every solution value SHALL be an RDF term. Anonymous nodes, blank nodes, statements and transactions SHALL be rendered as the skolem IRIs `urn:tiramemsu:node:<n>`, `urn:tiramemsu:bnode:<n>`, `urn:tiramemsu:stmt:<n>` and `urn:tiramemsu:tx:<t>` with unsigned decimal numbers. Literals SHALL be rendered in canonical lexical form: integers as `xsd:integer`, booleans as `xsd:boolean`, doubles in the canonical shortest round-trip form, plain strings without datatype, language strings with lower-cased tag, and date-times as `xsd:dateTime` in their stored offset (`Z` for zero, no suffix without timezone) with fractional seconds only when the milliseconds are non-zero.

#### Scenario: Statement IRI
- **WHEN** `(v:alice v:worksAt v:acme)` has eid number 12 and `SELECT ?r WHERE { v:alice v:worksAt v:acme ~ ?r }` runs
- **THEN** the row has `r = <urn:tiramemsu:stmt:12>`

#### Scenario: Date-time rendering
- **WHEN** values inserted as `"2026-09-01T14:00:00.000+02:00"`, `"2026-09-01T12:00:00.250+00:00"` and `"2026-09-01T12:00:00"` (all `xsd:dateTime`) are returned
- **THEN** they are `"2026-09-01T14:00:00+02:00"`, `"2026-09-01T12:00:00.250Z"` and `"2026-09-01T12:00:00"`, each typed `xsd:dateTime`

### Requirement: SPARQL JSON results

`SELECT` and `ASK` results SHALL serialise as SPARQL 1.1 Query Results JSON byte-identical to the pinned Rust build for the same rows in the same order: `head.vars` in projection order, one object per row omitting unbound variables, `"type": "uri"` for IRIs and skolem IRIs, `"type": "literal"` with `"xml:lang"` or `"datatype"` (omitted for plain strings), and `{"head":{},"boolean":<b>}` for `ASK`. Row order SHALL be preserved when the query has `ORDER BY`. Only the standard members SHALL appear unless provenance was requested.

#### Scenario: SELECT document
- **WHEN** `SELECT ?p ?age WHERE { ?p v:name ?n OPTIONAL { ?p v:age ?age } }` returns one row `p = v:bob` with `age` unbound and is serialised
- **THEN** the output is `{"head":{"vars":["p","age"]},"results":{"bindings":[{"p":{"type":"uri","value":"urn:tiramemsu:v:bob"}}]}}`

#### Scenario: Typed literal binding
- **WHEN** a row binds `a` to the integer 41
- **THEN** its binding is `{"type":"literal","value":"41","datatype":"http://www.w3.org/2001/XMLSchema#integer"}`

#### Scenario: ASK document
- **WHEN** an `ASK` answers true and is serialised
- **THEN** the output is `{"head":{},"boolean":true}`

### Requirement: CONSTRUCT results

`CONSTRUCT` SHALL return the set of triples obtained by instantiating the template per solution, skipping a template triple whose variable is unbound or whose term is invalid in its position, using fresh blank nodes per solution, and listing each triple once in first-occurrence order. The result SHALL serialise as N-Triples, and as RDF 1.2 N-Triples when a triple term occurs.

#### Scenario: Mapped predicate
- **WHEN** `(v:alice v:worksAt v:acme)` is live and `CONSTRUCT { ?c v:employs ?p } WHERE { ?p v:worksAt ?c }` runs
- **THEN** the result is exactly `<urn:tiramemsu:v:acme> <urn:tiramemsu:v:employs> <urn:tiramemsu:v:alice> .`

#### Scenario: Fresh blank node per solution
- **WHEN** `CONSTRUCT { ?p v:card [ v:name ?n ] } WHERE { ?p v:name ?n }` runs over two named people
- **THEN** four triples are produced and the two card nodes are distinct blank nodes

### Requirement: Query provenance option

The SPARQL entry point with options SHALL accept a provenance flag, off by default; the plain entry point SHALL behave as the one with options at their defaults. With provenance on, each `SELECT` row SHALL carry the ascending, duplicate-free list of eids of the stored statements matched to produce it: the group's patterns, the matched part of an `OPTIONAL`, the `UNION` branch taken, reifier, triple-term and annotation patterns, fixed-length path triples, patterns inside `SERVICE` time scopes (in that scope's view) and, under `GRAPH` or a single `FROM <g>`, the membership statement. A pattern whose eid is not bound SHALL list every visible eid with the matched `(s, p, o)`. `FILTER EXISTS`, `NOT EXISTS`, `MINUS`, virtual predicates and recursive paths SHALL contribute nothing. `DISTINCT` SHALL merge rows into the first one and union their provenance before `OFFSET`/`LIMIT`; groups and subqueries SHALL union the provenance of their input rows. Rows, order and variables SHALL be identical to the same query without provenance. The SPARQL JSON document SHALL gain the member `"provenance"` between `"head"` and `"results"`, an array parallel to the bindings of arrays of `urn:tiramemsu:stmt:<n>` IRIs. `ASK`, `CONSTRUCT`, updates and `SELECT DISTINCT` of no variable in a subquery with provenance SHALL fail before any read with `Unsupported` features `"provenance for ASK"`, `"provenance for CONSTRUCT"`, `"provenance for updates"` and `"provenance with DISTINCT of no variable"`.

#### Scenario: OPTIONAL present and absent
- **WHEN** `e1 = (v:bob v:name "Bob")`, `e2 = (v:bob v:age 41)` and `e3 = (v:carol v:name "Carol")` are live and `SELECT ?p ?a WHERE { ?p v:name ?n OPTIONAL { ?p v:age ?a } }` runs with provenance
- **THEN** the `v:bob` row has provenance `[e1, e2]` and the `v:carol` row has `[e3]`

#### Scenario: One triple lists all its eids
- **WHEN** `(v:alice v:worksAt v:acme)` is live as `e1` and `e2` and `SELECT ?c WHERE { v:alice v:worksAt ?c }` runs with provenance
- **THEN** exactly one row is returned, with provenance `[e1, e2]`

#### Scenario: Retracted statement cited from a time scope
- **WHEN** `e1 = (v:alice v:worksAt v:acme)` was asserted in tx 1 and retracted in tx 2 and `SELECT ?c WHERE { SERVICE <urn:tiramemsu:tm:asOf/1> { v:alice v:worksAt ?c } }` runs with provenance on the current view
- **THEN** one row `c = v:acme` with provenance `[e1]` is returned

#### Scenario: DISTINCT merges before LIMIT
- **WHEN** alice and bob each know two people and `SELECT DISTINCT ?s WHERE { ?s v:knows ?o } ORDER BY ?s LIMIT 1` runs with provenance
- **THEN** exactly one row `s = v:alice` is returned with the eids of both of alice's statements

#### Scenario: JSON member and default off
- **WHEN** a one-row result with provenance `[e5, e7]` is serialised, and the same query runs without the option
- **THEN** the first document has `"provenance":[["urn:tiramemsu:stmt:5","urn:tiramemsu:stmt:7"]]` between `head` and `results` and is otherwise byte-identical to the second, which has no `"provenance"` member

#### Scenario: ASK with provenance
- **WHEN** `ASK { ?s ?p ?o }` runs with provenance
- **THEN** it fails with `Unsupported { feature: "provenance for ASK" }`

#### Scenario: Machine-checked provenance soundness
- **WHEN** the proofs library builds
- **THEN** the property that every eid in a provenance row is a statement visible in the view of a stored triple pattern of the lowered plan and has the content that pattern matched in a solution projecting to the row holds as a theorem whose axioms satisfy the proof policy

### Requirement: Out-of-subset constructs fail before execution

Constructs outside the supported subset SHALL be rejected after parsing and before any store read with `Unsupported { feature }`, using the feature texts of the pinned Rust build, and SHALL return no partial result. This SHALL cover at least `DESCRIBE`, federated `SERVICE` (a variable or a non-`tm:` IRI), custom aggregates, the unsupported functions, negated property sets, the SPARQL 1.2 triple functions and the provenance combinations listed above.

#### Scenario: Federated SERVICE
- **WHEN** `SELECT * WHERE { SERVICE <http://dbpedia.org/sparql> { ?s ?p ?o } }` is submitted
- **THEN** the request fails with `Unsupported { feature: "SERVICE" }` and no row is produced
