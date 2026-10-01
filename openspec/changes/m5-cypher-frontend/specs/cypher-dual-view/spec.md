## Purpose

The Cypher dual view: every statement eid is both a relationship and a node with the implicit label `:Statement`, so Cypher reads and writes layers (statements about statements) while standard Cypher keeps its meaning, over one id space shared with SPARQL.

## ADDED Requirements

### Requirement: Relationship variable in node position
A variable bound to a relationship SHALL be usable in a node position of a later pattern, in the same clause or any later clause where it is in scope, and there SHALL denote the same statement eid. Such a use SHALL NOT count as a relationship position for the isomorphism constraint.

#### Scenario: Belief supporting a relationship
- **WHEN** e1 = `(v:alice v:WORKS_AT v:acme)`, `(v:belief9 rdf:type v:Belief)`, `(v:belief9 v:SUPPORTED_BY e1)` and `(e1 v:confidence 0.8)` are live and `MATCH (a)-[r:WORKS_AT]->(c), (b:Belief)-[:SUPPORTED_BY]->(r) RETURN a, c, r.confidence, b` runs
- **THEN** one row is returned: `v:alice`, `v:acme`, 0.8, `v:belief9`

#### Scenario: Reuse in a later clause
- **WHEN** `MATCH ()-[r:WORKS_AT]->() WITH r MATCH (b)-[:SUPPORTED_BY]->(r) RETURN b` runs on the same store
- **THEN** one row `v:belief9` is returned

#### Scenario: Statement as subject
- **WHEN** `(e1 v:assertedBy v:agent7)` is also live and `MATCH ()-[r:WORKS_AT]->() MATCH (r)-[:assertedBy]->(who) RETURN who` runs
- **THEN** `who` is `v:agent7`

#### Scenario: Node-position use is not a traversal
- **WHEN** `MATCH (a)-[r:WORKS_AT]->(c), (x)-[s]->(r) RETURN count(*) AS n` runs on the first store
- **THEN** `n` is 1, with `s` the `SUPPORTED_BY` statement

### Requirement: Statements reached through relationships are nodes
When a relationship's subject or object is a statement, the node variable at that end SHALL bind to the statement in node form, without having been bound as a relationship first.

#### Scenario: Unbound node variable binds a statement
- **WHEN** `MATCH (b:Belief)-[:SUPPORTED_BY]->(x) RETURN labels(x) AS l, x.confidence AS conf` runs on the first store
- **THEN** `x` is a Node with e1's element id, `l` contains `"Statement"`, and `conf` is 0.8

### Requirement: Implicit Statement label
Every statement in node form SHALL carry the label `Statement` in addition to the labels of its own `rdf:type` statements. `MATCH (s:Statement)` SHALL enumerate each visible statement whose predicate is not in `sys:` exactly once, including property and label statements. `labels()` of a statement node SHALL list `"Statement"` first, then its other labels ascending. An unlabelled node pattern with no binding through the dual view SHALL NOT enumerate statements.

#### Scenario: Enumerate statements
- **WHEN** only `(v:alice v:name "Alice")` and `(v:alice v:knows v:bob)` are live and `MATCH (s:Statement) RETURN count(s) AS n` runs
- **THEN** `n` is 2

#### Scenario: Typed statement
- **WHEN** `(e1 rdf:type v:Claim)` is live and `MATCH (s:Statement:Claim) RETURN labels(s) AS l` runs
- **THEN** `l` is `["Statement", "Claim"]`

#### Scenario: Plain node scan
- **WHEN** only e1 = `(v:alice v:knows v:bob)` and `(e1 v:confidence 0.8)` are live and `MATCH (n) RETURN count(n) AS c` runs
- **THEN** `c` is 2

### Requirement: startNode, endNode and type on either form
`startNode(x)`, `endNode(x)` and `type(x)` SHALL accept a relationship or a statement node and return the statement's subject, its object and its predicate's resolved name. A subject or object that is a statement SHALL be returned as a statement node, and the object of a property statement as its literal value.

#### Scenario: Relationship form
- **WHEN** `MATCH (a)-[r:WORKS_AT]->(c) RETURN startNode(r) = a AS s, endNode(r) = c AS e, type(r) AS t` runs
- **THEN** the row is `true, true, "WORKS_AT"`

#### Scenario: Node form and literal end
- **WHEN** `MATCH (:Belief)-[:SUPPORTED_BY]->(x) RETURN type(x) AS t` runs, and `MATCH (s:Statement) WHERE type(s) = 'name' RETURN endNode(s) AS v` runs on a store with `(v:alice v:name "Alice")`
- **THEN** `t` is `"WORKS_AT"` and `v` is the string `"Alice"`

### Requirement: Properties and relationships of statements
Literal-valued statements whose subject is a statement SHALL be its properties, readable as `r.key` and `x.key`; node- or statement-valued ones SHALL be relationships starting at the statement node, subject to `sys:isEdge`. Nesting SHALL have no depth limit.

#### Scenario: Two-level layer
- **WHEN** e1 = `(v:alice v:WORKS_AT v:acme)`, e7 = `(v:belief9 v:SUPPORTED_BY e1)` and `(e7 v:method "llm-extraction")` are live and `MATCH ()-[r:WORKS_AT]->(), ()-[s:SUPPORTED_BY]->(r) RETURN s.method AS m` runs
- **THEN** `m` is `"llm-extraction"`

### Requirement: Returned form and equality
A variable SHALL be returned in the form of its first binding: a Relationship if first bound in relationship position, a Node labelled `Statement` if first bound in node position. Both forms SHALL carry the same element id and compare equal under `=`. A variable first bound as a node MUST NOT be used in a relationship position; doing so MUST fail with a `Parse` error spanning that use.

#### Scenario: Two forms, one eid
- **WHEN** `MATCH ()-[r:WORKS_AT]->() MATCH (:Belief)-[:SUPPORTED_BY]->(x) RETURN r, x, r = x AS same, elementId(r) = elementId(x) AS sameId` runs
- **THEN** `r` is a Relationship, `x` a `Statement` Node, and `same` and `sameId` are `true`

#### Scenario: Node variable in relationship position
- **WHEN** `MATCH (:Belief)-[:SUPPORTED_BY]->(x) MATCH ()-[x]->() RETURN x` is compiled
- **THEN** it fails with a `Parse` error spanning the second `x`

### Requirement: Standard Cypher keeps its meaning
A query that uses relationship variables only in relationship positions and node variables only in node positions SHALL return the openCypher result over the property-graph projection, with statements appearing as nodes only at relationship ends that are statements or through `:Statement`.

#### Scenario: Layers visible only at statement ends
- **WHEN** e1 = `(v:alice v:knows v:bob)` and `(v:carol v:SUPPORTED_BY e1)` are live
- **THEN** `MATCH (a)-[r]->(b) WHERE NOT b:Statement RETURN count(r) AS c` returns 1 and `MATCH (a)-[r]->(b) RETURN count(r) AS c` returns 2

### Requirement: Writing layers
Write clauses SHALL accept a relationship variable or a statement node in node positions: `CREATE (b)-[:T]->(r)` SHALL create a statement whose object is r's eid, `SET r.key = v` SHALL write a statement whose subject is the eid, and `DELETE x` on a statement node SHALL retract it with cascade.

#### Scenario: Attach a belief
- **WHEN** `` MATCH ({`@id`: 'v:alice'})-[r:WORKS_AT]->() CREATE (b:Belief {text: 'from CV'})-[:SUPPORTED_BY]->(r) `` runs through a transaction handle
- **THEN** a statement `(b, v:SUPPORTED_BY, e1)` is live for the new node b

#### Scenario: Delete through the node form
- **WHEN** `MATCH (:Belief)-[:SUPPORTED_BY]->(x) DELETE x` runs
- **THEN** e1 is retracted and the `SUPPORTED_BY` statement pointing at it is retracted by cascade

### Requirement: One id space with SPARQL
Element ids SHALL be the RDF identities used by the SPARQL front end: an IRI node's IRI, and `urn:tiramemsu:node:<n>`, `urn:tiramemsu:bnode:<n>` and `urn:tiramemsu:stmt:<n>` for anonymous nodes, blank nodes and statements. A node created by Cypher SHALL be visible to SPARQL under its element id, a statement bound by a Cypher relationship variable SHALL be the eid that a SPARQL reifier on the same triple binds, and an element id passed back as `` `@id` `` SHALL denote the same node.

#### Scenario: Cypher node read by SPARQL
- **WHEN** `CREATE (n:Person {name: 'Bob'}) RETURN elementId(n) AS id` runs and returns `urn:tiramemsu:node:12`
- **THEN** SPARQL `SELECT ?n WHERE { <urn:tiramemsu:node:12> v:name ?n }` returns `"Bob"`

#### Scenario: Relationship and reifier agree
- **WHEN** Cypher `MATCH ()-[r:WORKS_AT]->() RETURN elementId(r) AS e` and SPARQL `SELECT ?r WHERE { ?a v:WORKS_AT ?c ~ ?r }` run on the first store
- **THEN** both return e1's skolem IRI `urn:tiramemsu:stmt:<n>`
