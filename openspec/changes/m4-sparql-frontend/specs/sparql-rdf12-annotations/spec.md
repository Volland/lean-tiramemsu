## Purpose

Maps the SPARQL 1.2 triple-term, reifier and annotation syntax onto tiramemsu's addressable statements: a reifier is a statement eid and an annotation is a layer triple whose subject is that eid, nested to any depth, in queries, updates and `CONSTRUCT` output.

## ADDED Requirements

### Requirement: Reifiers bind statement eids

In a query pattern, `s p o ~ ?r`, `<< s p o ~ ?r >>` and `?r rdf:reifies <<( s p o )>>` SHALL each bind `?r` to the eid of a statement with content `(s, p, o)` visible in the pattern's view, one solution per eid. A blank-node reifier, or an omitted one as in `<< s p o >>`, SHALL act as an unprojected variable. A reifier constant that is not a visible statement with that content SHALL match nothing, without error.

#### Scenario: Reifier binds the eid
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` is live and `SELECT ?r WHERE { v:alice v:worksAt v:acme ~ ?r }` runs
- **THEN** one row is returned whose `r` is the statement IRI of e1

#### Scenario: Explicit rdf:reifies form
- **WHEN** the same data is queried with `SELECT ?r WHERE { ?r rdf:reifies <<( v:alice v:worksAt v:acme )>> }`
- **THEN** the same single row is returned

#### Scenario: One row per episode
- **WHEN** `(v:alice v:worksAt v:acme)` is live as e1 and e2 and `SELECT ?r WHERE { v:alice v:worksAt ?c ~ ?r }` runs
- **THEN** two rows are returned, for e1 and e2

#### Scenario: Reified triple as subject
- **WHEN** e1 carries `(e1 v:confidence 0.8)` and `SELECT ?c WHERE { << v:alice v:worksAt v:acme >> v:confidence ?c }` runs
- **THEN** one row `c = 0.8` typed `xsd:decimal` is returned

#### Scenario: Reifier constant that is not a statement
- **WHEN** `ASK { v:alice v:worksAt v:acme ~ v:someIri }` runs
- **THEN** the answer is `false` and no error is raised

### Requirement: Annotation blocks are required layer patterns

`s p o ~ ?r {| q1 v1 ; q2 v2 |}`, with or without an explicit reifier, SHALL match only when the statement and every annotation triple `(eid q1 v1)`, `(eid q2 v2)` are visible in the same view and graph scope. A missing annotation SHALL remove the solution unless the query wraps it in `OPTIONAL`.

#### Scenario: Annotation values read
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` has `(e1 v:confidence 0.8)` and `(e1 v:source v:crawler)` and `SELECT ?c ?s WHERE { v:alice v:worksAt v:acme {| v:confidence ?c ; v:source ?s |} }` runs
- **THEN** one row `c = 0.8`, `s = v:crawler` is returned

#### Scenario: Missing annotation removes the solution
- **WHEN** `(v:bob v:worksAt v:acme)` has no annotation and `SELECT ?p WHERE { ?p v:worksAt v:acme {| v:confidence ?c |} }` runs
- **THEN** `v:bob` is not returned

#### Scenario: Optional annotation
- **WHEN** `SELECT ?p ?c WHERE { ?p v:worksAt v:acme ~ ?r OPTIONAL { ?r v:confidence ?c } }` runs over the same data
- **THEN** `v:bob` is returned with `c` unbound

### Requirement: Layers nest to any depth

Reifiers and annotations SHALL nest: an annotation triple MAY carry its own reifier and annotation block, and a triple term MAY occur inside another. An eid bound by a reifier SHALL be usable in any subject or object position of another pattern.

#### Scenario: Annotation on an annotation
- **WHEN** e1 = `(v:alice v:worksAt v:acme)`, e2 = `(e1 v:confidence 0.8)` and e3 = `(e2 v:method "llm-extraction")` are live and `SELECT ?c ?m WHERE { v:alice v:worksAt v:acme {| v:confidence ?c ~ ?r2 {| v:method ?m |} |} }` runs
- **THEN** one row `c = 0.8`, `m = "llm-extraction"` is returned

#### Scenario: Nested triple term
- **WHEN** e5 = `(v:bob v:says e1)` and e6 = `(v:carol v:doubts e5)` are live and `SELECT ?who WHERE { ?who v:doubts <<( v:bob v:says <<( v:alice v:worksAt v:acme )>> )>> }` runs
- **THEN** one row `who = v:carol` is returned

#### Scenario: Belief referencing a fact
- **WHEN** `(v:belief9 v:supportedBy e1)` is live and `SELECT ?b WHERE { ?b v:supportedBy ?r . ?r rdf:reifies <<( v:alice v:worksAt ?c )>> }` runs
- **THEN** one row `b = v:belief9` is returned

### Requirement: Triple terms denote statements

A triple term `<<( s p o )>>` as the object of a pattern whose predicate is not `rdf:reifies` SHALL match an object that is the eid of a visible statement with content `(s, p, o)`, once per distinct referring triple unless an eid is bound.

#### Scenario: Triple term in object position
- **WHEN** `(v:belief9 v:supportedBy e1)` is live with e1 = `(v:alice v:worksAt v:acme)` and `ASK { v:belief9 v:supportedBy <<( v:alice v:worksAt v:acme )>> }` runs
- **THEN** the answer is `true`

### Requirement: rdf:reifies is virtual

`rdf:reifies` SHALL never be stored, and a variable-predicate pattern SHALL NOT return `rdf:reifies` rows. `?r rdf:reifies X` with `X` not a triple term SHALL fail with `Unsupported { feature: "rdf:reifies without triple term" }`; a variable predicate with a triple-term object with `Unsupported { feature: "variable predicate with triple term" }`; a triple term in `VALUES` with `Unsupported { feature: "triple term in VALUES" }`. `TRIPLE`, `SUBJECT`, `PREDICATE`, `OBJECT` and `isTRIPLE` SHALL fail with `Unsupported` naming the function. A triple term in subject position SHALL be a `Parse` error, as SPARQL 1.2 requires.

#### Scenario: Variable predicate does not see rdf:reifies
- **WHEN** only e1 = `(v:alice v:worksAt v:acme)` is live and `SELECT ?p WHERE { ?s ?p ?o }` runs
- **THEN** exactly one row `p = v:worksAt` is returned

#### Scenario: rdf:reifies with a variable object
- **WHEN** `SELECT ?t WHERE { ?r rdf:reifies ?t }` is submitted
- **THEN** the request fails with `Unsupported { feature: "rdf:reifies without triple term" }`

#### Scenario: Triple function
- **WHEN** `SELECT ?x WHERE { ?x v:about ?o FILTER(isTRIPLE(?o)) }` is submitted
- **THEN** the request fails with `Unsupported { feature: "isTRIPLE" }`

### Requirement: Reifiers follow the pattern's view

A reifier SHALL bind only eids visible in its pattern's view: retracted eids under history, eids live at `t` under as of `t`. Annotation triples SHALL be read in the base triple's view unless a time `SERVICE` scope around them says otherwise.

#### Scenario: History shows a superseded fact and its replacement
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` was superseded by e10 with a new valid start and `SELECT ?r FROM <urn:tiramemsu:tm:history> WHERE { v:alice v:worksAt v:acme ~ ?r }` runs
- **THEN** two rows are returned, for e1 and e10, while the current view returns only e10

#### Scenario: Cascaded annotation before its retraction
- **WHEN** e1 and its annotation e2 were retracted in tx 9 and `SELECT ?c WHERE { v:alice v:worksAt v:acme {| v:confidence ?c |} }` runs on the view as of tx 8
- **THEN** one row `c = 0.8` is returned

### Requirement: One eid across surfaces

The eid bound by a reifier SHALL be the statement identity returned by the Lean API for that statement and accepted back as its statement IRI.

#### Scenario: API eid equals reifier
- **WHEN** the API asserts `(v:alice v:worksAt v:acme)` and returns eid number N, and `SELECT ?r WHERE { v:alice v:worksAt v:acme ~ ?r }` runs
- **THEN** `r = <urn:tiramemsu:stmt:N>`, and `SELECT ?c WHERE { <urn:tiramemsu:stmt:N> v:confidence ?c }` reads that statement's annotations

### Requirement: Inserted annotations become layer triples on the eid

In `INSERT DATA` and insert templates, a triple with a reifier or annotation block SHALL assert `(s, p, o)` idempotently, the reifier SHALL denote that statement's eid (new or existing), and each annotation triple SHALL be asserted idempotently with that eid as subject. A reified triple or triple term used as a subject or object SHALL assert its triple idempotently and use its eid there. This is a deliberate deviation from RDF 1.2, shared with Rust: every reifier is a stored, asserted statement, and no `rdf:reifies` triple is stored. A variable reifier bound by `WHERE` SHALL let the template attach triples to that eid.

#### Scenario: INSERT DATA with annotation
- **WHEN** `INSERT DATA { v:alice v:worksAt v:acme {| v:confidence 0.8 ; v:source v:crawler |} }` is submitted on an empty store
- **THEN** exactly three statements are live: e1 = `(v:alice v:worksAt v:acme)`, `(e1 v:confidence 0.8)` and `(e1 v:source v:crawler)`

#### Scenario: Annotation insert is idempotent
- **WHEN** the same request is submitted again
- **THEN** no statement is created and the report lists all three eids as existing

#### Scenario: Reference to a reified triple asserts it
- **WHEN** `INSERT DATA { v:belief9 v:supportedBy << v:alice v:worksAt v:acme >> }` is submitted on an empty store
- **THEN** e1 = `(v:alice v:worksAt v:acme)` and `(v:belief9 v:supportedBy e1)` are both live

#### Scenario: Template attaches to a bound eid
- **WHEN** e1 and e2 are live episodes of `(v:alice v:worksAt v:acme)` and `INSERT { ?r v:reviewed true } WHERE { v:alice v:worksAt v:acme ~ ?r }` is submitted
- **THEN** `(e1 v:reviewed true)` and `(e2 v:reviewed true)` are both asserted

### Requirement: Reifier restrictions in updates

In an update, a reifier SHALL be a blank node, a variable bound to a statement eid, or the statement IRI of a stored statement whose content equals the reified triple. Any other reifier SHALL fail the request with `Unsupported { feature: "reifier that is not a statement" }`; one reifier for two different triples SHALL fail with `Unsupported { feature: "reifier of more than one triple" }`. Nothing SHALL be written in either case.

#### Scenario: IRI reifier rejected
- **WHEN** `INSERT DATA { v:alice v:worksAt v:acme ~ v:myReifier {| v:confidence 0.8 |} }` is submitted
- **THEN** the request fails with `Unsupported { feature: "reifier that is not a statement" }` and nothing is written

#### Scenario: Statement IRI reifier accepted
- **WHEN** e1 = `(v:alice v:worksAt v:acme)` is live with number 12 and `INSERT DATA { v:alice v:worksAt v:acme ~ <urn:tiramemsu:stmt:12> {| v:confidence 0.8 |} }` is submitted
- **THEN** `(e1 v:confidence 0.8)` is asserted and e1 is reported as existing

#### Scenario: One reifier for two triples
- **WHEN** `INSERT DATA { _:r rdf:reifies <<( v:a v:b v:c )>> . _:r rdf:reifies <<( v:d v:e v:f )>> }` is submitted
- **THEN** the request fails with `Unsupported { feature: "reifier of more than one triple" }`

### Requirement: Deletes through reifiers are eid-precise

In a delete template, a triple whose reifier is bound to an eid SHALL retract exactly that eid, with cascade, and no other eid with the same content. A delete template triple whose subject is a bound eid SHALL retract the matching layer triples and leave the eid live.

#### Scenario: Retract one episode only
- **WHEN** e1 and e2 are live episodes of `(v:alice v:worksAt v:acme)`, only e1 has `(e1 v:source v:crawler)`, and `DELETE { ?s v:worksAt ?o ~ ?r } WHERE { ?s v:worksAt ?o ~ ?r {| v:source v:crawler |} }` is submitted
- **THEN** e1 (explicit) and its annotation (cascade) are retracted and e2 stays live

#### Scenario: Retract an annotation only
- **WHEN** e1 has `(e1 v:confidence 0.8)` and `DELETE { ?r v:confidence ?c } WHERE { v:alice v:worksAt v:acme ~ ?r {| v:confidence ?c |} }` is submitted
- **THEN** the confidence statement is retracted and e1 stays live

### Requirement: CONSTRUCT emits RDF 1.2 reification

A `CONSTRUCT` template with a reifier or annotation SHALL produce per solution the triple `(s, p, o)`, the triple `(reifier rdf:reifies <<( s p o )>>)` and one triple per annotation with the reifier as subject; an eid in any position SHALL render as its statement IRI.

#### Scenario: Export an annotated fact
- **WHEN** e1 (number 12) = `(v:alice v:worksAt v:acme)` has `(e1 v:confidence 0.8)` and `CONSTRUCT { ?s v:worksAt ?o ~ ?r {| v:confidence ?c |} } WHERE { ?s v:worksAt ?o ~ ?r {| v:confidence ?c |} }` runs
- **THEN** the result is exactly `v:alice v:worksAt v:acme`, `<urn:tiramemsu:stmt:12> rdf:reifies <<( v:alice v:worksAt v:acme )>>` and `<urn:tiramemsu:stmt:12> v:confidence 0.8`, serialised with the RDF 1.2 N-Triples triple-term syntax
