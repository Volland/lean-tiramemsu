## Purpose

Evaluates a basic graph pattern of stored triple patterns with a worst-case-optimal Leapfrog Triejoin over the store's sorted index range scans, with results proven bag-equal to the reference join semantics for every variable order.

## ADDED Requirements

### Requirement: LFTJ equals the reference join for every variable order
For a join region of stored triple patterns, each under its own view, and for every variable order that lists each of the region's variables exactly once (eid variables included), the LFTJ operator SHALL return a bag of solution mappings equal to the reference natural-join denotation of the region. Equal means the same mappings with the same multiplicities, in any order. The operator SHALL accept any pattern mix of constants, variables, repeated variables within a pattern, variable predicates and eid variables. A region in which some pattern denotes the empty bag (for example a constant missing from the term dictionary) SHALL return the empty bag.

#### Scenario: Triangle under every variable order
- **WHEN** the region `?a :k ?b . ?b :k ?c . ?c :k ?a` is evaluated on a store holding the edges `1→2`, `2→3`, `3→1`, `2→1` under each of the six orders of `a, b, c`
- **THEN** every evaluation returns the three mappings `{a=1,b=2,c=3}`, `{a=2,b=3,c=1}`, `{a=3,b=1,c=2}`, each once

#### Scenario: Repeated variable within a pattern
- **WHEN** the region `?x :p ?x . ?x :q ?y` is evaluated on a store holding `(n1 :p n1)`, `(n2 :p n3)`, `(n1 :q n5)`, `(n2 :q n6)`
- **THEN** the result is exactly `{x=n1, y=n5}`

#### Scenario: Eid variable used as a join variable
- **WHEN** the region binds `?r` as the eid of `?x :knows ?y` and joins it with `?r :confidence ?c`, and the store holds one `knows` statement with a `confidence` statement about it
- **THEN** the result is one mapping that binds `?r` to that statement's eid and `?c` to its confidence, for every variable order of `x, y, r, c`

#### Scenario: Missing constant short-circuits
- **WHEN** a region contains a pattern whose constant IRI is not in the term dictionary
- **THEN** the result is empty for every variable order and no further range scans are issued for the region

#### Scenario: Agrees with the reference evaluator on random inputs
- **WHEN** property tests generate random stores, random regions of one to six patterns and random valid variable orders, and run them on the model store and on the SQLite store
- **THEN** both stores return results bag-equal to the reference denotation

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** bag-equality with the reference denotation, for every duplicate-free variable order that covers the region's variables and every admissible access choice, holds as a theorem whose only hypothesis about the store is the range-scan contract, and its axioms satisfy the proof policy

### Requirement: Leapfrog intersection is exact
At each variable level, the operator SHALL intersect the candidate keys of every pattern that contains the variable by leapfrogging: repeatedly seeking the iterator with the smallest key to the largest key among the iterators. It SHALL emit exactly the keys present in all of them, in increasing key order, each once. Key order SHALL be the order of the store's range scans: signed 64-bit order of the encoded ObjectIds.

#### Scenario: Intersection of three sorted key sets
- **WHEN** one level intersects the key sets `{1, 4, 7, 9}`, `{4, 5, 9}` and `{0, 4, 9, 12}`
- **THEN** the level yields `4` and then `9`, and nothing else

#### Scenario: Negative and extreme keys
- **WHEN** a level intersects key sets that contain negative ObjectIds and the largest signed 64-bit value
- **THEN** keys are compared in signed order and the largest value is yielded when common, without overflow

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** sortedness of the output and membership-iff-in-every-input hold as a theorem whose axioms satisfy the proof policy

### Requirement: Trie iterators are faithful under every view
For each pattern, the operator SHALL build a trie over the pattern's variables in the chosen order. It SHALL read the pattern's view family (`live_*` under `Now`, `hist_*` under `AsOf` and `History`) through a range scan on `spo`, `pos` or `osp`, or through an in-memory sorted copy of the pattern's rows when no index order fits. At every level, the keys the trie offers SHALL be exactly the distinct values of that variable among the pattern's rows that match the view (transaction time and valid time) and the already bound variables. Patterns of one region SHALL be allowed to carry different views.

#### Scenario: Mixed views in one region
- **WHEN** a triangle region has one pattern under `Now`, one under `AsOf(t)` and one under `valid At(d)`, and the store holds edges retracted after `t` and edges whose valid interval excludes `d`
- **THEN** each pattern contributes exactly the rows its own view admits, and the result equals the reference denotation

#### Scenario: Retracted and re-asserted rows
- **WHEN** a statement is asserted, retracted and re-asserted, and a region reads it under `History`
- **THEN** the pattern's level offers its key once, and its leaf group holds both rows

#### Scenario: Three-variable pattern with a non-rotation order
- **WHEN** a pattern `?s ?p ?o` must be read under the order `s, o, p`, which no index order provides
- **THEN** the operator reads it through a sorted in-memory copy and the result still equals the reference denotation

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** under the range-scan contract, every iterator kind (index range, index with existence check, in-memory sorted copy) offers exactly the projected key set at every level and every seek returns the least offered key not below the target, as theorems whose axioms satisfy the proof policy

### Requirement: Bag multiplicities are preserved
The operator SHALL emit each joined mapping with multiplicity equal to the product of the multiplicities of its per-pattern rows. A pattern's multiplicity follows the query's `graph_set` flag: under `SetOfTriples` without an eid variable, rows with equal `(s, p, o)` count once. Under `BagOfEids` each matching row counts once. With an eid variable, each row is its own mapping.

#### Scenario: Duplicate statements under SetOfTriples
- **WHEN** two live eids carry the same `(alice :knows bob)` and a region containing `?a :knows ?b` runs under `SetOfTriples`
- **THEN** each result mapping that uses this triple appears once

#### Scenario: Duplicate statements under BagOfEids
- **WHEN** the same store and region run under `BagOfEids`
- **THEN** each such mapping appears twice

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the per-pattern leaf multiplicity equals the reference pattern denotation's multiplicity under both `graph_set` values, as a theorem whose axioms satisfy the proof policy

### Requirement: LFTJ is total and detects contract violations
The operator SHALL terminate on every store and every input, without a search budget that can run out. Every seek SHALL be checked: a range scan that returns a key below the requested lower bound, or fails to advance on a successor seek, SHALL abort the query with a store-contract error. The query SHALL NOT return rows after a violation. Under the store contract, this error SHALL never occur.

#### Scenario: Out-of-order store
- **WHEN** the operator runs over a test store that returns keys out of order for one range scan
- **THEN** the query fails with a store-contract error and returns no rows

#### Scenario: Machine-checked
- **WHEN** the runtime and proofs libraries build under the proof-policy gates
- **THEN** the operator is defined without `partial`, `unsafe` or fuel, termination is accepted by Lean, and the absence of the store-contract error under the range-scan contract holds as a theorem whose axioms satisfy the proof policy

### Requirement: Results stream with bounded working memory
The operator SHALL deliver mappings to the consuming operator one at a time, without first collecting the whole result. Its working memory SHALL be bounded by the region's size, one bounded read-ahead buffer per open level iterator, the current leaf groups, and any in-memory sorted pattern copies.

#### Scenario: Large triangle count
- **WHEN** the triangle count of the 3 × 600 layered fixture (about 3.24 million mappings) is aggregated with `COUNT`
- **THEN** the peak memory of the query stays below a fixed bound that does not grow with the number of mappings, and the count is exact

### Requirement: Compatible with the Rust build
On any database file both builds can open, a query whose join region runs through LFTJ SHALL return a result bag-equal to the pinned Rust build's result. Deviation from Rust (D6): Rust evaluates cyclic patterns as SQLite nested loops, so the row order of a result without `ORDER BY` MAY differ from Rust's. Only the bag of rows is compatible.

#### Scenario: Triangle fixtures against the oracle
- **WHEN** the uniform, hub-and-spoke and layered triangle fixtures are counted by the Lean build and by the pinned Rust build on the same `.db` file
- **THEN** the counts are equal

#### Scenario: Unordered row order
- **WHEN** a cyclic query without `ORDER BY` runs on both builds
- **THEN** the differential harness compares the results as multisets and passes even if row order differs
