## Purpose

The physical evaluation of joins over the store's sorted index range scans: the scan interface every join algorithm consumes, index choice, index nested-loop evaluation, and the rewrites that push filters and bindings into scans, all proven to compute the reference natural join whatever order a planner picks.

## ADDED Requirements

### Requirement: Sorted range-scan interface
The evaluator SHALL read statements only through the store's range-scan interface: given an index order (`spo`, `pos` or `osp`), a view and a key prefix of ObjectIds, a scan SHALL return exactly the statements visible in the view whose leading key columns equal the prefix, in ascending key order with the eid as the last column. The interface SHALL also offer a seek that returns the least next-column key at or after a given key among those statements, and a lookup by eid. Join algorithms (this capability's nested loop and the Leapfrog Triejoin of a later change) SHALL consume only this interface.

#### Scenario: Prefix scan in key order
- **WHEN** a scan on `pos` under `Now` with prefix `(worksAt)` runs over statements whose objects are `acme`, `globex`, `acme`
- **THEN** it returns the three statements ordered by object, then subject, then eid

#### Scenario: Seek
- **WHEN** a seek on `spo` with prefix `(alice)` asks for the least predicate at or after `knows`
- **THEN** it returns the smallest visible predicate of `alice` that is not below `knows`, or nothing

#### Scenario: Machine-checked model scans
- **WHEN** the proofs library builds
- **THEN** "on the model store, a scan returns exactly the visible statements matching the prefix, sorted by the order's key, and a seek returns the least matching next key" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Index choice
For a triple pattern whose eid is bound, the evaluator SHALL use the lookup by eid. Otherwise it SHALL scan the index order whose key prefix is exactly the set of bound positions (every subset of `{s, p, o}` is a prefix of one of `spo`, `pos`, `osp`), in the live family under `Now` and the history family under `AsOf` and `History`; a valid-time selector SHALL filter the scanned statements. Under `SetOfTriples` without an eid variable, consecutive statements with equal `(s, p, o)` in scan order SHALL produce one row.

#### Scenario: Subject and object bound
- **WHEN** `(alice ?p acme)` is evaluated
- **THEN** the evaluator scans `osp` with prefix `(acme, alice)`

#### Scenario: Live family under Now
- **WHEN** a pattern under `Now` is scanned on a store with many retracted statements of its predicate
- **THEN** the scan uses the live family and reads no retracted statement

#### Scenario: Machine-checked set-of-triples deduplication
- **WHEN** the proofs library builds
- **THEN** "removing consecutive equal `(s, p, o)` from a scan yields each distinct visible `(s, p, o)` exactly once" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Index nested-loop evaluation
A `Join` whose inputs are triple patterns SHALL be evaluated as an index nested loop in a chosen order: each pattern, in turn, SHALL be scanned once per partial row with every position bound by a constant or by an earlier pattern used as a key prefix. Non-pattern inputs SHALL be evaluated by their operator and joined on their shared variables. The order SHALL be chosen by a planner from bound positions and per-predicate counts; the choice SHALL affect only speed.

#### Scenario: Chain join reads by prefix
- **WHEN** `Join[(alice knows ?b), (?b worksAt ?c)]` is evaluated in that order
- **THEN** the second pattern is scanned on `spo` with prefix `(b, worksAt)` once per row of the first

#### Scenario: Statistics change only speed
- **WHEN** the per-predicate counts are stale or wrong
- **THEN** the query returns the same bag

### Requirement: Join-order independence
For every list of triple patterns and every permutation of it, index nested-loop evaluation in that order SHALL return the reference natural join of the patterns, as a bag. This statement, over the sorted range-scan interface, is the contract any join algorithm and any planner order SHALL satisfy, so a planner needs no proof of its own.

#### Scenario: Every order agrees
- **WHEN** a four-pattern join is evaluated in all 24 orders
- **THEN** all 24 results equal the reference bag

#### Scenario: Machine-checked order independence
- **WHEN** the proofs library builds
- **THEN** "for every pattern list, every permutation and every model store state, index nested-loop evaluation equals the reference natural join" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Filter push-down and binding passing
The evaluator SHALL push a filter conjunct into the earliest pattern position after which all of its variables are certainly bound, and turn an equality with a constant into a key-prefix constraint. It SHALL pass bindings sideways from the left side of a join or optional into the right side only for variables the right side certainly binds itself. A conjunct that mentions a variable that is only possibly bound SHALL stay above the join. These rewrites SHALL never change the reference bag.

#### Scenario: Constant equality becomes a prefix
- **WHEN** `Filter(?c = acme, (?x worksAt ?c))` is evaluated
- **THEN** the pattern is scanned on `pos` with prefix `(worksAt, acme)`

#### Scenario: Optional variable is not pushed
- **WHEN** `Filter(!BOUND(?city), LeftJoin((?x worksAt ?c), (?c locatedIn ?city)))` is evaluated
- **THEN** the filter is applied after the optional, and companies without a location are returned

#### Scenario: Machine-checked push-down soundness
- **WHEN** the proofs library builds
- **THEN** "filter push-down and sideways binding passing preserve the reference bag of every validated query" holds as a theorem whose axioms satisfy the proof policy
