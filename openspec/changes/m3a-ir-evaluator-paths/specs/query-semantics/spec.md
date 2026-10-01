## Purpose

The denotational reference semantics of the IR: what rows a query means on a store state under its views and flags. It is the specification every evaluator, planner and front end is proven or tested against.

## ADDED Requirements

### Requirement: Reference semantics
The meaning of a query SHALL be a bag (multiset) of rows defined compositionally per operator on a store state, as stated in this capability. A row SHALL be a finite map from variables to terms. Every execution path (any evaluator, plan, join order or store backend) SHALL return the reference bag; result order SHALL be significant only below a root `OrderLimit`. The reference semantics SHALL itself be executable, so it serves as a test oracle.

#### Scenario: Backends agree
- **WHEN** the same query is executed on a model store and on a SQLite store holding the same statements
- **THEN** both return the reference bag

#### Scenario: Machine-checked evaluator equals the reference semantics
- **WHEN** the proofs library builds
- **THEN** "for every validated query, every plan and every model store state, the evaluator's result equals the reference bag (and the reference list under a root `OrderLimit`)" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Triple pattern matching
A triple pattern SHALL match the statements visible in its own view (per the store's view visibility). Under `BagOfEids` it SHALL yield one row per matching statement; under `SetOfTriples` and without an eid variable it SHALL yield one row per distinct visible `(s, p, o)`; with an eid variable it SHALL yield one row per statement under either flag. A variable repeated within one pattern SHALL require equal values in those positions. With a graph selector `Set(G)` a statement SHALL match once if it has a visible membership in at least one graph of `G`; with `Var(?g)` it SHALL yield one row per visible membership, binding `?g`.

#### Scenario: Repeated variable
- **WHEN** `(?x knows ?x)` is evaluated over `(a knows a)` and `(a knows b)`
- **THEN** only `?x = a` is returned

#### Scenario: Statement in two graphs of the set
- **WHEN** statement `e1` is a member of `g1` and `g2` and a pattern with `Set[g1, g2]` matches it
- **THEN** `e1` produces one row

#### Scenario: One row per membership
- **WHEN** statement `e1` is a member of `g1` and `g2` and a pattern with `Var(?g)` matches it
- **THEN** two rows are produced, with `?g = g1` and `?g = g2`

### Requirement: Virtual predicate patterns
A triple pattern whose predicate is the constant `sys:subject`, `sys:object` or `sys:predicate` SHALL match, for each statement `e` visible in the pattern's view, the triple `(e, that predicate, part of e)`. The constants `tm:txAdded` and `tm:txRetracted` SHALL yield the adding and retracting transaction; `tm:addedAt` and `tm:retractedAt` their commit instants as date-times with offset `Z`; `tm:validFrom` and `tm:validTo` the valid-time bounds as date-times; `tm:retractKind` the retraction kind. An absent value (a live statement's retraction, an unbounded valid time) SHALL produce no triple. A constant object SHALL compare by value (a date-time by instant). A variable predicate SHALL NOT match virtual triples, and virtual triples SHALL be computed from statement rows, never from stored triples.

#### Scenario: Subject of a statement
- **WHEN** `e1 = (alice worksAt acme)` is live and `(e1 sys:subject ?s)` is evaluated under `Now`
- **THEN** the only row is `?s = alice`

#### Scenario: Live statement has no retraction
- **WHEN** `(e1 tm:txRetracted ?t)` is evaluated for a live `e1` under `Now`
- **THEN** no row is returned

#### Scenario: Variable predicate ignores virtual triples
- **WHEN** `(e1 ?p ?o)` is evaluated for a statement `e1` with no stored layers
- **THEN** no row is returned

### Requirement: Compatibility and missing values
Two rows SHALL be compatible when they agree on every variable both bind. Under `Unbound`, a variable bound in one row and absent from the other SHALL not prevent compatibility. Under `Null3VL`, a variable that both inputs can bind SHALL join only when both rows bind it to equal values; a missing value (NULL) SHALL equal nothing, itself included. Term equality in joins SHALL be identity of terms (equal canonical encodings), not value comparison.

#### Scenario: Unbound joins with anything
- **WHEN** under `Unbound` a row with `?x` absent is joined with a row `?x = a`
- **THEN** the joined row binds `?x = a`

#### Scenario: Null never joins
- **WHEN** under `Null3VL` a row with `?x` null is joined on `?x` with a row `?x = a`
- **THEN** no joined row is produced

#### Scenario: Numerically equal but distinct terms
- **WHEN** a join compares `"1"^^xsd:integer` with `"1.0"^^xsd:decimal` stored as distinct terms
- **THEN** they are not compatible

### Requirement: Relational operators
`Join` SHALL be the bag natural join over compatible rows. `LeftJoin(l, r, c)` SHALL return each merge of an `l` row with a compatible `r` row for which `c` is true, and each `l` row with no such `r` row unchanged. `Union` SHALL be bag union. `Filter(c)` SHALL keep exactly the rows for which `c` is true. `Extend(v := e)` SHALL add `v` when `e` has a value and leave `v` unbound (NULL under `Null3VL`) when `e` errors. `Project` SHALL restrict rows to its variables and, when distinct, keep one copy of each row. Under `RelIsomorphism`, rows in which two patterns of one match group bind the same statement SHALL be removed.

#### Scenario: Optional absent
- **WHEN** `LeftJoin((?x worksAt ?c), (?c locatedIn ?city))` is evaluated and `acme` has no location
- **THEN** the row for `acme` is returned with `?city` unbound

#### Scenario: Union keeps duplicates
- **WHEN** both branches of a `Union` return the row `?x = a`
- **THEN** the result holds that row twice

#### Scenario: Machine-checked join algebra
- **WHEN** the proofs library builds
- **THEN** "Join is invariant under permutation of its inputs, associative, and has `Join[]` as unit, as bags" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Three-valued expression evaluation
An expression SHALL evaluate to a term or to an error. An unbound variable (`Unbound`) or NULL (`Null3VL`), a type error, and integer division by zero SHALL be errors. `AND`, `OR` and `NOT` SHALL follow the three-valued (Kleene) tables with error as the third value: `false AND error = false`, `true OR error = true`, `NOT error = error`. A filter SHALL keep a row only when the effective boolean value of its condition is true. `BOUND`, `COALESCE`, `IF` and `sameTerm` SHALL follow SPARQL 1.1. `EXISTS q` SHALL be true exactly when the reference bag of `q` has a row compatible with the current row.

#### Scenario: Error in a filter drops the row
- **WHEN** `Filter(?age > 30, …)` meets a row where `?age` is the string `"old"`
- **THEN** the row is dropped and no error is raised

#### Scenario: Disjunction absorbs an error
- **WHEN** `Filter(?age > 30 || ?vip = true, …)` meets a row with `?age` unbound and `?vip = true`
- **THEN** the row is kept

### Requirement: Arithmetic and value comparison
Integer and decimal arithmetic SHALL be exact. Double arithmetic SHALL use hardware IEEE binary64 operations, which are part of the trusted base and opaque to the proofs. Numeric comparison SHALL compare by value across integer, decimal and double; date-times SHALL compare by instant; strings by code point.

#### Scenario: Mixed numeric comparison
- **WHEN** `Filter(?x < 2.5)` meets `?x = 2` (an integer)
- **THEN** the row is kept

#### Scenario: Double arithmetic matches Rust
- **WHEN** `Extend(?y := ?x * 0.1)` is evaluated on a double `?x` by the Lean build and the Rust oracle
- **THEN** both bind the same IEEE bit pattern

### Requirement: Aggregation
`Aggregate(G, aggs)` SHALL partition the input bag by the values of `G` and produce one row per group binding `G` and each aggregate output. With empty `G` and an empty input it SHALL produce one row (`COUNT` = 0, other aggregates unbound); with non-empty `G` and an empty input, no rows. A distinct aggregate SHALL use the set of argument values. Every aggregate except `COUNT(*)` SHALL ignore rows whose argument is missing or errors; `SUM` and `AVG` SHALL use numeric values; `MIN` and `MAX` SHALL use the value sort order of `OrderLimit`. Every aggregate SHALL be a function of the group's multiset: `SAMPLE` SHALL return the least value and `GROUP_CONCAT` SHALL concatenate, and double `SUM`/`AVG` SHALL fold, in the canonical value order.

#### Scenario: Count over an empty input
- **WHEN** `Aggregate([], [COUNT(*) as ?n], (?x worksAt neverSeen))` is evaluated
- **THEN** one row with `?n = 0` is returned

#### Scenario: Grouped aggregate over an empty input
- **WHEN** `Aggregate([?c], [COUNT(*) as ?n], (?x worksAt neverSeen))` is evaluated
- **THEN** no row is returned

#### Scenario: Machine-checked order independence of aggregates
- **WHEN** the proofs library builds
- **THEN** "an aggregate's result depends only on the multiset of its group's rows" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Ordering, skip and limit
`OrderLimit(keys, skip, limit)` SHALL sort rows by the keys in order, each by the value sort order of the codec (byte-identical to the Rust sort key), descending keys reversed, an unbound or erroring key first in ascending order. Rows equal on every key SHALL be ordered by the canonical row order (each cell's sort key in variable order, missing first). Then `skip` rows SHALL be dropped and at most `limit` kept.

#### Scenario: Strings sort by value, not by id
- **WHEN** names `"bob"` and `"alice"` were stored in that order and rows are ordered by name ascending
- **THEN** `"alice"` comes first

#### Scenario: Ties are deterministic
- **WHEN** two rows tie on every key and the query is evaluated under two different join orders
- **THEN** both evaluations return the rows in the same order

### Requirement: Stable historical results
The reference bag of a query whose patterns all use `AsOf(t)` views SHALL NOT change when transactions after `t` commit.

#### Scenario: Recompute after later writes
- **WHEN** a query under `AsOf(150)` is evaluated, then 50 more transactions commit, then it is evaluated again
- **THEN** both evaluations return the same bag

#### Scenario: Machine-checked stability
- **WHEN** the proofs library builds
- **THEN** "extending a store state by later commits leaves the reference bag of every query under `AsOf(t)` unchanged, for `t` up to the earlier state's last transaction" holds as a theorem whose axioms satisfy the proof policy
