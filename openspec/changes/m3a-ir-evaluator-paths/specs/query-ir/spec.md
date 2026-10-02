## Purpose

The logical query algebra that every front end (the Lean API now, SPARQL in M4, Cypher in M5) produces and the proven evaluator consumes: its operators, pattern positions, per-pattern time views, graph selectors, semantic flags and the structural rules a query must satisfy.

## ADDED Requirements

### Requirement: Operator set
The IR SHALL consist of three leaf operators and eight relational operators:
- leaves: a triple pattern, a path pattern, and inline values (a variable list and rows of optional constants, an absent cell being undefined);
- `Join` of any number of inputs (the empty join is the unit relation: one row with no bindings);
- `LeftJoin(left, right, cond?)`, `Union` of any number of inputs, `Filter(cond, input)`, `Extend(var := expr, input)`;
- `Aggregate(group vars, aggregates, input)`, `Project(vars, distinct, input)`, `OrderLimit(keys, skip?, limit?, input)`.
Operators SHALL nest arbitrarily. A query SHALL be an operator tree together with its semantic flags.

#### Scenario: Basic graph pattern
- **WHEN** a query is `Join[(?a knows ?b), (?b worksAt ?c)]`
- **THEN** it is a valid IR tree whose leaves are two triple patterns

#### Scenario: Empty join is the unit relation
- **WHEN** a query is `Join[]`
- **THEN** it denotes exactly one row with no bindings

#### Scenario: Inline values with an undefined cell
- **WHEN** inline values declare variables `?x ?y` and a row gives `?x = alice` and leaves `?y` absent
- **THEN** the row binds `?x` and leaves `?y` unbound

### Requirement: Pattern positions
Each subject, predicate, object and graph position of a pattern, each inline-values cell and each skip or limit SHALL be one of: a variable, a constant value, an already encoded ObjectId, or a named parameter. Parameters SHALL be resolved from the execution's parameter map before any store read; a parameter missing from the map SHALL fail with `InvalidQuery` naming it.

#### Scenario: Parameter as a pattern constant
- **WHEN** the pattern `(?x worksAt $org)` is executed with `org = acme`
- **THEN** it returns the same rows as `(?x worksAt acme)`

#### Scenario: Missing parameter
- **WHEN** the pattern `(?x worksAt $org)` is executed without `org`
- **THEN** execution fails with `InvalidQuery` naming `org` and reads nothing

### Requirement: Per-pattern view
Every triple pattern and path pattern SHALL carry its own view (a transaction-time selector `Now`, `AsOf(t or instant)` or `History`, and a valid-time selector `Unfiltered` or `At(epoch ms)`). A front end SHALL lower with the handle's view as the default and overlay a query-level or per-pattern clause part by part: a given selector replaces the selector of the same kind, a missing one keeps it.

#### Scenario: Two views in one query
- **WHEN** a query joins `(alice worksAt ?before)` under `AsOf(150)` with `(alice worksAt ?after)` under `Now`
- **THEN** the two patterns read different statement sets in one evaluation

#### Scenario: Overlaying one part
- **WHEN** the default view is `{Now, At(d)}` and a clause gives only `AsOf(150)`
- **THEN** the pattern's view is `{AsOf(150), At(d)}`

### Requirement: Eid binding
A triple pattern SHALL optionally bind the statement's eid to a variable. An eid variable SHALL be usable in subject or object position of other patterns, so a query reaches layers. The same eid variable in two patterns SHALL require the same statement.

#### Scenario: Annotation on a statement
- **WHEN** a query joins `(alice worksAt ?c) eid ?e` with `(?e confidence ?x)`
- **THEN** each row pairs a `worksAt` statement with a confidence asserted on that statement's eid

#### Scenario: Eid equal to a constant
- **WHEN** a pattern binds its eid to the constant eid `e7`
- **THEN** it matches at most the statement `e7`

### Requirement: Graph selectors
A triple pattern and a path pattern SHALL carry a graph selector: `Any` (no condition), `Set` of one or more graphs given by constants or parameters, or `Var(g)`. Membership SHALL be the statement `(e sys:inGraph g)` read in the pattern's own view.

#### Scenario: Graph selector forms
- **WHEN** three patterns carry `Any`, `Set[g1, g2]` and `Var(?g)`
- **THEN** all three are valid selectors

#### Scenario: Empty graph set rejected
- **WHEN** a pattern carries `Set[]`
- **THEN** validation fails with `InvalidQuery`

### Requirement: Expressions
Filter conditions, LeftJoin conditions, Extend expressions, aggregate arguments and sort keys SHALL be expressions built from variables, constants, parameters, comparisons (`= != < <= > >=`), `sameTerm`, `AND`, `OR`, `NOT`, `BOUND`, `IN` / `NOT IN`, arithmetic (`+ - * /`, unary minus), `COALESCE`, `IF`, the SPARQL 1.1 scalar functions (string, numeric, date-time, type tests, casts to the XSD types), and `EXISTS` / `NOT EXISTS` over an IR subtree. `REGEX` and `REPLACE` SHALL fail with `Unsupported` until the SPARQL front end supplies their regular-expression dialect. An `EXISTS` subtree SHALL be correlated with the enclosing row only through shared variables.

#### Scenario: Correlated existence test
- **WHEN** `Filter(EXISTS (?x confidence ?c), (?x a Person))` is evaluated
- **THEN** the subtree is tested once per row with `?x` taken from that row

### Requirement: Aggregates and sort keys
An aggregate SHALL name an output variable, a function (`COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, `SAMPLE`, `GROUP_CONCAT` with a separator), an optional argument (absent only for `COUNT(*)`) and a distinct flag. A sort key SHALL be an expression with a direction. Skip and limit SHALL be non-negative integer constants or parameters.

#### Scenario: Count star
- **WHEN** an aggregate is `COUNT(*)` with output `?n`
- **THEN** it is valid without an argument

#### Scenario: Negative limit
- **WHEN** an `OrderLimit` has limit `-1`
- **THEN** validation fails with `InvalidQuery`

### Requirement: Path patterns
A path pattern SHALL have a start and an end (each a variable, constant, ObjectId or parameter), a path expression, a mode (`REACH`, `TRAIL`, `ANY_SHORTEST`, `ALL_SHORTEST`), an optional hop bound, an optional variable bound to the path value, a view and a graph selector. Mode names SHALL be parsed case-insensitively; any other mode name (for example `WALK`, `SIMPLE`, `ACYCLIC`, `SHORTEST`) SHALL fail with `Unsupported` naming it.

#### Scenario: Mode names
- **WHEN** the mode text `all_shortest` is parsed
- **THEN** it is `ALL_SHORTEST`

#### Scenario: Unsupported mode
- **WHEN** the mode text `SIMPLE` is parsed
- **THEN** it fails with `Unsupported` naming `SIMPLE`

### Requirement: Semantic flags
A query SHALL carry three flags: match mode (`Homomorphism` or `RelIsomorphism`), missing values (`Unbound` or `Null3VL`) and graph set (`SetOfTriples` or `BagOfEids`). The SPARQL preset SHALL be `(Homomorphism, Unbound, SetOfTriples)` and the Cypher preset `(RelIsomorphism, Null3VL, BagOfEids)`. Any combination SHALL be accepted, and the same tree SHALL be evaluable under any flags.

#### Scenario: Presets
- **WHEN** the SPARQL and Cypher presets are built
- **THEN** they hold exactly the flag triples above

#### Scenario: Same tree, different graph set
- **WHEN** a store holds two live parallel statements with content `(a knows b)` (written by `create`) and `(?x knows ?y)` is evaluated without an eid under `SetOfTriples` and under `BagOfEids`
- **THEN** it returns one row and two rows respectively

### Requirement: Relationship-isomorphism groups
A triple pattern SHALL optionally belong to a numbered match group. Under `RelIsomorphism`, two patterns of one group SHALL never bind the same statement; under `Homomorphism` groups SHALL have no effect.

#### Scenario: Group constraint
- **WHEN** `(a knows ?x)` and `(?y knows b)` are in group 1 and a single statement `(a knows b)` exists
- **THEN** the join is empty under `RelIsomorphism` and has one row under `Homomorphism`

### Requirement: Structural validation
Validation SHALL run before any store read, need no database, and fail with `InvalidQuery` naming the first problem for: an `Extend` that rebinds a variable its input can bind; an aggregate output that collides with a grouping variable or another output; an inline-values row whose width differs from its variable list, a variable in a values cell, or a repeated values variable; a negative skip or limit; a virtual-predicate triple pattern that binds an eid or has a graph selector; an aggregate other than `COUNT` without an argument; an empty graph set or a variable inside a graph set; a projected variable that the input cannot bind; a function applied to the wrong number of arguments. A path pattern whose start and end are both unbound at evaluation time SHALL fail with `Unsupported` ("path needs a bound endpoint"), not `InvalidQuery`.

#### Scenario: Extend rebinds a bound variable
- **WHEN** `Extend(?x := 1, (?x p ?y))` is validated
- **THEN** validation fails with `InvalidQuery`

#### Scenario: Ragged values
- **WHEN** inline values declare two variables and one row has three cells
- **THEN** validation fails with `InvalidQuery`

#### Scenario: Machine-checked validation soundness
- **WHEN** the proofs library builds
- **THEN** "a validated query with complete parameters never fails with `InvalidQuery` on any store state" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Result column order
The result columns SHALL be the variables of the root `Project` in declared order; without a root `Project`, every variable the tree can bind, in order of first binding in a left-to-right walk.

#### Scenario: Project fixes column order
- **WHEN** `Project([?c, ?a], Join[(?a worksAt ?c)])` is executed
- **THEN** the columns are `?c, ?a` in that order

#### Scenario: Implicit column order
- **WHEN** `Join[(?a knows ?b), (?b worksAt ?c)]` is executed without a `Project`
- **THEN** the columns are `?a, ?b, ?c`

### Requirement: Constants never write
Planning and evaluation SHALL never write to the store. A constant IRI or dictionary literal that is not in the term dictionary SHALL make every pattern position it occupies match nothing, without failing, while the same constant in an expression, an `Extend` or inline values SHALL still denote its value.

#### Scenario: Unknown IRI constant
- **WHEN** `(?x worksAt neverSeen)` is evaluated and `neverSeen` is not in the dictionary
- **THEN** it returns no rows, raises no error, and the dictionary is unchanged

#### Scenario: Union with one empty branch
- **WHEN** `Union[(?x worksAt neverSeen), (?x worksAt acme)]` is evaluated
- **THEN** it returns the rows of the second branch

#### Scenario: Unknown constant bound by Extend
- **WHEN** `Extend(?y := "neverStored", Join[])` is evaluated
- **THEN** it returns one row binding `?y` to the string `"neverStored"`
