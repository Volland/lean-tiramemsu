## Purpose

Defines the optional per-predicate schema stored as ordinary versioned `sys:` statements (cardinality one, uniqueness with upsert, value type, subject type, edge flag), how each flag constrains writes inside the writer transaction, and how schema changes violated by live data are rejected.

## ADDED Requirements

### Requirement: Schema flags are versioned statements

A predicate's schema SHALL be the live statements whose subject is the predicate's IRI and whose predicate is `sys:cardinality`, `sys:unique`, `sys:valueType`, `sys:subjectType` or `sys:isEdge`. A flag SHALL be in force exactly while its statement is live in transaction time, independent of its valid interval, and enforcement SHALL use the flags live at the current point of the writing transaction. A predicate without flags SHALL behave as cardinality many without constraints.

#### Scenario: Flag takes effect within its transaction
- **WHEN** one transaction asserts `(:email sys:unique true)` and then `(alice :email "a@x.org")` and `(bob :email "a@x.org")`
- **THEN** the transaction fails with `UniqueViolation`

#### Scenario: Retracting a flag lifts the constraint
- **WHEN** the `sys:unique` flag of `:email` is retracted
- **THEN** a later transaction may assert the same email for two subjects

### Requirement: Flag values are validated

A flag's subject SHALL be an `IRI` outside `sys:` (otherwise `ReservedNamespace` for a `sys:` IRI, an invalid-term error for other kinds). Its object SHALL be `sys:one` or `sys:many` for `sys:cardinality`; a `BOOL` for `sys:unique` and `sys:isEdge`; a tag IRI or datatype IRI for `sys:valueType`; and `sys:IRI`, `sys:NODE`, `sys:BNODE`, `sys:STMT` or `sys:TX` for `sys:subjectType`; otherwise `ValueTypeMismatch` naming the flag. Every flag except `sys:subjectType` SHALL hold one live value: a new value SHALL retract the previous one with kind `cardinality`. `sys:subjectType` values SHALL accumulate.

#### Scenario: Changing a flag value
- **WHEN** `(:tag sys:cardinality sys:one)` is live and `(:tag sys:cardinality sys:many)` is asserted
- **THEN** the first is retracted with kind `cardinality` and only `sys:many` is live

#### Scenario: Second subject type
- **WHEN** `(:note sys:subjectType sys:STMT)` is live and `(:note sys:subjectType sys:TX)` is asserted
- **THEN** both are live and nothing is retracted

### Requirement: Order of schema checks

For every inserted statement the checks SHALL run in the order value type, subject type, uniqueness, cardinality-one replacement, and a failing check SHALL prevent the later ones. For assert, the two type checks SHALL run before the idempotency lookup, and uniqueness and cardinality SHALL run only when a statement is to be inserted.

#### Scenario: Value type is checked first
- **WHEN** `:confidence` has `sys:valueType xsd:double` and `sys:subjectType sys:STMT`, and `(alice :confidence "high")` is asserted
- **THEN** the transaction fails with `ValueTypeMismatch`, not `SubjectTypeMismatch`

#### Scenario: Unique check only on insert
- **WHEN** `:email` is unique, `(alice :email "a@x.org")` is live, and the same statement is asserted again
- **THEN** assert returns `Existing` and no uniqueness error is raised

### Requirement: Cardinality one replaces overlapping objects

For a predicate flagged `sys:cardinality sys:one`, an insert of `(s, p, o)` SHALL first retract, with kind `cardinality` and with cascade, every live `(s, p, o')` with `o' ≠ o` whose valid interval overlaps the new one, replaying nothing. Non-overlapping episodes SHALL stay live; an assert that finds an existing match SHALL retract nothing.

#### Scenario: Replacement without carrying annotations
- **WHEN** `:age` is `sys:one`, `e1 = (alice :age 30)` has `(e1 :source :form)`, and `(alice :age 31)` is asserted
- **THEN** `e1` and its annotation are retracted with kind `cardinality` and the new statement has no annotations

#### Scenario: Non-overlapping episodes coexist
- **WHEN** `:worksAt` is `sys:one`, `(alice :worksAt acme)` is live `[2020-01-01, 2022-01-01)` and `(alice :worksAt globex)` is asserted `[2022-01-01, unbounded)`
- **THEN** both are live

### Requirement: Uniqueness and upsert

For a predicate flagged `sys:unique true`, an insert of `(s2, p, o)` while a live `(s1, p, o)` with `s1 ≠ s2` exists SHALL fail with `UniqueViolation { p, o, existing: s1 }`, regardless of valid time. Upsert of `(p, o)` SHALL return the subject of the live `(s, p, o)` with the smallest eid and write nothing, or else allocate a new `NODE`, assert `(node, p, o)` without valid time and return it; on a predicate not flagged unique it SHALL fail with a not-unique-predicate error.

#### Scenario: Second subject rejected
- **WHEN** `:email` is unique, `(alice :email "a@x.org")` is live and `(bob :email "a@x.org")` is asserted
- **THEN** the transaction fails with `UniqueViolation` naming `:email`, `"a@x.org"` and `alice`, and leaves no trace

#### Scenario: Upsert twice in one transaction
- **WHEN** one transaction upserts `(:email, "new@x.org")` twice
- **THEN** both calls return the same new node and one statement is inserted

### Requirement: Value type and subject type

A live `sys:valueType` SHALL reject an object that does not match it with `ValueTypeMismatch { p, expected, got }`: a tag IRI matches that tag; a datatype IRI matches its inline encodings (`xsd:integer`: `INT`; `xsd:string`: `SHORT_STR`, `STR`; `rdf:langString`: `LANG_STR`; `xsd:boolean`, `xsd:date`, `xsd:dateTime`, `xsd:double`, `xsd:decimal`: their tags) and `TYPED` values with that datatype. Live `sys:subjectType` values SHALL mean any-of and SHALL reject another subject kind with `SubjectTypeMismatch { p, expected, got }`, `expected` listing the tag IRIs in eid order. `sys:isEdge` SHALL be stored and SHALL NOT constrain writes.

#### Scenario: Typed layer
- **WHEN** `(:confidence sys:subjectType sys:STMT)` is live
- **THEN** `(e1 :confidence 0.8)` is inserted and `(alice :confidence 0.8)` fails with `SubjectTypeMismatch`

#### Scenario: String datatype accepts short and long strings
- **WHEN** `:name` has `sys:valueType xsd:string` and `"Al"` and `"Alexandrina"` are asserted
- **THEN** both are inserted

### Requirement: Schema changes violated by live data are rejected

Asserting a flag that live data, including earlier writes of the same transaction, already violates SHALL fail with `SchemaConflict { violating }` listing the violating eids ascending: for `sys:one`, live statements of the predicate sharing a subject with a different-object overlapping one; for `sys:unique true`, live statements whose object is held by several subjects; for `sys:valueType`, live statements whose object does not match; for `sys:subjectType`, live statements whose subject kind is outside the resulting set. Retracting a `sys:subjectType` value that narrows the set onto violating data SHALL fail the same way; retracting the last value SHALL lift the constraint.

#### Scenario: Unique on duplicated data
- **WHEN** `(alice :email "a@x.org")` and `(bob :email "a@x.org")` are live and `(:email sys:unique true)` is asserted
- **THEN** the transaction fails with `SchemaConflict` listing both eids
