## Purpose

Defines speculation and dry runs: applying a transaction hypothetically with the full engine, reading the uncommitted result, and discarding it so that nothing reaches history, proven observationally pure on the model, while ids shown during speculation are never issued again.

## ADDED Requirements

### Requirement: Speculation runs the full engine and exposes the uncommitted state

A speculation SHALL take the single writer, start from the latest committed state, run the caller's write program with full semantics (schema checks, cascade, supersede, cardinality-one, upsert, metadata, volatile, memberships), then run the caller's read-only query program against the resulting uncommitted state with a now view, optionally narrowed by valid-at, and return the query's value. The query SHALL NOT be run when the write program fails.

#### Scenario: Hypothetical assert is visible inside
- **WHEN** a speculation asserts `(alice worksAt globex)` and its query looks up alice's employer
- **THEN** the query sees `globex` and its value is returned to the caller

#### Scenario: Hypothetical retraction with cascade
- **WHEN** a speculation retracts `e1` that has annotation `e2`
- **THEN** inside the query neither `e1` nor `e2` is in the now view

#### Scenario: Operations fail
- **WHEN** the speculative writes fail with `UniqueViolation`
- **THEN** that error is returned and the query is not run

### Requirement: Speculation is observationally pure

After a speculation or dry run finishes, successfully or not, every statement, term, transaction row, volatile value, `pred_multi` row, `last_t` and `last_instant` SHALL equal its value before, no event SHALL appear in the log, and every view read SHALL return what it returned before. Only the id counters MAY have advanced.

#### Scenario: Tables unchanged
- **WHEN** a speculation asserts statements with new long strings, supersedes a statement and sets a volatile value
- **THEN** afterwards `triple`, `term`, `tx`, `volatile` and `pred_multi` equal their previous contents

#### Scenario: Numbers not consumed
- **WHEN** the last committed transaction is 4, a speculation runs, and a transaction commits
- **THEN** the committed transaction has number 5

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Ids allocated in speculation are burned

After the speculative state is discarded, the statement, node, blank-node and term id counters SHALL be raised to their values at the end of the speculation, in a commit of their own that changes nothing else, so that no id allocated during a speculation or dry run, whether it succeeded or failed, is ever issued again, also after the database is reopened. When no id was allocated, no counter commit SHALL be made.

#### Scenario: Statement ids are not reissued
- **WHEN** a speculation creates statements up to eid `e20` and a transaction then inserts a statement
- **THEN** its eid is greater than `e20`

#### Scenario: Term ids are not reissued
- **WHEN** a speculation interns a new IRI with term id 30 and a later transaction interns the same IRI
- **THEN** the IRI receives a term id greater than 30

#### Scenario: Burned ids survive a reopen
- **WHEN** a speculation burns ids, the database is closed and reopened, and a statement is inserted
- **THEN** its eid is greater than every burned eid

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Dry run returns the would-be report

A transaction run with `dry_run` SHALL execute its body exactly as a commit would, return the report a commit from the same state and clock reading would have returned (including the `t` and instant it would have had), and then discard every effect as a speculation does.

#### Scenario: Dry run preview
- **WHEN** a dry run asserts two statements and retracts one with an annotation
- **THEN** the report lists the two asserted eids and both retractions with their kinds, the `tx` and `triple` tables are unchanged, and the next commit receives the `t` the report showed

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Speculation is isolated and starts from now

Readers on other connections SHALL never see speculative state. A speculation SHALL hold the writer for its whole duration, so other writers wait. There SHALL be no way to speculate from a past transaction and no persistent branch.

#### Scenario: Other readers never see speculation
- **WHEN** a reader looks up the same pattern while a speculative query is running
- **THEN** it sees only committed state

#### Scenario: Writers wait for speculation
- **WHEN** a transaction starts on another task while a speculation is running
- **THEN** it commits only after the speculation finishes and sees none of its writes
