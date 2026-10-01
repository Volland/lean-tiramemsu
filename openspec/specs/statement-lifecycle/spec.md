# statement-lifecycle Specification

## Purpose
Defines the life of a stored statement: born live, retracted at most once with a recorded kind, never deleted or changed, and addressed by an eid that is never issued twice. These rules are proven as an invariant that every operation preserves.

## Requirements

### Requirement: Statement content is immutable

A statement SHALL consist of an eid (a `STMT` ObjectId), a subject, a predicate, an object, a valid interval, the number `t_add` of the transaction that inserted it, and an optional retraction made of `t_ret` and `ret_kind`. The subject SHALL be an `IRI`, `NODE`, `BNODE`, `STMT` or `TX` id and the predicate an `IRI`. After insertion, the eid, subject, predicate, object, valid interval and `t_add` SHALL never change, and `t_ret` and `ret_kind` SHALL be either both absent or both present.

#### Scenario: Content survives retraction
- **WHEN** `e1 = (alice worksAt acme)` valid `[2020-01-01, 2022-01-01)` is inserted in transaction 3 and retracted in transaction 7
- **THEN** the history view shows `e1` with the same subject, predicate, object, interval and `t_add = 3`, and with `t_ret = 7` and a retraction kind

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Live to retracted exactly once

A statement SHALL be live from its insertion until it is retracted. A retraction SHALL set `t_ret` to the current transaction number and `ret_kind` to one of `explicit` (0), `cascade` (1), `supersede` (2) or `cardinality` (3). A retracted statement SHALL never become live again and its `t_ret` and `ret_kind` SHALL never change. Any operation that would retract an already-retracted statement SHALL leave it untouched.

#### Scenario: Second retraction leaves the first
- **WHEN** `e1` was retracted in transaction 4 with kind `explicit` and a later transaction retracts it again
- **THEN** `e1` keeps `t_ret = 4` and kind `explicit`

#### Scenario: Asserted and retracted in one transaction
- **WHEN** transaction 7 inserts `e5` and retracts it
- **THEN** `e5` has `t_add = 7` and `t_ret = 7`, is absent from the now view and from every as-of view, and is present in the history view

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Nothing is ever deleted

No operation SHALL remove a statement, a term or a transaction row. Every committed transaction, dry run and speculation SHALL leave every previously stored statement present with its content, every previously stored term and transaction row present and unchanged, and the id counters no lower than before. The engine SHALL issue no SQL that the never-forget triggers would abort.

#### Scenario: Random operations under the triggers
- **WHEN** random sequences of every write operation, including failures, dry runs and speculation, run against a database with the format-1 triggers
- **THEN** no trigger aborts a statement and every row present before a transaction is present after it

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Eids are never reused

Every statement inserted by any operation SHALL receive an eid that has never been issued before by a committed transaction, a dry run or a speculation on the database. Eids issued inside a transaction that fails MAY be issued again, because a failed transaction leaves the counters unchanged (Rust-compatible).

#### Scenario: Retract then re-assert
- **WHEN** `e1 = (alice worksAt acme)` is retracted and the same triple is asserted again
- **THEN** the new statement has an eid different from and greater than `e1`, and `e1` stays retracted

#### Scenario: Failed transaction may reissue
- **WHEN** a transaction that allocated eid 20 fails and the next transaction inserts a statement
- **THEN** the new statement may receive eid 20

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: No direct self-reference

A statement SHALL NOT use its own eid as its subject or object; a write that would do so SHALL fail with `SelfReference(eid)` and leave no trace. Reference cycles between distinct statements SHALL be allowed. A `STMT` id in subject or object position SHALL be accepted whether it refers to a live statement, a retracted one or one not yet issued.

#### Scenario: Guessed own eid
- **WHEN** a caller asserts a statement whose object is the eid the engine will allocate for that statement
- **THEN** the transaction fails with `SelfReference` carrying that eid

#### Scenario: Annotating a retracted statement
- **WHEN** `e1` was retracted earlier and a transaction asserts `(e1 :note "was wrong")`
- **THEN** the statement is inserted and is live

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the invariant that no stored statement references itself holds as a theorem whose axioms satisfy the proof policy
