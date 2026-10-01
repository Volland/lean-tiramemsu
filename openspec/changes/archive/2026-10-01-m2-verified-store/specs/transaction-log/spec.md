## Purpose

Defines the unit of every write: a transaction with a gap-free number and a strictly increasing instant from an injectable clock, recorded even when it changes nothing, carrying metadata as triples, reporting what it did, and leaving no trace when it fails.

## ADDED Requirements

### Requirement: Gap-free transaction numbers

Every committed transaction SHALL receive the number `t` equal to the previous committed number plus one, starting at 1. Failed transactions, dry runs and speculations SHALL NOT consume a number. The `tx` table SHALL hold exactly the numbers 1 to the last committed `t`.

#### Scenario: Numbers across failures and speculation
- **WHEN** transaction 3 commits, then a transaction fails, a dry run runs and a speculation runs, then another transaction commits
- **THEN** the last transaction has `t = 4` and the `tx` table holds exactly 1 to 4

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Strictly increasing instants for any clock

Every committed transaction SHALL record `instant = max(now, previous_instant + 1)` in epoch milliseconds, where `now` is read from the database's clock after the writer lock is taken and `previous_instant` is the instant of the previous committed transaction, or 0 for the first. Instants SHALL be strictly increasing in `t` for every possible sequence of clock readings, including clocks that stand still or move backwards. An instant outside the 64-bit signed range SHALL fail the transaction with a store error (listed deviation: Rust overflows).

#### Scenario: Clock moves backwards
- **WHEN** a transaction commits with the clock at 10 000 and the next with the clock at 5 000
- **THEN** the instants are 10 000 and 10 001

#### Scenario: Clock stands still
- **WHEN** three transactions commit while the clock reads 7 000
- **THEN** the instants are 7 000, 7 001 and 7 002

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Every committed transaction is recorded

Every committed transaction SHALL add exactly one `tx` row, even when its body performs no operation or only idempotent no-ops, and even when it only touches volatile state.

#### Scenario: Empty transaction
- **WHEN** a transaction whose body does nothing commits
- **THEN** a new `tx` row exists with the next number and a fresh instant, and its report lists no statement

#### Scenario: All operations idempotent
- **WHEN** a transaction only re-asserts statements that are live with overlapping valid time
- **THEN** a new `tx` row is recorded and the report lists those statements as existing and none as asserted

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Injectable clock

A database SHALL take its clock when it is opened, defaulting to the system clock in epoch milliseconds. A manual clock that only moves when set or advanced SHALL be available, so that instants and as-of-instant views are deterministic in tests and in differential runs against Rust.

#### Scenario: Manual clock
- **WHEN** a database is opened with a manual clock at 1 000, a transaction commits, the clock is advanced by 500 and another transaction commits
- **THEN** the instants are 1 000 and 1 500

### Requirement: Transactions are nodes with metadata triples

A transaction SHALL be addressable by the `TX` id whose payload is `t`. The metadata operation SHALL assert, idempotently, a statement whose subject is the current transaction; its predicate SHALL be `sys:author`, `sys:source`, `sys:reason` or any non-reserved predicate. Metadata statements SHALL be ordinary statements. A `TX` id SHALL be accepted as subject or object of any other statement. `sys:author`, `sys:source` and `sys:reason` with a subject that is not a transaction SHALL fail with `ReservedNamespace`.

#### Scenario: Author and reason
- **WHEN** a transaction records `sys:author = :agent7` and `sys:reason = "user correction"` and commits as `t = 5`
- **THEN** the now view contains `(tx5 sys:author :agent7)` and `(tx5 sys:reason "user correction")`, each with its own eid and `t_add = 5`

#### Scenario: Metadata on a non-transaction
- **WHEN** a transaction asserts `(alice sys:reason "x")`
- **THEN** it fails with `ReservedNamespace`

### Requirement: Transaction report

A committed or dry-run transaction SHALL return a report with `t`, `instant`, `asserted` (every inserted statement eid except memberships, in insertion order), `existing` (eids returned as existing by assert, without duplicates and without eids the same transaction inserted), `retracted` (every retracted non-membership eid with its kind, in retraction order), `superseded` (every `(old, new)` pair of each supersede, root first), `memberships` (new membership eids) and `memberships_retracted` (retracted membership eids with kinds).

#### Scenario: Mixed operations
- **WHEN** one transaction asserts a new statement A, re-asserts a live statement B, and retracts C that has one annotation D
- **THEN** `asserted = [A]`, `existing = [B]` and `retracted = [(C, explicit), (D, cascade)]`

#### Scenario: Repeated assert in one transaction
- **WHEN** one transaction asserts the same new statement twice
- **THEN** the eid is listed once in `asserted` and not in `existing`

### Requirement: Transaction options

A transaction SHALL accept `dry_run` (default false) and `max_cascade` (default 10 000). `max_cascade` SHALL bound every cascade set computed in the transaction, as the retraction-cascade capability specifies; `dry_run` SHALL behave as the speculative-transactions capability specifies.

#### Scenario: Default cascade limit
- **WHEN** a transaction with default options retracts a statement with 9 999 dependents, and another retracts one with 10 000 dependents
- **THEN** the first commits and the second fails with `CascadeLimitExceeded`

### Requirement: Atomic failure leaves no trace

When any operation fails or the body returns an error, the whole transaction SHALL be rolled back and the error returned: no `tx` row, statement, retraction, term, volatile change, `pred_multi` row or `meta` counter change SHALL remain, and no term interned by it SHALL become visible through any cache.

#### Scenario: Error after successful operations
- **WHEN** a transaction asserts a statement with a new long string, retracts another statement, and then fails with `UniqueViolation`
- **THEN** the error is returned and the `tx`, `triple`, `term`, `volatile`, `pred_multi` and `meta` tables equal their previous contents

#### Scenario: Body aborts
- **WHEN** the body returns its own error after performing writes
- **THEN** that error is returned and no effect of the body remains

### Requirement: Transaction bodies cannot perform IO

A transaction body and a speculative query SHALL be programs over the engine's read and write operations only, so that the same body runs unchanged on the model store and on SQLite and so that a nested write on the same database cannot be expressed (listed deviation: Rust rejects nested writes at runtime with a re-entrancy error).

#### Scenario: Same body on both stores
- **WHEN** one body value is run on the model store and on a SQLite store from the same initial state and clock reading
- **THEN** both return the same result and report and reach equal states
