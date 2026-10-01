## Purpose

Defines the volatile side table for high-churn state that does not deserve history: transactional upserts per subject and key, outside the graph, visible only through the now view.

## ADDED Requirements

### Requirement: Volatile values are upserted per subject and key

Setting a volatile value SHALL upsert the row `(s, key)` with the value and `updated_at` equal to the current transaction's instant. The key SHALL be an `IRI` and the subject subject-capable, both naming existing terms when they are dictionary ids; otherwise the write SHALL fail with an invalid-term error. Clearing SHALL remove the row and SHALL succeed when there is none. Volatile writes SHALL belong to their transaction: discarded when it fails, by dry runs and by speculation.

#### Scenario: Overwrite a value
- **WHEN** transaction 3 sets `(alice, :lastSeen)` and transaction 4 sets it again with another value
- **THEN** one row exists with the second value and `updated_at` equal to transaction 4's instant

#### Scenario: Failed transaction discards the write
- **WHEN** a transaction sets a volatile value and then fails
- **THEN** the volatile table is unchanged

#### Scenario: Clear twice
- **WHEN** `(alice, :score)` is cleared twice
- **THEN** the row is gone and both calls succeed

### Requirement: Volatile values are not statements

Volatile values SHALL have no eid, transaction-time lifetime, valid time or layers. Setting or clearing one SHALL NOT insert or retract any statement, and SHALL NOT change any triple lookup, dependents read or event log entry on any view. A transaction whose only operation is a volatile write SHALL still record a `tx` row.

#### Scenario: Not visible as a triple
- **WHEN** `(alice, :lastSeen)` is set as a volatile value
- **THEN** a now-view lookup of `alice :lastSeen` returns no statement and the events since the previous transaction contain nothing for it

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Volatile values resolve only under now

Resolving the values of `(s, key)` on a view SHALL return the objects of the statements `(s, key, o)` selected by the view when there are any; otherwise, only for a now view, the volatile value if one exists. As-of and history views SHALL never return a volatile value. Inside a speculation, the query SHALL see the speculation's own volatile writes.

#### Scenario: Now view reads the volatile value
- **WHEN** `(alice, :lastSeen)` is volatile and no statement `(alice :lastSeen ?)` is live
- **THEN** resolving it on the now view returns the volatile value

#### Scenario: Absent under time travel
- **WHEN** the same key is resolved on the as-of view at the latest transaction and on the history view
- **THEN** both return nothing

#### Scenario: Statement wins
- **WHEN** `(alice :status "away")` is live and `(alice, :status)` is volatile with `"busy"`
- **THEN** resolving on the now view returns `"away"`

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the absence of volatile values under as-of and history holds as a theorem whose axioms satisfy the proof policy
