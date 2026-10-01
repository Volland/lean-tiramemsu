# store-contract Specification

## Purpose
Defines the abstract store the engine runs on: ordered index scans under a view, appends, the single retraction, counters, transactions, savepoints and snapshot reads. It is met by a pure model, over which all theorems are stated, and by SQLite, which is linked to the model by refinement tests and is the only trusted storage assumption (D3).

## Requirements

### Requirement: One engine over two stores
The engine SHALL reach storage only through the store interface. The interface SHALL have exactly two implementations: a pure model store and a SQLite store. Any code written against the interface SHALL run unchanged on both.

#### Scenario: Same code on both stores
- **WHEN** a sequence of store operations written against the interface is run once on the model store and once on the SQLite store
- **THEN** both runs compile from the same source and return results that the refinement comparison accepts

### Requirement: Index families and key order
The store SHALL offer ordered scans over these families of the triple table, each mirroring one format-1 index, with the key shown and the statement id as the final tiebreak:

| Family | Rows | Key order |
|---|---|---|
| live spo / pos / osp | live only | (s,p,o) / (p,o,s) / (o,s,p), t_ret, v_from, v_to, eid |
| history spo / pos / osp | all | the same permutation, t_add descending, t_ret, v_from, v_to, eid |
| valid | live only | p, v_from, v_to, eid |
| added log | all | t_add, eid |
| retracted log | retracted only | t_ret, ret_kind, eid |

Integer values SHALL compare as signed 64-bit integers, and an absent value SHALL sort before every present value. Scan results SHALL be in exactly this order.

#### Scenario: Signed comparison
- **WHEN** live spo is scanned over rows whose subjects are −1, 0 and 2⁶² with no prefix
- **THEN** they are returned in the order −1, 0, 2⁶²

#### Scenario: History newest first
- **WHEN** history spo is scanned with prefix (s,p,o) and that triple was added at transactions 3, 7 and 5
- **THEN** the rows are returned with t_add 7, 5, 3

#### Scenario: Absent sorts first
- **WHEN** the valid family is scanned with prefix (p) over rows with v_from absent and v_from = 10
- **THEN** the row with v_from absent comes first

### Requirement: Range scan semantics
A scan SHALL take a family, an equality prefix over the family's leading key columns (at most three for the live and history families, one for valid, none for the logs), an optional inclusive or exclusive lower and upper bound on the next key column, and a view. It SHALL return every row of the family that matches the prefix, the bounds and the view predicate, each exactly once, in key order. A row whose bounded column is absent SHALL NOT satisfy a bound. The caller SHALL be able to stop a scan early, and stopping SHALL return the rows delivered so far. A prefix longer than the family allows, or a live or valid family with a view other than now, SHALL fail with an invalid-scan error.

#### Scenario: Seek with a lower bound
- **WHEN** live pos is scanned with prefix (p) and an inclusive lower bound 40 on o, over objects 10, 40 and 90
- **THEN** exactly the rows with o = 40 and o = 90 are returned, in that order

#### Scenario: Early stop
- **WHEN** a scan that matches 1 000 rows is stopped after the third row
- **THEN** exactly the first three rows in key order were delivered

#### Scenario: Live family under as-of
- **WHEN** live spo is scanned with view as-of 5
- **THEN** the scan fails with an invalid-scan error

### Requirement: View predicates
A scan's view SHALL filter rows exactly as the Rust view mapping does (D6). Transaction time: now selects rows with no t_ret; as-of t selects rows with t_add ≤ t and (no t_ret or t_ret > t); history selects all rows. Valid time: unfiltered selects all rows; at d selects rows with (no v_from or v_from ≤ d) and (no v_to or v_to > d). The two parts SHALL combine by conjunction.

#### Scenario: Retracted between
- **WHEN** a row has t_add = 5 and t_ret = 9 and history spo is scanned under as-of 8, as-of 9 and as-of 4
- **THEN** it is returned only under as-of 8

#### Scenario: Half-open valid interval
- **WHEN** a live row has v_from = 100 and v_to = 200 and is scanned under at 100, at 199 and at 200
- **THEN** it is returned under at 100 and at 199, not at 200

### Requirement: Point reads
The store SHALL read: a triple row by statement id; a term row by id; a term id by its key (tag, lexical form, datatype, language), where an absent datatype or language matches only an absent one; a transaction row by number; the transaction with the greatest instant at or before a given instant; a counter by name; a volatile row by (subject, key); all volatile rows of a subject ordered by key; and whether a predicate is in the multi-eid set. A missing row SHALL be reported as absent, not as an error.

#### Scenario: Latest transaction at an instant
- **WHEN** transactions 1, 2 and 3 have instants 100, 200 and 300 and the store is asked for the transaction at or before 250
- **THEN** it returns transaction 2

#### Scenario: Term key with absent datatype
- **WHEN** a term with tag IRI, lexical form "x" and no datatype exists, and the store looks up tag IRI, "x" with datatype 7
- **THEN** the lookup returns absent

### Requirement: Appends never overwrite
The store SHALL append triple, term and transaction rows. Appending a row whose statement id, term id or transaction number already exists SHALL fail with an id-reused violation; appending a term whose key already exists SHALL fail with a term-key violation; appending a transaction whose instant already exists SHALL fail with an instant violation. A term's numeric value SHALL be stored as SQLite stores a REAL: NaN as absent and negative zero as positive zero. The interface SHALL have no operation that deletes or rewrites a triple, term or transaction row.

#### Scenario: Reused statement id
- **WHEN** a triple row is appended with an id that a retracted row already has
- **THEN** the append fails with an id-reused violation and the existing row is unchanged

#### Scenario: Numeric normalization
- **WHEN** a term is appended with numeric value −0.0 and another with NaN
- **THEN** reading them back gives +0.0 and an absent numeric value

### Requirement: Single retraction update
The only update to an existing triple row SHALL be retraction, which sets t_ret and ret_kind of a live row and changes nothing else. Retracting a row that is already retracted SHALL fail with a retract-once violation, and retracting an unknown id SHALL fail with not-found.

#### Scenario: Retract a live row
- **WHEN** a live row is retracted at transaction 9 with kind 2
- **THEN** that row has t_ret 9 and ret_kind 2 and every other column and row is unchanged

#### Scenario: Retract twice
- **WHEN** an already retracted row is retracted again
- **THEN** the call fails with a retract-once violation and the row keeps its first t_ret

### Requirement: Counters and side tables
The store SHALL read and set named integer counters, upsert and delete volatile rows keyed by (subject, key), and add predicates to the multi-eid set. Adding a predicate already in the set SHALL succeed without change.

#### Scenario: Volatile upsert
- **WHEN** a volatile row for (s, k) is put with value 1 and then with value 2
- **THEN** reading (s, k) returns value 2 and there is one row for (s, k)

### Requirement: Write transactions and savepoints
Every write SHALL happen inside a write transaction. Reads on the writer inside a transaction SHALL see its own earlier writes. Commit SHALL make all writes of the transaction visible at once; rollback SHALL discard all of them. A failed write SHALL leave the store as it was before that write and SHALL NOT end the transaction. Savepoints SHALL nest: rolling back to a savepoint SHALL restore the state at that savepoint and keep it open, and releasing it SHALL keep its writes and close it and every newer savepoint. A write outside a transaction, a nested begin, a commit or rollback without a transaction, a savepoint operation outside a transaction and a savepoint name that is not open SHALL each fail with a misuse error and change nothing.

#### Scenario: Failed write inside a transaction
- **WHEN** a transaction appends row e1, then appends a row with a reused id, then commits
- **THEN** the second append fails, the commit succeeds, and e1 is stored

#### Scenario: Rollback to savepoint
- **WHEN** a transaction appends e1, opens savepoint s, appends e2, rolls back to s, appends e3 and commits
- **THEN** e1 and e3 are stored and e2 is not

#### Scenario: Write without a transaction
- **WHEN** a triple is appended with no write transaction open
- **THEN** the call fails with a misuse error and nothing is stored

### Requirement: Snapshot reads
A reader SHALL observe the committed state as of the moment it began reading, for every read until it ends, regardless of later commits and of uncommitted writes. Several readers SHALL be independent of each other and of the writer. Committed state SHALL survive closing and reopening the store; uncommitted writes SHALL NOT.

#### Scenario: Commit after a reader began
- **WHEN** a reader begins, then the writer commits a new row, then the reader scans
- **THEN** the reader does not see the new row, and a reader begun after the commit does

#### Scenario: Uncommitted writes invisible
- **WHEN** the writer has appended a row in an open transaction and a reader begins and scans
- **THEN** the reader does not see the row

#### Scenario: Close during a transaction
- **WHEN** the store is closed while a write transaction is open and then reopened
- **THEN** only the writes of committed transactions are present

### Requirement: Storage errors are typed
Every store failure SHALL be one of: a violation (id reused, retract once, term key taken, instant taken), not-found, invalid scan, misuse, or a storage error carrying SQLite's primary and extended result codes and message. The model store SHALL never produce a storage error. After a storage error inside a write transaction the transaction SHALL be rolled back.

#### Scenario: Busy database
- **WHEN** the SQLite store reports a busy error in the middle of a write transaction
- **THEN** the call fails with a storage error carrying the busy code and the transaction's writes are discarded

### Requirement: SQLite meets the contract by refinement test
The SQLite store SHALL be linked to the model store only by tests, never by an axiom. A refinement test SHALL generate seeded random sequences that mix valid and invalid writes, transaction and savepoint control, reader begin and end on several readers, and every kind of read; run each sequence on both stores; and compare every result, including the order of scan rows and the error variant. A failing sequence SHALL be reproducible from its seed, minimized, and kept as a permanent regression case. The test SHALL also start from database files written by the pinned Rust build. Scan order SHALL be guaranteed by the SQL text itself and not depend on the plan SQLite chooses, and every scan shape SHALL be served by its family's covering index.

#### Scenario: Divergence found
- **WHEN** a generated sequence produces different results on the two stores
- **THEN** the test fails, prints the seed and the minimized sequence, and the minimized sequence is added to the regression cases

#### Scenario: Covering index plan
- **WHEN** the plan of each scan shape is explained on the SQLite store
- **THEN** each uses its family's index as a covering index with no separate sort step, or the test reports the shape

#### Scenario: Rust-written file
- **WHEN** the refinement test loads a file written by the pinned Rust build into both stores and runs a generated sequence
- **THEN** both stores return the same results

### Requirement: The model store is exact and ordered
On the model store, a valid scan SHALL return exactly the rows of the state that match its prefix, bounds and view, with no duplicates, strictly increasing in the family's key order, and an invalid scan SHALL fail with an invalid-scan error. The family key order SHALL be a strict total order on rows with distinct statement ids.

#### Scenario: Machine-checked scan exactness and order
- **WHEN** the proofs library builds
- **THEN** scan exactness, duplicate-freedom and strict key order on well-formed model states hold as theorems whose axioms satisfy the proof policy

### Requirement: Model writes are atomic and never overwrite
On the model store, every operation SHALL preserve uniqueness of statement ids; a failing operation SHALL leave the state unchanged; a successful append SHALL keep every existing row and add exactly one; a successful retraction SHALL change only t_ret and ret_kind of one live row; rollback SHALL restore the committed state; rolling back to a savepoint SHALL restore the state at that savepoint; commit SHALL publish the current state as committed.

#### Scenario: Machine-checked write atomicity
- **WHEN** the proofs library builds
- **THEN** id uniqueness preservation, unchanged state on failure, append and retraction effects, rollback, savepoint rollback and commit hold as theorems whose axioms satisfy the proof policy
