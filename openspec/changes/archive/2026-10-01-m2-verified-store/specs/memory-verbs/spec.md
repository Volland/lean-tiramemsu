## Purpose

Defines the write verbs of a transaction (assert, create, retract, retract-matching, supersede, confirm, new node, new blank node) and the write pipeline they share, with idempotent assert and layer-preserving supersede proven on the model.

## ADDED Requirements

### Requirement: Write pipeline

Every statement written by assert, create, confirm, metadata, upsert or a membership verb SHALL pass, in this order: position checks (subject kind, `IRI` predicate, dictionary ids that name an existing term of their tag; otherwise an invalid-term error); the reserved-namespace check for user writes; the interval check (`v_from < v_to` when both are present, otherwise `InvalidInterval`); the predicate-schema type checks; for assert only, the idempotency lookup; the uniqueness check and cardinality-one replacement; eid allocation; the self-reference check; insertion with `t_add` equal to the current transaction. A failing step SHALL prevent all later ones and fail the transaction.

#### Scenario: Literal subject rejected
- **WHEN** a transaction asserts a statement whose subject is the integer 5
- **THEN** the transaction fails with an invalid-term error and leaves no trace

#### Scenario: Empty interval rejected
- **WHEN** a statement is asserted with `v_from = v_to = 2025-01-01`
- **THEN** the transaction fails with `InvalidInterval`

### Requirement: Reserved namespaces

User writes SHALL NOT use a predicate in `urn:tiramemsu:tm:` nor in `urn:tiramemsu:sys:`, except the schema flags `sys:cardinality`, `sys:unique`, `sys:valueType`, `sys:subjectType`, `sys:isEdge`, the vocabulary settings `sys:vocab`, `sys:prefix`, `sys:prefixName`, `sys:prefixIri`, and `sys:author`, `sys:source`, `sys:reason` with a transaction subject. Any other such predicate, including `sys:confirmedBy`, `sys:supersedes` and `sys:inGraph`, SHALL fail with `ReservedNamespace(iri)`; `sys:sensitive` SHALL fail with `Unsupported` naming milestone M6. The engine itself SHALL write `sys:confirmedBy`, `sys:supersedes` and `sys:inGraph`.

#### Scenario: Forged confirmation
- **WHEN** a transaction asserts `(e1 sys:confirmedBy tx3)` directly
- **THEN** it fails with `ReservedNamespace(urn:tiramemsu:sys:confirmedBy)`

#### Scenario: Allowed flag
- **WHEN** a transaction asserts `(:email sys:unique true)`
- **THEN** the statement is inserted

### Requirement: Assert is idempotent

Assert SHALL return `Existing(eid)` and insert nothing when a live statement with the same subject, predicate and object has a valid interval overlapping the requested one, choosing the smallest such eid; otherwise it SHALL insert a statement with a fresh eid and return `New(eid)`. Intervals `a` and `b` overlap exactly when `(a.from absent or b.to absent or a.from < b.to) and (b.from absent or a.to absent or b.from < a.to)`. An overlapping but different interval SHALL NOT be merged, widened or narrowed. Asserting the same statement twice in a row SHALL have the effect of asserting it once.

#### Scenario: Same fact twice
- **WHEN** `(alice worksAt acme)` is asserted in transaction 1 and again in transaction 2
- **THEN** transaction 2 returns `Existing` with the eid from transaction 1 and inserts no statement

#### Scenario: Touching intervals do not overlap
- **WHEN** `(alice worksAt acme)` is live valid `[2020-01-01, 2022-01-01)` and is asserted valid `[2022-01-01, 2024-01-01)`
- **THEN** assert returns `New` and both statements are live

#### Scenario: Retracted match is ignored
- **WHEN** `(alice worksAt acme)` was retracted and is asserted again
- **THEN** assert returns `New` with a fresh eid

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Assert can confirm an existing match

Assert SHALL accept an on-existing policy `Return` (default) or `Confirm`. With `Confirm`, an assert that finds an existing match SHALL also confirm it as the confirm verb does and still return `Existing(eid)`; an assert that inserts SHALL NOT confirm.

#### Scenario: Confirming re-assert
- **WHEN** `(alice worksAt acme)` is live as `e1` and transaction 9 asserts it with `Confirm`
- **THEN** assert returns `Existing(e1)` and `(e1 sys:confirmedBy tx9)` is live

### Requirement: Create always inserts

Create SHALL always insert a new statement with a fresh eid, even when an equal live statement exists, and return the eid. Schema checks SHALL apply as for assert.

#### Scenario: Parallel edges
- **WHEN** `(a called b)` is created twice
- **THEN** two different eids are returned and both statements are live

### Requirement: Retract and retract-matching

Retract SHALL, for a live statement, retract it with kind `explicit`, cascade, and return true; for a retracted or unknown eid it SHALL change nothing and return false. Retract-matching SHALL take an optional subject, predicate and object, collect every statement live at the call that matches them regardless of valid time, retract each that is still live in ascending eid order with cascade, and return all collected eids; a collected statement already retracted by an earlier match's cascade SHALL keep that cascade's kind.

#### Scenario: Retract twice in one transaction
- **WHEN** one transaction retracts `e1` twice
- **THEN** the first call returns true and the second returns false

#### Scenario: Match reached through an earlier cascade
- **WHEN** `e2 = (e1 :note "x")` annotates `e1 = (alice :note "y")` and retract-matching runs with predicate `:note`
- **THEN** both eids are returned, `e1` has kind `explicit` and `e2` kind `cascade`

### Requirement: Supersede replays the layers

Supersede of a live statement `root` with a patch SHALL, in the current transaction `t`: compute the cascade set `C` of `root`; allocate fresh eids for the members of `C` in cascade order, forming `σ`; retract every member of `C` with kind `supersede` at `t`; insert, for every member `m` of `C` that is not a graph membership, a statement with eid `σ(m)`, the predicate of `m`, subject and object of `m` rewritten through `σ` where they are members of `C`, the valid interval of `m`, and `t_add = t`, except that `σ(root)` takes the patched object and interval; insert `(σ(root) sys:supersedes root)`; and return `σ(root)`. No other statement SHALL be inserted, and no other statement SHALL be retracted except by cardinality-one replacement for the new root. Graph memberships in `C` SHALL be retracted and not replayed.

#### Scenario: Replay rewires annotations and references
- **WHEN** `e1 = (alice worksAt acme)` has `e2 = (e1 :confidence 0.8)` and `e7 = (:belief9 :supportedBy e1)`, and `e1` is superseded with `v_from = 2025-02-01`
- **THEN** a new root `e10 = (alice worksAt acme)` valid from `2025-02-01`, `(e10 :confidence 0.8)`, `(:belief9 :supportedBy e10)` and `(e10 sys:supersedes e1)` are live, and `e1`, `e2`, `e7` are retracted with kind `supersede`

#### Scenario: Cycles are rewired
- **WHEN** the cascade set contains two statements that reference each other
- **THEN** their replays reference each other's new eids and neither references an old eid

#### Scenario: Chain of corrections
- **WHEN** `e1` is superseded into `e10` and later `e10` into `e20`
- **THEN** `(e20 sys:supersedes e10)` and `(e20 sys:supersedes e1)` are live and `(e10 sys:supersedes e1)` is retracted with kind `supersede`

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Patch rules

A patch SHALL be able only to set the object, set or clear `v_from`, and set or clear `v_to`; omitted fields keep the root's values. A patch whose interval is empty, or that leaves object and both bounds unchanged, SHALL fail with `InvalidPatch`. Supersede of a retracted or unknown statement, including one retracted earlier in the same transaction, SHALL fail with `NotLive(eid)`. The new root SHALL pass the value-type and uniqueness checks and trigger cardinality-one replacement; the subject-type check SHALL NOT be repeated. The cascade set SHALL be bounded by `max_cascade`.

#### Scenario: Close an open interval
- **WHEN** `e1` valid `[2020-01-01, unbounded)` is superseded with `v_to = 2026-03-01`
- **THEN** the new root is valid `[2020-01-01, 2026-03-01)`

#### Scenario: Patch changes nothing
- **WHEN** a statement is superseded with an empty patch or with its current object
- **THEN** the transaction fails with `InvalidPatch` and leaves no trace

#### Scenario: Supersede twice in one transaction
- **WHEN** one transaction supersedes `e1` and then supersedes `e1` again
- **THEN** the second call fails with `NotLive(e1)`

### Requirement: Confirm and new ids

Confirm SHALL, for a live statement `eid`, assert `(eid sys:confirmedBy txT)` for the current transaction `T` idempotently and return its eid; for a retracted or unknown eid it SHALL fail with `NotLive(eid)`. New-node and new-blank-node SHALL return a fresh `NODE` or `BNODE` id never issued before, writing no statement.

#### Scenario: Confirmation by two transactions
- **WHEN** live `e1` is confirmed in transactions 5 and 8
- **THEN** `(e1 sys:confirmedBy tx5)` and `(e1 sys:confirmedBy tx8)` are live and `e1` is unchanged

#### Scenario: Fresh node ids
- **WHEN** a transaction calls new-node twice
- **THEN** two different `NODE` ids are returned and no statement is written

### Requirement: Multi-eid predicate bookkeeping

When an insert finds another stored statement, live or retracted, with the same subject, predicate and object, the predicate SHALL be added to `pred_multi` if absent and `meta.multi_version` SHALL increase by one, exactly as in Rust format 1.

#### Scenario: Parallel edge marks the predicate
- **WHEN** `(a called b)` is created twice on a fresh database
- **THEN** `pred_multi` contains `called` and `multi_version` increased by one
