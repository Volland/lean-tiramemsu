## Purpose

Defines memory merging as an algebraic object only: statements form a two-phase set keyed by eid, merge is their union with the earliest retraction, and its laws are proven on the model so that future replication rests on them. No user operation merges databases.

## ADDED Requirements

### Requirement: Merge is the 2P-set union

The model SHALL define the merge of two statement sets as the set holding every eid present in either; for an eid present in both, the merged statement SHALL be retracted when it is retracted in either, with the earliest retraction under the order by `t_ret` then `ret_kind`, and live only when live in both. When the two sides disagree on the content of one eid, a fixed total order on statements SHALL choose the result, so that merge is defined for every pair. Merge SHALL NOT be exposed as a database operation.

#### Scenario: Retraction wins
- **WHEN** `e1` is live in set A and retracted at 7 with kind `explicit` in set B
- **THEN** in the merge `e1` is retracted at 7 with kind `explicit`

#### Scenario: Earliest retraction
- **WHEN** `e1` is retracted at 9 in A and at 7 in B
- **THEN** in the merge `e1` is retracted at 7

#### Scenario: No user operation
- **WHEN** the public database operations are listed
- **THEN** none merges two databases or statement sets

### Requirement: Merge laws

Merge SHALL be commutative, associative and idempotent on statement sets.

#### Scenario: Random sets
- **WHEN** merge is evaluated on random statement sets A, B and C
- **THEN** `merge(A, B) = merge(B, A)`, `merge(merge(A, B), C) = merge(A, merge(B, C))` and `merge(A, A) = A`

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the laws hold as theorems whose axioms satisfy the proof policy

### Requirement: Merge preserves never forget

When two statement sets agree on the content of every shared eid, their merge SHALL contain every eid of both with unchanged content, SHALL keep every retraction of either side (no statement becomes live again), and SHALL preserve the statement-level invariant (no self-reference, nonempty intervals, `t_add ≤ t_ret`).

#### Scenario: Nothing is lost
- **WHEN** A holds `e1` and `e2` and B holds `e2` retracted and `e3`
- **THEN** the merge holds `e1`, `e2` retracted and `e3`, each with its content

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy
