## Purpose

Defines immutable views that select statements by transaction time (now, as-of a transaction or instant, history) and optionally by valid time, the triple lookup and event log read through them, and the proven link between as-of views and replay of the log.

## ADDED Requirements

### Requirement: Views combine a transaction-time and a valid-time selector

A view SHALL be a transaction-time selector (`Now`, `AsOf(t)`, `AsOf(instant)` or `History`) combined with a valid-time selector (`Unfiltered` or `At(d)`); every combination SHALL be allowed. The default view SHALL be `Now` and `Unfiltered`. Deriving a view SHALL return a new view and SHALL NOT read or write the database. Valid time SHALL never filter unless `At(d)` is chosen.

#### Scenario: Valid time is opt-in
- **WHEN** `(alice worksAt acme)` valid `[2020-01-01, 2022-01-01)` is live and the now view is read
- **THEN** the statement is returned

#### Scenario: Valid-at combined with as-of
- **WHEN** `e1 = (alice worksAt acme)` valid from `2020-01-01` was superseded in transaction 9 with `v_to = 2026-03-01`
- **THEN** the as-of view at 8 filtered at `2026-06-01` returns `e1`, and the now view filtered at `2026-06-01` returns no employer for alice

### Requirement: Now, as-of and history selection

The now view SHALL return exactly the live statements of its snapshot. The as-of view at transaction `t` SHALL return exactly the statements with `t_add ≤ t` and (`t_ret` absent or `t_ret > t`), reporting `t_ret` and `ret_kind` as absent; as-of 0 SHALL be empty and as-of a number above the last committed one SHALL equal the now view. The history view SHALL return every stored statement with its real `t_ret` and `ret_kind`.

#### Scenario: State before a retraction
- **WHEN** `e1` is asserted in transaction 3 and retracted in transaction 6
- **THEN** as-of views at 3, 4 and 5 return `e1` without `t_ret`, and as-of views at 2 and 6 do not

#### Scenario: History shows both
- **WHEN** `e1` was retracted in transaction 6 and `e2` is live
- **THEN** the history view returns `e1` with `t_ret = 6` and its kind, and `e2` without `t_ret`

### Requirement: As-of equals replay of the log

For every `t`, the as-of view at `t` SHALL equal the state obtained by replaying, from an empty state, the event log entries with time `≤ t` in log order, where an assert entry adds its statement and a retract entry removes it. Equivalently, the as-of view at a committed `t` SHALL equal the now view as it was right after transaction `t` committed, whatever commits later.

#### Scenario: Random operation sequences
- **WHEN** random sequences of assert, create, retract, retract-matching, supersede and cardinality-one operations are committed
- **THEN** for every `t` from 0 to the last, the as-of view at `t` equals both the replayed log and the now view recorded right after `t` committed

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: As-of by instant

The as-of view at instant `ms` SHALL resolve, within its snapshot, to the largest committed `t` whose instant is `≤ ms`, or to 0 when there is none, and then behave as the as-of view at that `t`. Resolution SHALL be monotone in `ms`, and resolving the instant of transaction `t` SHALL give `t`.

#### Scenario: Instant between transactions
- **WHEN** transaction 1 has instant 1 000 and transaction 2 has instant 2 000
- **THEN** as-of 1 500 resolves to 1, as-of 2 000 to 2 and as-of 999 is empty

#### Scenario: Backwards clock
- **WHEN** instants were forced to 10 000, 10 001 and 10 002 by a backwards clock
- **THEN** as-of at those instants resolves to transactions 1, 2 and 3

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Valid-at is half-open

The valid-at view at `d` SHALL keep exactly the statements whose interval contains `d`: (`v_from` absent or `v_from ≤ d`) and (`v_to` absent or `v_to > d`), applied after the transaction-time selection. Two nonempty intervals SHALL overlap, in the sense used by assert and cardinality-one, exactly when some instant is in both.

#### Scenario: Boundaries
- **WHEN** a statement is valid `[2025-01-01, 2026-03-01)`
- **THEN** valid-at `2025-01-01` and `2026-02-28T23:59:59.999Z` return it, and valid-at `2024-12-31` and `2026-03-01` do not

#### Scenario: Unbounded
- **WHEN** a statement has no valid interval
- **THEN** every valid-at view returns it

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Triple lookup

A view SHALL answer a lookup with optional subject, predicate and object, returning every selected matching statement with eid, subject, predicate, object, `t_add`, `t_ret`, `v_from`, `v_to` and `ret_kind`, in ascending eid order, engine statements included. A lookup SHALL never write; a constant that needs the dictionary and is absent SHALL give an empty result without interning.

#### Scenario: Lookup by subject and predicate
- **WHEN** `(alice likes tea)`, `(alice likes coffee)` and `(bob likes tea)` are live and the now view is looked up with `alice` and `likes`
- **THEN** exactly the two alice statements are returned in ascending eid order

#### Scenario: Unknown constant
- **WHEN** a lookup uses a 20-byte string never stored
- **THEN** the result is empty and the `term` table is unchanged

### Requirement: Event log

The event log SHALL hold one `assert` entry at `t_add` for every stored statement and one `retract` entry at `t_ret`, with its kind, for every retracted statement. Events since `t` SHALL be every entry with time `> t`, ordered by time, asserts before retracts, then ascending eid. Failed transactions, dry runs and speculations SHALL produce no entries.

#### Scenario: Retraction with cascade
- **WHEN** transaction 4 asserts `e1` and `e2 = (e1 :note "x")` and transaction 5 retracts `e1`
- **THEN** events since 3 are `(4, e1, assert)`, `(4, e2, assert)`, `(5, e1, retract, explicit)`, `(5, e2, retract, cascade)`
