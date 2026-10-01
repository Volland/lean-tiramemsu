## 1. Prerequisites and store interface

- [x] 1.1 Confirm M0 (`Store` interface, `ModelStore`, `SqliteStore`, proof gates, Rust oracle pin) and M1 (ObjectId, term dictionary, schema and triggers) are merged; `lake build` and the axiom check pass on main
- [x] 1.2 Check the `Store` interface against design §8 (volatile upsert/delete/lookup, `pred_multi` insert-if-absent, point lookup by eid, savepoint/rollback-to/release, `meta.last_t` read); add any missing operation to `ModelStore` and `SqliteStore` with a contract test and a refinement case
- [x] 1.3 Create the module skeleton of design §2 (`Tiramemsu/Engine`, `Tiramemsu/View`, `Tiramemsu/Model`, `Tiramemsu/Shell`, `TiramemsuProofs/Store`, `tests/Store`) wired into the lakefile; build is green

## 2. Core types and intervals

- [x] 2.1 Implement `Engine/Types.lean`: `Row`, `Retraction`, `RetKind` (codes 0–3), `Valid`, `Patch`, `Asserted`, `TxOptions` (defaults `dry_run = false`, `max_cascade = 10000`), `TxReport`, new `Error` cases with Rust-equivalent names
- [x] 2.2 Implement `Engine/Interval.lean`: `Valid.check`, `overlaps`, `validAt`
- [x] 2.3 Prove the half-open characterisation of `validAt` and `overlaps ↔ ∃ d, validAt d i ∧ validAt d j` for nonempty intervals; add both to the theorem index (temporal-views: Valid-at is half-open)
- [x] 2.4 Define `WF`, `WFIn t` and `Extends` in `TiramemsuProofs/Store/Invariant.lean`; prove `Extends` is a preorder and the `begin`/`commit` bridges between `WF` and `WFIn`

## 3. Transaction programs and the transaction log

- [x] 3.1 Implement `Engine/Prog.lean`: `Verb`, `TxProg`, `ReadProg` (free monads with `Monad` instances), `TxCtx`, `TxM`, and the generic interpreter `TxProg.run`
- [x] 3.2 Implement `transactCore` (tx row, `nextInstant`, counter store at commit, rollback on error) generic over `Store`; model instance `Model.transact`
- [x] 3.3 Prove `prev < nextInstant prev now` and the tx-log theorem (`txs` grows by exactly `(lastT + 1, nextInstant …)` for every program, including `pure ()`); index them (transaction-log: gap-free numbers, strictly increasing instants, every committed transaction recorded)
- [x] 3.4 Implement the metadata verb and the report assembly (`existing` deduplication, membership lists)
- [x] 3.5 Scenario tests for transaction-log on both stores: numbering across failure/dry run/speculation, backwards and standing clock, empty and all-no-op transactions, metadata, report contents, atomic failure table equality, same body on both stores

## 4. Write pipeline and basic verbs

- [x] 4.1 Implement `Engine/Schema.lean` read side (`PredicateSchema` from live flags at the current point of the transaction) and the value-type and subject-type checks
- [x] 4.2 Implement `Engine/Pipeline.lean` in the order of the memory-verbs write-pipeline requirement, including reserved namespaces, self-reference and `pred_multi` upkeep
- [x] 4.3 Implement assert (with `Return`/`Confirm`), create, confirm, new-node, new-blank-node in `Engine/Verbs.lean`
- [x] 4.4 Prove the per-verb `WFIn`/`Extends` preservation lemmas for these verbs and for the read verbs
- [x] 4.5 Prove assert idempotence (existing match returns the smallest eid and changes no row; `assert x; assert x` equals one assert); index it (memory-verbs: Assert is idempotent)
- [x] 4.6 Scenario tests for pipeline, reserved namespaces, assert, confirm, create, new ids, `pred_multi`

## 5. Cascade, retraction and dependents

- [x] 5.1 Implement `Engine/Walk.lean` (`walk vis root`, fuel = row count + 1), `cascadeSet` with the `max_cascade` abort, and `retractRoot` with kind assignment
- [x] 5.2 Prove walk termination within the fuel, `Nodup`, root first, and walk = reflexive-transitive closure of `StandsOn vis`; prove the limit error occurs iff the closure is larger than the limit; index (retraction-cascade: closure, order/cycles, size limit)
- [x] 5.3 Implement retract and retract-matching; prove their preservation lemmas and that `retract e` retracts exactly the cascade set with root `explicit`, rest `cascade`
- [x] 5.4 Implement `dependents` on a view through the same `walk`; prove dependents = closure over visible statements and `dependents now = cascadeSet` as lists; index (retraction-cascade: dependents on any view)
- [x] 5.5 Scenario tests for cascade (layers, nodes and tx metadata not propagating, diamond, cycles, kinds, limit per root, past visibility) and dependents on now, as-of, history, valid-at

## 6. Supersede

- [x] 6.1 Implement `Engine/Supersede.lean` with patch resolution, `InvalidPatch`/`NotLive`, schema checks, `σ` allocation in cascade order, membership skipping and the `sys:supersedes` link
- [x] 6.2 Prove the supersede preservation lemma and the replay theorem (retracted set and kinds, exact list of new rows, rewiring through `σ`, patch on the root only, other rows unchanged except cardinality retractions); index (memory-verbs: Supersede replays the layers)
- [x] 6.3 Scenario tests for supersede and patch rules (rewiring, deep layers, cycles, chains, close/clear bounds, no-change and empty patches, twice in one transaction, limit, schema failures)

## 7. Predicate schema

- [x] 7.1 Implement flag validation, single-valued flag replacement, uniqueness, cardinality-one replacement, upsert, schema-change conflicts and subject-type retraction checks
- [x] 7.2 Prove the preservation lemmas for upsert and the flag paths (enforcement itself is tested, not proven)
- [x] 7.3 Scenario tests for every predicate-schema requirement, plus check order

## 8. Named-graph membership and volatile state

- [x] 8.1 Implement `Engine/Graph.lean` (add, remove, clear, create, drop) and the view reads `graphMembers` and `graphs`; prove their preservation lemmas
- [x] 8.2 Scenario tests for named-graph-membership (names, idempotent add, remove, management verbs, engine-owned predicate, cascade and supersede of members, time travel and valid-at reads)
- [x] 8.3 Implement `Engine/Volatile.lean` and `values` resolution; prove the volatile preservation lemmas and that views ignore volatile state and `values` under as-of/history returns statement objects only; index (volatile-state)
- [x] 8.4 Scenario tests for volatile-state (upsert, clear, failure, not a statement, now-only resolution, statement wins, speculation sees its own writes)

## 9. Never-forget invariant over every program

- [x] 9.1 Prove `Preserves` closure under `pure`/`bind` and, by induction on `TxProg`, `transact_wf_extends` for every program, clock reading and option set; index (statement-lifecycle: immutable content, live to retracted once, nothing deleted, no self-reference)
- [x] 9.2 Prove the eid corollaries (retraction never changes, new eids above every previously issued eid); index (statement-lifecycle: Eids are never reused)
- [x] 9.3 Scenario tests for statement-lifecycle, including the trigger run over random operations

## 10. Temporal views

- [x] 10.1 Implement `View/Spec.lean` and `View/Read.lean`: selectors, `triples` (as-of masking, ascending eid, no interning), `resolveInstant`, `eventsSince` (Rust order)
- [x] 10.2 Prove as-of = replay of the event log and as-of `a.lastT` on any extension = now on `a`; index (temporal-views: As-of equals replay of the log)
- [x] 10.3 Prove `resolveInstant` = largest `t` with instant ≤ `ms`, its monotonicity and `resolveInstant (instant t) = t`; prove valid-at commutes with the transaction-time selection; index (temporal-views: As-of by instant)
- [x] 10.4 Scenario tests for temporal-views (selector combinations, as-of/history boundaries, instants, valid-at boundaries, lookup, unknown constant, event log) and the random-sequence replay property on SQLite

## 11. Speculation and dry run

- [x] 11.1 Implement `speculateCore` and `dryRunCore` generic over `Store` (savepoint, query on the writer state, rollback, burn only advanced id counters, separate burn on failure)
- [x] 11.2 Prove speculation purity (only id counters change, every view read unchanged, query sees the speculative state, allocated ids below the new counters) and dry-run report equality with commit; index (speculative-transactions)
- [x] 11.3 Scenario tests for speculative-transactions on both stores, including burned ids after reopen and failures inside speculation

## 12. Merge laws

- [x] 12.1 Implement `Model/Merge.lean` (`StmtSet` strictly sorted by eid, `RowState.join`, `merge`) with no public database operation
- [x] 12.2 Prove pointwise `lookup (merge a b) = join …`, extensionality of strictly sorted sets, and commutativity, associativity, idempotence; index (merge-laws: Merge laws)
- [x] 12.3 Prove never-forget preservation under content agreement and row-level `WF` preservation; index (merge-laws: Merge preserves never forget)
- [x] 12.4 Randomised tests of the merge scenarios and a check that no public operation merges

## 13. Shell, concurrency and clocks

- [x] 13.1 Implement `Shell/Clock.lean` (system clock, manual clock) and the `Int64` range checks at the SQLite boundary
- [x] 13.2 Implement `Shell/Pool.lean` and `Shell/Db.lean` (`open` with readers default 4 and busy timeout, mutex-guarded writer with `BEGIN IMMEDIATE`, `transact`, `dryRun`, `speculate`, `withView` pinned to one read transaction with `basisT`, commit-only term cache)
- [x] 13.3 Concurrency tests: 8×100 concurrent transactions, concurrent unique upsert, two handles on one file, reads during a long write, pool exhaustion, stable reads within a view, failed intern not leaking, readers during speculation
- [x] 13.4 Concurrency oracle test: N readers + 1 writer with random programs; replay the committed log on the model and compare every recorded read with the model at its basis

## 14. Refinement, differential and benchmarks

- [x] 14.1 Random `TxProg` generator (all verbs, failures, dry runs, speculation, manual clock) and the refinement suite comparing results, reports, errors, every view at every `t` and table contents between `ModelStore` and `SqliteStore`
- [x] 14.2 Differential suite against the pinned Rust oracle: same scripts and manual clock, canonical dumps of `triple`, `term`, `tx`, `meta`, `volatile`, `pred_multi` and reports equal; cross-open files in both directions
- [x] 14.3 Report-only write benchmarks (assert, supersede) against Rust on the shared harness (D14)

## 15. Documentation and validation

- [x] 15.1 Update `lat.md/` (architecture: engine and free-monad bodies, store operations, shell; verification: Tier 1 theorem list; decisions or a new section for the listed deviations: IO-free bodies, per-view snapshots, `Int64` boundary checks) and add `@lat:` refs from the new modules
- [x] 15.2 Run `lat check` until it passes
- [x] 15.3 Confirm the theorem index covers every requirement with a machine-checked scenario and CI's axiom check passes
- [x] 15.4 Run `openspec validate m2-verified-store --strict` until it passes
