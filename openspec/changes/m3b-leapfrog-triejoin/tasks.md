## 1. Preconditions

- [ ] 1.1 Confirm the M0 range scan takes a key prefix, an inclusive lower bound on the next key column and a row limit, and that the M0 scan-contract predicate and its `ModelStore` instance theorem exist; amend M0 first if not (design Risks)
- [ ] 1.2 Confirm M3a exposes the reference denotation of `Join`, the INLJ theorem for every pattern order, a pattern-order input for INLJ, and the explain surface; the join-planner of this change replaces M3a's default pattern ordering (M3a keeps it as the fallback canonical plan); add `join_split` (design §9 item 7) to the proof task list here if M3a lacks it
- [ ] 1.3 Create the module skeleton of design §8 in both libraries and the empty theorem-index entries for every proven requirement; `lake build` passes with the proof-policy gates

## 2. Keys and leapfrog intersection

- [ ] 2.1 Implement `Key` order (signed 64-bit), successor with end at `Int64.max`, and the headroom measure; unit tests at `Int64.min`, `-1`, `0`, `Int64.max`
- [ ] 2.2 Implement leapfrog intersection over an abstract level iterator (`key`, `seek`, `atEnd`) with `termination_by` on headroom and the run-time monotonicity check
- [ ] 2.3 Prove `leapfrog_spec` (sorted output, membership iff in every input) for list-backed iterators
- [ ] 2.4 Property-test leapfrog on random sorted key sets including negative and extreme keys

## 3. Level iterators and access kinds

- [ ] 3.1 Implement `Access` (contiguous, skipScan, materialized) and `Access.fits` per design §2, including repeated variables and eid levels
- [ ] 3.2 Implement the store-backed contiguous iterator with the adaptive read-ahead buffer and the store-contract check
- [ ] 3.3 Implement the skip-scan iterator (candidate seek plus existence seek)
- [ ] 3.4 Implement the materialized iterator (constant-prefix scan, filter, project, sort in σ order, group)
- [ ] 3.5 Implement leaf groups and leaf multiplicity for `SetOfTriples`, `BagOfEids` and eid variables
- [ ] 3.6 Prove `seek_rest` and `level_keys` for each of the three kinds under `ScanContract`
- [ ] 3.7 Prove `leaf_count` for both `graph_set` values and for eid levels
- [ ] 3.8 Test iterators on `SqliteStore` against `ModelStore` with buffer limits 1, 2 and 256 under `Now`, `AsOf`, `History` and `valid At`

## 4. Triejoin operator

- [ ] 4.1 Implement `lftjFold` (levels in σ order, leapfrog per level, leaf expansion with multiplicity product) and `lftjList`
- [ ] 4.2 Prove `lftjFold_eq` (fold equals folding the list)
- [ ] 4.3 Prove the store-independent model lemma: triejoin over faithful sorted tries equals the bag natural join
- [ ] 4.4 Prove `lftj_perm_denote` from 2.3, 3.6, 3.7 and 4.3, and the `ModelStore` corollary
- [ ] 4.5 Prove `lftj_no_contract_error`; confirm with `#print axioms` that 2.3–4.5 stay within the allowed axioms
- [ ] 4.6 Add the faulty-store test (out-of-order keys yield a store-contract error and no rows)
- [ ] 4.7 Add the spec scenarios as tests: triangle under six orders, repeated variable, eid join variable, missing constant, mixed views, history re-assert, non-rotation order, SetOfTriples versus BagOfEids
- [ ] 4.8 Add the random property test: stores, regions of one to six patterns, valid σ, on both stores against the reference denotation

## 5. Planner core

- [ ] 5.1 Implement region extraction from `Join` (stored triple patterns versus the rest)
- [ ] 5.2 Implement GYO cyclicity; unit tests for triangle, four-cycle, chain, star and two patterns sharing two variables
- [ ] 5.3 Implement `JoinPlan`, `JoinPlan.valid`, canonical fallback and region execution dispatch to INLJ (M3a) or LFTJ, with the remaining operands joined by INLJ
- [ ] 5.4 Prove `execRegion_valid` (and `join_split` if needed per 1.2)
- [ ] 5.5 Test the invalid-plan fallback through a planner test hook

## 6. Estimates, ordering and explain

- [ ] 6.1 Implement `PredCounts` with lazy counting scans, bounded constant-prefix probes and the cap
- [ ] 6.2 Hook commit deltas into the writer path (M2 commit) and the stale-stamp check on readers
- [ ] 6.3 Implement the INLJ greedy order and the LFTJ σ heuristic with access choice and the bounded repair pass
- [ ] 6.4 Implement the planner options (`lftj := auto | always | never`, small-input threshold, buffer limit) in the Lean API and CLI
- [ ] 6.5 Implement the explain join-plan section (algorithm, reason, order, per-pattern view, family, index order or in-memory copy, estimate)
- [ ] 6.6 Golden-plan suite over fixed IR and fixed count snapshots, including the repeated-planning determinism check
- [ ] 6.7 Tests for rare-predicate-first, refresh after commit and harmless stale counts
- [ ] 6.8 Differential test: `never`, `auto` and `always` return bag-equal results on the property-test queries

## 7. Benchmarks and Rust oracle

- [ ] 7.1 Port the triangle fixtures with a deterministic generator writing one `.db` file read by both builds
- [ ] 7.2 Port the skewed plan-quality fixture (huge class, rare predicate, churned properties) with fresh and stale count runs
- [ ] 7.3 Run the triangle benchmark against the pinned Rust build; assert equal counts as a hard test and report times and ratios; calibrate the buffer limit
- [ ] 7.4 Calibrate the small-input threshold from the uniform fixture and small cyclic shapes; record values and evidence
- [ ] 7.5 Measure peak memory on the 3 × 600 layered count and add the bounded-memory check
- [ ] 7.6 Add the differential harness case comparing cyclic query results with Rust as multisets

## 8. Documentation and validation

- [ ] 8.1 Update `lat.md/` (architecture: LFTJ, planner, count cache; verification: theorem-index entries for M3b; roadmap: benchmark results and calibrated thresholds; deviations list) with code refs to the new modules
- [ ] 8.2 Run `lat check` until it passes
- [ ] 8.3 Run `openspec validate m3b-leapfrog-triejoin --strict` until it passes
