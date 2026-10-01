## Why

Cyclic and skewed basic graph patterns are where nested-loop joins collapse: the Rust build, which leaves them to SQLite's nested loops, measured 41× slower than an intersection join on a hub-and-spoke graph and 36–104× slower on layered graphs (Rust `bench/triangles`). M3a gives v1 a proven index nested-loop join (INLJ); M3b completes the hybrid of D13 with a worst-case-optimal Leapfrog Triejoin (LFTJ), proven equal to the reference join semantics for every variable order, so that the planner choosing between them needs no proof.

## What Changes

- Add a Leapfrog Triejoin operator in the runtime `Tiramemsu` library: per-pattern trie iterators over the `live_*`/`hist_*` index orders `spo`, `pos`, `osp` under each pattern's own view (prefix seeks, or seeks confirmed by an existence check when a constant column follows a variable column), an in-memory sorted trie when no index order fits the chosen variable order, leapfrog intersection per variable, and leaf expansion that restores bag multiplicities.
- Prove in `TiramemsuProofs` (Tier 2, D2): for every variable order that is a permutation of the region's variables, the LFTJ result is bag-equal to the reference natural-join denotation of the BGP from M3a; leapfrog intersection computes exact sorted intersection; the operator is total by a well-founded measure (no fuel, no `partial`). The only trusted assumption is the store contract that range scans return matching rows in key order (D3, D7); a violated order is detected and reported, never silently mis-joined.
- Add an unverified join planner whose output is correctness-irrelevant by construction: every plan passes a decidable validity check before execution, and every valid plan is covered by the INLJ theorem (M3a) or the LFTJ theorem (this change). The planner routes cyclic BGPs (GYO reduction) to LFTJ and acyclic ones to INLJ, orders patterns and variables from cached per-predicate counts refreshed after commit, produces deterministic plans, and shows them through explain.
- Add benchmark fixtures ported from Rust `bench/triangles` (uniform, hub-and-spoke, layered) and a skewed plan-quality fixture to the M0 harness; Lean must beat Rust on the hub-and-spoke and layered fixtures, report-only until the M6 gate (D14).
- Deviations from Rust (D6), listed in the specs: cyclic BGPs no longer run as SQLite nested loops; row order of unordered results may differ from Rust (results stay bag-equal); explain shows the Lean join plan instead of SQLite's `EXPLAIN QUERY PLAN`; the planner reads its own per-predicate counts, not `sqlite_stat1`/`sqlite_stat4`.

## Capabilities

### New Capabilities

- `leapfrog-triejoin`: LFTJ over sorted trie iterators built from index range scans under any per-pattern view; leapfrog intersection; bag-equality with the reference BGP semantics for every variable order; totality; store-contract violation detection.
- `join-planner`: cyclicity-based routing between LFTJ and INLJ, plan validity gate, cardinality estimates from cached per-predicate counts, deterministic pattern and variable ordering, planner options, explain output for join plans, and the triangle and plan-quality benchmarks.

### Modified Capabilities

None. M3a's `query-semantics` and `nested-loop-join` requirements are used unchanged; the planner supplies INLJ with a pattern order through the interface M3a already exposes.

## Impact

- New runtime modules under `Tiramemsu/Exec/Lftj/` and `Tiramemsu/Plan/`; new proof modules under `TiramemsuProofs/Exec/Lftj/` and `TiramemsuProofs/Plan/`; theorem index entries for every proven requirement (verification.md, Proof Policy).
- Depends on M0 (Store interface, ordered range scans with a lower bound, store contract, benchmark harness, Rust oracle pin), M2 (views, commit hook for cache refresh) and M3a (IR, reference denotation, INLJ and its theorem, explain surface, Lean API and CLI).
- No file-format change, no new dependency, no SQL evaluation added (D3); SQLite statistics tables written by Rust are left untouched.
- Benchmarks gain `triangles` and `plan-quality` suites against the pinned Rust build; results are reported, not gated, until M6 (D14).
