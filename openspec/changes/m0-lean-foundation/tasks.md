## 1. Prerequisites and pins

- [x] 1.1 PREREQUISITE, owner, outside this repository (not done by this change): land the Rust `reserve-replica-id` change in `../tiramemsu` with the origin-bit option chosen by D15, and archive it there; record the resulting commit hash here when done — landed as `cb53154a90445bd13d6e41b77a3db94744ea3a83` (archived at `openspec/changes/archive/2026-10-01-reserve-replica-id`)
- [x] 1.2 Select the Mathlib commit whose `lean-toolchain` leansqlite builds on; record both commits and the toolchain release in design notes of the PR
- [x] 1.3 Write `lean-toolchain` and `lakefile.lean` with `require mathlib` and `require sqlite` (leansqlite) at those exact commits; commit the generated `lake-manifest.json`
- [x] 1.4 Add `scripts/ci.sh` as the single CI entry point (build, policy check, tests, oracle) and the CI workflow running it on macOS arm64 and Linux x86_64

## 2. Lake project skeleton

- [x] 2.1 Create targets `Tiramemsu` (root `Tiramemsu.lean`), `TiramemsuProofs`, exe `tiramemsu` (`Main.lean`), and non-default tooling exes `policy-check`, `tiramemsu-tests`, `oracle`; default build = the first three
- [x] 2.2 Implement `tiramemsu version` printing program version, linked SQLite version (via leansqlite) and supported format version 1
- [x] 2.3 Add the toolchain-pin consistency check (project toolchain = pinned Mathlib's toolchain; every manifest entry has an exact rev) to `scripts/ci.sh`
- [x] 2.4 Add the native-binary checks: dynamic dependencies listed by `otool -L`/`ldd` contain no Lean shared library; executable's version command runs with no toolchain on `PATH`
- [ ] 2.5 Add `.gitignore` for `.lake/`, `.oracle/`, generated C; verify a fresh clone builds with the default target on both platforms

## 3. leansqlite gap check

- [x] 3.1 Write the gap-check probes in `tiramemsu-tests probe`, one per need listed in the sqlite-binding spec (open flags, WAL + `synchronous`, busy timeout, `BEGIN IMMEDIATE`/`COMMIT`/`ROLLBACK`, read snapshot, savepoints, statement reuse, Int64/text/blob/NULL/double binding, NULL vs 0, ordered stepping with early stop, changes count, result codes, cross-thread connection use, version and compile options)
- [x] 3.2 Run the probes; record each need's status (direct / via SQL / gap) and closure in a gap-check table committed next to the probes
- [x] 3.3 Close every gap per design Decision 7 (SQL, upstream PR pinned, or pinned fork); re-pin leansqlite if needed and rerun 3.2 until no blocking gap remains
- [x] 3.4 Add the value-fidelity probes: Int64 extremes, text with NUL, REAL normalization of NaN and −0.0, NULL distinct from 0 and empty text
- [x] 3.5 Add the nightly-only probe writing and scanning a file larger than 2 GiB on 64-bit platforms
- [x] 3.6 Add the probe that preparing `SELECT * FROM tm_path(1, 'knows+', 'REACH')` fails on a Lean connection, and that no user function is registered

## 4. Proof policy checker

- [x] 4.1 Create `policy/verified-modules.txt`, `policy/toolchain-imports.txt` (empty), `policy/bv-decide-allowlist.txt` (empty) and `policy/theorem-index.toml` (empty)
- [x] 4.2 Implement `policy-check` environment rules: no `sorryAx`, no axiom declared in project modules, theorem axiom set within `propext`/`Classical.choice`/`Quot.sound` plus `Lean.ofReduceBool` and its dependencies for allowlisted names only
- [x] 4.3 Implement verified-module rules: no `unsafe` or opaque (`opaque`/`partial`) constants; `implemented_by`/`extern` only with a `@[csimp]` theorem; imports only Init, Std and verified modules
- [x] 4.4 Implement source rules: no `native_decide`/`decide +native` in either library; `bv_decide` only in `TiramemsuProofs.Codec.*`; allowlist entries only from those modules; no C/C++/header files outside `abi/` and build output
- [x] 4.5 Implement the runtime import-closure rule: modules reachable from `Tiramemsu` and `Main` have roots in Init, Std, leansqlite, Tiramemsu or the toolchain-import allowlist, reporting the import chain on failure
- [x] 4.6 Implement the theorem-index rule: parse `openspec/specs/**/spec.md` for `Machine-checked` scenarios; strict mode for project specs, report mode for active changes, `--change <name> --strict` for a pre-archive run
- [x] 4.7 Add `Policy/Fixtures` with one seeded violation per rule and the checker self-test asserting each is rejected with its rule id; wire both into `scripts/ci.sh`

## 5. Store types, model and proofs

- [x] 5.1 Implement `Tiramemsu/Store/Types.lean`: rows, `TxSel`, `ValidSel`, `View`, `Family`, `Bound`, `ScanSpec`, `Violation`, `StoreError`; add the module to the verified list
- [x] 5.2 Implement `Tiramemsu/Store/Order.lean`: per-family key extraction, signed/absent-first comparison, `keyLt`, `ScanSpec.Valid`, `ScanSpec.Matches` (prefix, bounds, view predicate)
- [x] 5.3 Prove the key-order theorems (strict order; totality on distinct eids) in `TiramemsuProofs/Store/Order.lean`; register them under "The model store is exact and ordered"
- [x] 5.4 Implement `Tiramemsu/Store/Interface.lean`: `ReadStore`, `WriteStore`, reader `beginRead`/`endRead`
- [x] 5.5 Implement `Tiramemsu/Store/Model.lean`: `ModelState`, `ModelStore`, all reads (scan as an ordered fold with early exit), appends with violations and REAL normalization, retraction, counters, volatile, `pred_multi`, transactions, savepoints, misuse errors
- [x] 5.6 Prove scan exactness, duplicate-freedom, sortedness, invalid-scan failure and the fold/list correspondence; register them in the theorem index
- [x] 5.7 Prove write atomicity: id-uniqueness preservation, unchanged state on failure, append and retraction effects, rollback, savepoint rollback, commit; register them under "Model writes are atomic and never overwrite"
- [x] 5.8 Unit-test the model against the store-contract scenarios (signed order, history newest first, seek, early stop, views, point reads, savepoints, misuse)
- [x] 5.9 Run `policy-check` strict on this change's specs; both proven requirements are indexed and pass the axiom rule

## 6. SqliteStore

- [x] 6.1 Depends on 1.1 for the pin, else use a provisional Rust build: extract `testdata/format1-schema.sql` from an empty database made by the Rust build (`sqlite_master.sql` in rowid order plus initial `meta` rows); add a check that it matches the pinned build once 8.1 is done
- [x] 6.2 Implement `Tiramemsu/Sqlite/Conn.lean`: writer open (RW, create, WAL, `synchronous = NORMAL`, busy timeout), reader open (read-only), `BEGIN IMMEDIATE`/commit/rollback, savepoints, read transactions that pin the snapshot with an immediate read
- [x] 6.3 Implement `Tiramemsu/Sqlite/Sql.lean`: fixed SQL per (family, prefix length, bound shape, view shape) with explicit `ORDER BY` equal to the family key and the verbatim `t_ret IS NULL` for now; SQL for point reads and writes
- [x] 6.4 Implement `Tiramemsu/Sqlite/Store.lean`: `ReadStore`/`WriteStore` instances with per-connection prepared-statement reuse, transaction-state tracking for misuse errors, retraction via guarded `UPDATE` plus lookup for `notFound`/`retractOnce`, trigger-abort mapping, rollback after storage errors
- [x] 6.5 Add the plan test: `EXPLAIN QUERY PLAN` of every scan shape uses the family's covering index with no temporary B-tree for ordering; shapes that do not are reported
- [x] 6.6 Add the compatibility test: opening and closing a Rust-written file without writes leaves schema, rows, statistics tables and journal mode unchanged
- [x] 6.7 Run the store-contract scenario tests of 5.8 on `SqliteStore`, plus close-during-transaction and reader-cannot-write

## 7. Refinement tests

- [x] 7.1 Implement the seeded operation generator (core `StdGen`): valid and invalid writes, transaction and savepoint control, up to three readers' begin/end, every read kind with random prefixes, bounds and views
- [x] 7.2 Implement the lock-step runner: each op on `ModelStore` and `SqliteStore`, comparing every result including scan order and error variant
- [x] 7.3 Implement delta-debugging minimization and writing failing sequences to `testdata/refine/` as regression cases replayed on every run
- [x] 7.4 Add runs that start from Rust-written fixture files (loaded into both stores)
- [x] 7.5 Wire CI (200 seeds × 300 ops) and nightly (5 000 seeds × 1 000 ops, Rust fixtures) runs into `scripts/ci.sh`

## 8. Differential oracle

- [x] 8.1 After 1.1: write `oracle/RUST_PIN` (commit, evidence path) and the read-only pin check (commit exists; archived `reserve-replica-id` present, active one absent)
- [x] 8.2 Implement the oracle build: `git archive` of the pin into `.oracle/rust-<pin>/` and build of `oracle/rust-driver`; test that the Rust repository's status, branches and worktree list are unchanged
- [x] 8.3 Implement `oracle/rust-driver`: JSON-lines protocol over `tiramemsu-json` (`Database::call` ops) plus `open`, `close`, `rawDump` (plain SQL in primary-key order)
- [x] 8.4 Implement `tiramemsu driver` on the Lean side: protocol, `open`, `close`, `rawDump` through `SqliteStore` reads, `unsupported` for every other op
- [x] 8.5 Implement canonicalization and comparison (sorted keys, exact integers, multiset vs ordered results, lexical doubles, errors by code) with unit tests for each rule
- [x] 8.6 Implement scenarios over shared files (build-tagged steps, handoff after close, compared steps on copies, reproducible mismatch reports)
- [x] 8.7 Create `oracle/deviations.toml` with the `tm_path` and SQL-UDF/`rarray` entries and the matcher logic; test that an unlisted difference fails and a listed one passes
- [x] 8.8 Add the M0 scenario: Rust writes transactions, Lean `rawDump` equals Rust `rawDump`; add it to `scripts/ci.sh`

## 9. Benchmark harness

- [x] 9.1 Implement the deterministic fixture builder (shape of Rust `bench/engine-comparison`, ~11·N statements) through the Rust driver
- [x] 9.2 Implement workload timing grouped by the performance-gate categories, result-equality checks per workload, "not available" for Lean-unsupported workloads, and bytes per statement
- [x] 9.3 Write JSON and Markdown reports with ratios; exit non-zero only on harness errors or result mismatches; add a test that a large ratio still exits successfully
- [x] 9.4 Run `oracle bench` at N = 100 000 and commit the first report

## 10. Documentation and validation

- [x] 10.1 Update `lat.md/`: architecture (Store Abstraction with families, interface and module paths), verification (policy checker rules, theorem index, allowlist files, oracle pin and deviation registry), roadmap (M0 status); add `@lat:` code refs from the store, policy checker and refinement runner
- [x] 10.2 Run `lat check` until all links and code refs pass
- [ ] 10.3 Run `policy-check --change m0-lean-foundation --strict` and `scripts/ci.sh` end to end on both platforms
- [x] 10.4 Run `openspec validate m0-lean-foundation --strict` until it passes
