## Why

Every later milestone (M1–M6) proves or tests against things that do not exist yet: a Lake project with a proof library kept out of the binary, CI gates that make "proven" mean something, a `Store` interface whose SQLite implementation is the only trusted storage assumption, and a pinned Rust build to compare against. M0 fixes these contracts before any verified code is written, so that no proof is later invalidated by a change of toolchain, store semantics or oracle (D4, D7).

## What Changes

- New Lake project with a pinned Lean toolchain that Mathlib supports, two libraries (`Tiramemsu` runtime on Lean core + Std + leansqlite; `TiramemsuProofs`, which alone may import Mathlib) and a natively compiled `tiramemsu` executable with the Lean runtime linked statically (D1, D7).
- CI proof gates: no `sorry`/`admit`/user `axiom`; verified modules total (no `partial`, `unsafe`, `opaque`); `implemented_by`/`extern` only with a `@[csimp]` theorem; no `native_decide`; per-theorem axiom-set check; `bv_decide` (and `Lean.ofReduceBool`) only in allowlisted codec proofs (D12); a theorem index mapping every proven requirement to its theorems (D7).
- The abstract `Store` interface and its contract: ordered range scans over every triple index family (live and history `spo`/`pos`/`osp`, `valid_p`, the two log indexes) under a view predicate, appends of triple/term/tx rows, the single retraction update, counters, volatile rows, `pred_multi`, write transactions, savepoints and snapshot reads (D3).
- `ModelStore`, a pure implementation, with machine-checked exactness, ordering and well-formedness of its scans and writes; this is the store every later theorem is stated over.
- `SqliteStore` over pinned leansqlite (D8), preceded by a recorded gap check of leansqlite against every need; refinement tests running random operation sequences on both stores and comparing every observable result.
- Listed deviation (D6, D8): the Lean build registers no SQL table functions or user functions; `tm_path` as a SQL table function, `rarray` and SQL UDFs are not available on its connections. The file format is unaffected.
- Differential oracle: the Rust build pinned at a recorded commit after the Rust `reserve-replica-id` change has landed (D15), a driver protocol both builds speak, canonical result comparison over shared `.db` files, a deviation registry, and a report-only benchmark harness (D6, D14).
- Prerequisite outside this repository: the owner lands `reserve-replica-id` (origin-bit option, per D15) in the Rust repository; this change only records the resulting commit.

## Capabilities

### New Capabilities
- `build-toolchain`: Lake project layout, pinned toolchain and dependencies, the two libraries and the executable, Mathlib confined to proofs, native build and supported platforms.
- `proof-policy`: CI-enforced rules that make every proof cover the code that runs, including the axiom check, the `bv_decide` allowlist and the theorem index.
- `store-contract`: semantics of the abstract Store interface (scans, appends, retraction, counters, transactions, savepoints, snapshots), the pure model and its proven properties, and the refinement tests that link SQLite to the model.
- `sqlite-binding`: the pinned leansqlite dependency, its gap check, connection setup, value fidelity, error mapping, and the dropped SQL table functions.
- `differential-oracle`: the pinned Rust build, the shared driver protocol, canonical comparison over shared files, the deviation registry and the report-only benchmark harness.

### Modified Capabilities
<!-- none: there are no existing specs -->

## Impact

- New repository content: `lakefile`, `lean-toolchain`, `lake-manifest.json`, `Tiramemsu/`, `TiramemsuProofs/`, `Main.lean`, policy checker, test and oracle executables, `oracle/` (Rust driver crate, pin record, deviation registry), `policy/` (verified-module manifest, allowlists, theorem index), CI workflow.
- Dependencies: Lean toolchain (pinned), Mathlib (proofs only), leansqlite with its bundled SQLite amalgamation (runtime); Rust toolchain and the pinned Rust sources for the oracle and benchmarks only.
- External: requires the Rust `reserve-replica-id` change to land in `../tiramemsu` before the pin is recorded; the Rust repository is otherwise only read.
- Later milestones state their theorems over `ModelStore` and register them in the theorem index; M1 replaces the schema fixture used here with byte-identical schema creation.
