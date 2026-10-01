# Verification

What is proven, what is trusted, and what is only tested. Proofs are about Lean definitions; the Lean compiler, runtime, C compiler, SQLite and leansqlite are trusted.

## Proof Tiers

Tiers 0–2 are proven in `TiramemsuProofs`; tiers 3–4 are differential-tested. See [[decisions#D2 Proof Scope]].

| Tier | Subject | Milestone | Status |
|---|---|---|---|
| 0 | Codec: ObjectId, doubles, decimals, dates, short strings | M1 | proven |
| 1 | Store state machine: never forget, idempotent assert, supersede replay, cascade = dependents closure, bitemporal views = log replay, speculation purity, monotone instants, merge laws | M2 | proven |
| 2 | Query semantics: IR denotation, join orders, LFTJ, paths, provenance soundness, bundle round-trip | M3 | proven |
| 3 | SPARQL and Cypher lowering to IR | M4–M5 | tested |
| 4 | SqliteStore against ModelStore, shell, C ABI | M0–M6 | tested |

## Proof Policy

Rules enforced by CI so that a proof always covers the code that runs. See [[decisions#D7 Proof Policy]] and [[decisions#D12 Scoped bv_decide]].

- No `sorry`, no `admit`, no user `axiom` in either library.
- Verified modules are total: no `partial`, no `unsafe`. Search loops use explicit fuel with a theorem that the bound suffices.
- `@[implemented_by]` and `@[extern]` are forbidden in verified modules except with a `@[csimp]` equality theorem.
- No `native_decide`. Every headline theorem's axioms are within `propext`, `Classical.choice`, `Quot.sound`, except allowlisted codec theorems that may also use `Lean.ofReduceBool` through `bv_decide`.
- A theorem index maps every spec requirement marked as proven to its theorem name; CI fails if a named theorem is missing. A requirement counts as proven when it has a scenario whose name starts with "Machine-checked".
- The Lean toolchain is pinned to a version Mathlib supports and bumped deliberately.

## Trusted Base

Everything a proof does not cover is listed here, so the verification claim stays exact.

- Lean kernel, compiler, runtime; the C compiler; hardware `Float` arithmetic in query expressions.
- SQLite and leansqlite, through the store contract: a range scan returns exactly the rows matching its key prefix and view predicate, in key order; writes inside a transaction are atomic; WAL readers see a committed prefix; transactions are serializable.
- The shell: IO, the connection pool, the CLI and the C ABI shim.

## Differential Oracle

Tested tiers are checked against the pinned Rust build on shared database files. See [[decisions#D6 Compatible By Contract]].

- Rust is pinned at one commit, recorded in the repository, after the `reserve-replica-id` change lands.
- Harnesses run the same operation sequences and queries on both builds over the same `.db` file and compare canonical results.
- Refinement tests run random operation sequences on `ModelStore` and `SqliteStore` and compare every observable result.
- The W3C SPARQL test suite (M4) and the openCypher TCK (M5) are a second oracle, so bugs shared with Rust are still caught.
