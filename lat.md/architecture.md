# Architecture

The port is two Lean libraries over one abstract store, with SQLite behind a narrow trusted contract and a thin unverified shell for IO, concurrency and the C ABI.

```
 Node.js (koffi)   Python (ctypes)   Lean API / CLI
        \               |                /
         C ABI shim  ── JSON bridge ── Db · View · Tx          (shell, unverified)
                            |
   SPARQL front end   Cypher front end                         (tested, M4–M5)
                \        /
          Logical IR + evaluator (INLJ, LFTJ, paths)           (proven, M3)
                     |
          Store state machine: verbs, cascade, views           (proven, M2)
                     |
          Codec: ObjectId, literals, terms                     (proven, M1)
                     |
      Store interface ── ModelStore (pure, proofs)
                     └── SqliteStore (leansqlite, refinement-tested)
```

## Libraries

The runtime and the proofs are separate Lake libraries so that Mathlib never reaches a binary. See [[decisions#D7 Proof Policy]].

- `Tiramemsu`: everything that is compiled and linked. Imports `Init` and `Std` only; any runtime `Lean.*` import needs an entry in `policy/toolchain-imports.txt` (empty at start), so the bindings carry their own JSON parser.
- `TiramemsuProofs`: theorems about `Tiramemsu` definitions. May import Mathlib. Never linked into an executable.
- `tiramemsu` executable: the CLI. `abi/`: the C shim and header.

## Store Abstraction

The engine is written once, generic over a `Store` interface, so the same code runs on the proof model and on SQLite.

- The interface offers ordered range scans over the index orders (`spo`, `pos`, `osp`, live and history families), appends of statement, term and tx rows, the single retraction update, counters, and savepoints.
- `ModelStore` is a pure value (lists of rows); all theorems are stated over it.
- `SqliteStore` implements the interface with leansqlite. It is linked to the model by refinement tests, not by axioms. See [[verification#Trusted Base]].
- Transaction bodies are IO-free programs (a free monad over the memory verbs) interpreted over either store, so theorems cover every body by induction. A nested write on the same database cannot be expressed, unlike Rust's runtime re-entrancy error.
- Speculation is a discarded pure state on the model and a savepoint on SQLite.

## SQLite Boundary

SQLite keeps the Rust file format but evaluates no queries. See [[decisions#D3 SQLite As Sorted Index Backend]].

- Schema DDL and the never-forget triggers are byte-identical to Rust format 1, so either implementation opens the other's files and plain-SQLite tools are still blocked from deleting.
- Every read is a prepared range statement on a covering index; joins, filters, optionals, aggregates and paths run in Lean.
- Not ported: SQL codegen, SQL UDFs, the `rarray` table function and `tm_path` as a SQL table function.
- The Lean build writes no planner statistics (`sqlite_stat*`, `PRAGMA optimize`); it never asks SQLite to plan a join.
- leansqlite normalizes REAL values (NaN to NULL, −0.0 to +0.0) and may be built with `SQLITE_DISABLE_LFS`; M0's gap check probes files over 2 GiB before anything depends on it.

## Concurrency

One writer and a reader pool, as in Rust; the verified core is pure, so concurrency exists only in the shell. See [[decisions#D10 Writer Plus Reader Pool]].

- The writer connection is guarded by a mutex; transactions use `BEGIN IMMEDIATE`.
- Each View holds a read transaction for its whole scope, so it sees one WAL snapshot: the state after some committed transaction prefix. Rust takes a snapshot per read; this is a listed deviation.
- Caches: the term cache is append-only (terms are immutable); per-predicate counts for join ordering refresh after commit and affect speed only.

## C ABI

One C file exports a JSON-bridge ABI to foreign languages; it contains no logic. See [[decisions#D9 C ABI Shim]].

- Functions: `tm_open`, `tm_call`, `tm_free`, `tm_close`, `tm_version`, all `const char*` in and out.
- The shim initializes the Lean runtime once, registers foreign threads with the runtime and marshals strings. The handle table lives in Lean behind a mutex, so C never holds a Lean object or touches reference counts.
- Operations and JSON forms are those of the Rust JSON bridge, so the Node.js and Python wrappers keep their public API.
