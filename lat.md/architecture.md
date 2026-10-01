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

- `Tiramemsu` (sources in `src/Tiramemsu/`): everything that is compiled and linked. Imports `Init`, `Std` and leansqlite's `SQLite.FFI`/`SQLite.LowLevel` only; any runtime `Lean.*` import needs an entry in `policy/toolchain-imports.txt` (empty), so the shell carries its own JSON (`Tiramemsu.Shell.Json`).
- `TiramemsuProofs` (`TiramemsuProofs/`): theorems about `Tiramemsu` definitions. May import Mathlib. Never linked into an executable.
- `tiramemsu` executable (`Main.lean`): `version` and the oracle `driver`. `abi/`: the C shim and header (M6).
- Tooling, never linked into the runtime: `policy-check` and `oracle` (sources in `tools/`), `tiramemsu-tests` (`Test/`).

The default build is the two libraries and the executable, so a build that compiles the code also checks the proofs. Lean sources of the runtime and the tools sit under `src/` and `tools/` because a root `Tiramemsu/`, `Policy/` or `Oracle/` would share a directory with the `tiramemsu` link, `policy/` or `oracle/` on case-insensitive filesystems.

Pins: toolchain `leanprover/lean4:v4.34.0`, Mathlib tag `v4.34.0` (`5ed29652…`), leansqlite `f9cdb9ea…`; `scripts/check-pins.sh` checks that the toolchain equals Mathlib's and that every manifest entry is an exact commit.

## Store Abstraction

The engine is written once, generic over a `Store` interface, so the same code runs on the proof model and on SQLite.

- The interface offers ordered range scans over the index orders (`spo`, `pos`, `osp`, live and history families), appends of statement, term and tx rows, the single retraction update, counters, and savepoints.
- `ModelStore` is a pure value (lists of rows); all theorems are stated over it.
- `SqliteStore` implements the interface with leansqlite. It is linked to the model by refinement tests, not by axioms. See [[verification#Trusted Base]].
- Transaction bodies are IO-free programs (a free monad over the memory verbs) interpreted over either store, so theorems cover every body by induction. A nested write on the same database cannot be expressed, unlike Rust's runtime re-entrancy error.
- Speculation is a discarded pure state on the model and a savepoint on SQLite.

### Index Families

Scans run over nine families, each mirroring one format-1 index with the statement id appended, so the contract order is the order SQLite stores. Defined in `Tiramemsu.Store.Order`.

| Family | Key | Max prefix | Rows |
|---|---|---|---|
| live spo / pos / osp | permutation, t_ret, v_from, v_to, eid | 3 | live |
| history spo / pos / osp | permutation, t_add descending, t_ret, v_from, v_to, eid | 3 | all |
| valid | p, v_from, v_to, eid | 1 | live |
| added log | t_add, eid | 0 | all |
| retracted log | t_ret, ret_kind, eid | 0 | retracted |

Values compare as signed 64-bit integers and an absent value sorts first. Bounds constrain the first key column after the prefix by value, and an absent value never satisfies a bound. Live and valid families accept only the `now` view.

### Interface

The classes `ReadStore`, `WriteStore` and `SnapshotStore` in `Tiramemsu.Store.Interface`; scans are ordered folds with early exit, so later joins seek with a lower bound and stop without materializing.

`ReadStore` has the scan and the point reads (triple, term by id and by key, transaction by number and latest at or before an instant, counter, volatile rows, `pred_multi`). `WriteStore` adds the appends, the single retraction, counters, volatile rows, `pred_multi`, `begin`/`commit`/`rollback` and savepoints. `SnapshotStore` hands out readers that see the committed state as of `beginRead`.

### Model Store

`ModelStore` in `Tiramemsu.Store.Model` is the pure implementation: lists of rows, a committed and a current state, a transaction flag and a savepoint stack.

Every write is a `WriteOp` whose `run` checks misuse and its violation first and returns the error with the state untouched; the monad is `StateT ModelStore (Except StoreError)`, so `tryCatch` restores the state as SQLite's statement-level abort does. The term `num` column is normalized as SQLite stores a REAL (NaN to absent, −0.0 to +0.0). The properties proven about it are in [[verification#Proven Store Properties]].

## SQLite Boundary

SQLite keeps the Rust file format but evaluates no queries. See [[decisions#D3 SQLite As Sorted Index Backend]].

- Schema DDL and the never-forget triggers are byte-identical to Rust format 1, so either implementation opens the other's files and plain-SQLite tools are still blocked from deleting.
- Every read is a prepared range statement on a covering index; joins, filters, optionals, aggregates and paths run in Lean.
- Not ported: SQL codegen, SQL UDFs, the `rarray` table function and `tm_path` as a SQL table function.
- The Lean build writes no planner statistics (`sqlite_stat*`, `PRAGMA optimize`); it never asks SQLite to plan a join.
- leansqlite exposes SQLite's REAL normalization (NaN to NULL, −0.0 to +0.0) and builds SQLite with `SQLITE_DISABLE_LFS`, which has no effect on 64-bit platforms; the gap check probes a file over 2 GiB. See [[verification#Trusted Base#leansqlite Gap Check]].

### Scan SQL

`Tiramemsu.Sqlite.Sql` holds one fixed statement per scan shape (family, prefix length, bound shapes, view shape), so SQL text never depends on values and statements are prepared once per connection.

Each scan has an explicit `ORDER BY` equal to the family key, so order never depends on the plan, and `INDEXED BY` the family's index. The live and valid families state `t_ret IS NULL` verbatim so their partial indexes qualify; on the full indexes the `now` view is `+t_ret IS NULL`, the same predicate but not an index term, because SQLite stops using index order after a column constrained by a non-seek `IS NULL`.

The plan test (`tiramemsu-tests plan`) reports what remains: no shape is covering, since a scan returns whole rows and the format-1 indexes lack `t_add` and `ret_kind` (live) or `ret_kind` (history); live scans with a prefix shorter than three need a block sort of `v_from, v_to, eid` within equal triples.

### SqliteStore

`Tiramemsu.Sqlite.Store` implements the interface over one writer connection and pooled reader connections; it tracks the transaction and savepoint state itself, so misuse never reaches SQL.

- Connections open through the raw `openV2` with extended result codes; the writer sets WAL, `synchronous = NORMAL`, Rust's `recursive_triggers = ON` and a busy timeout; readers are read-only.
- Text is bound as UTF-8 bytes and cast in SQL, and read back as a blob, because leansqlite's text calls stop at an embedded NUL.
- Retraction is the guarded `UPDATE … WHERE eid = ? AND t_ret IS NULL`; with no changed row a lookup reports not-found or retract-once. Trigger aborts and unique-index failures map to violations; any other SQLite failure inside a write transaction rolls it back.
- A reader begins with `BEGIN` and an immediate read of `meta`, which pins its WAL snapshot.

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
