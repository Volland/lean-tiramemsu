# connection-concurrency Specification

## Purpose
Defines how one database is shared by concurrent callers: a single mutex-guarded writer that serialises every write, a pool of reader connections, and views pinned to one WAL snapshot that is always a committed prefix of the transaction log.

## Requirements

### Requirement: Single writer serialisation

Every transaction, dry run and speculation on a database handle SHALL run one at a time on one writer connection guarded by a mutex, inside a SQLite write transaction taken with `BEGIN IMMEDIATE`, so that each observes every effect committed before it. Concurrent callers SHALL wait rather than fail. Two handles on one file SHALL be serialised by SQLite, waiting up to the busy timeout.

#### Scenario: Concurrent transactions from many tasks
- **WHEN** 8 tasks each commit 100 transactions concurrently
- **THEN** exactly 800 transactions commit, numbered 1 to 800 without gap or duplicate, with strictly increasing instants

#### Scenario: Read-modify-write is atomic
- **WHEN** two tasks concurrently upsert the same value on a `sys:unique` predicate
- **THEN** both receive the same node and exactly one live statement holds the value

#### Scenario: Two handles on one file
- **WHEN** two handles opened on the same file commit concurrently
- **THEN** transaction numbers across both stay gap-free and unique

### Requirement: Reader pool

A database handle SHALL keep a pool of read-only connections, 4 by default and configurable at open. Reads SHALL run on a pooled reader and never wait for the writer. When every reader is busy, a new read SHALL wait for one to be returned.

#### Scenario: Reads during a long write
- **WHEN** a transaction holds the writer and a view read starts on another task
- **THEN** the read completes without waiting for the transaction and sees only committed state

#### Scenario: Pool exhaustion waits
- **WHEN** the pool has 2 readers, both are held by open views, and a third view is opened
- **THEN** the third waits until one view ends and then succeeds

### Requirement: A view is pinned to a committed snapshot

Opening a view on committed state SHALL take one reader and one read transaction for the whole scope of the view, so that every read through it sees the same WAL snapshot; the snapshot SHALL be the state right after some committed transaction `b`, its basis, which the view SHALL expose. Uncommitted writes SHALL never be visible. The reader SHALL return to the pool when the scope ends, whether it ends normally or with an error. (Listed deviation: Rust takes a snapshot per read, not per view.)

#### Scenario: Stable reads within one view
- **WHEN** a view reads a pattern, another task commits a transaction that changes it, and the same view reads it again
- **THEN** both reads return the same rows and the basis is unchanged

#### Scenario: Readers match the model at their snapshot
- **WHEN** N reader tasks repeatedly open views and read now, as-of, history and valid-at views while one writer commits random transactions, and the writer's committed log is afterwards replayed on the model store
- **THEN** every recorded read equals the model's read of the same view at that view's basis

### Requirement: Caches never change results

Shared caches SHALL hold only committed, immutable data: a term interned by a transaction SHALL enter a shared cache only after that transaction commits, and terms from failed transactions, dry runs and speculations SHALL never enter it. Per-predicate statistics MAY lag commits and SHALL affect speed only.

#### Scenario: Failed intern does not leak
- **WHEN** a transaction interns a new string and fails, and a reader then decodes the id that string had
- **THEN** the reader does not return that string

### Requirement: Speculative reads stay on the writer

The query of a speculation SHALL read on the writer connection inside the speculation, seeing its uncommitted state, and SHALL bypass shared caches for uncommitted terms; no pooled reader SHALL see that state.

#### Scenario: Reader during speculation
- **WHEN** a speculation's query is running and another task opens a now view
- **THEN** that view sees only committed state
