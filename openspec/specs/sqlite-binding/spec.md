# sqlite-binding Specification

## Purpose
Defines how the Lean build reaches SQLite: through the pinned leansqlite binding and its bundled SQLite, checked against every need before use, configured like the Rust build so files stay compatible, with exact value transfer and typed errors (D8).

## Requirements

### Requirement: Pinned leansqlite with bundled SQLite
The runtime SHALL reach SQLite only through leansqlite pinned to an exact commit, using the SQLite amalgamation that leansqlite bundles. The linked SQLite SHALL support STRICT tables, partial and expression indexes and WAL mode, and SHALL be compiled thread-safe. No hand-written C for storage SHALL exist in this repository.

#### Scenario: Version floor
- **WHEN** the executable reports its linked SQLite version and compile options
- **THEN** the version is at least 3.37.0 and the thread-safety option is not 0

### Requirement: Gap check before use
Before the SQLite store is written, a gap check SHALL be recorded that lists each need below with its status (supported directly, supported through SQL, or gap) and an executable probe for it: opening read-write-create and read-only; WAL journal mode and `synchronous = NORMAL`; busy timeout; `BEGIN IMMEDIATE`, `COMMIT`, `ROLLBACK`; read transactions holding one snapshot; `SAVEPOINT`, `ROLLBACK TO`, `RELEASE`; prepared statements reused with reset and rebinding; binding and reading signed 64-bit integers, text, blobs, NULL and doubles; distinguishing NULL from zero; stepping rows in order and stopping early; the changed-row count; primary and extended result codes with messages; use of a connection from a thread other than the one that opened it; files larger than 2 GiB on 64-bit platforms; and reading the SQLite version and compile options.

#### Scenario: Probes pass
- **WHEN** the gap-check probes run on a supported platform
- **THEN** every need recorded as supported passes its probe

#### Scenario: Gap found
- **WHEN** a need has no direct or SQL-level support
- **THEN** it is recorded as a gap with the chosen closure, and the SQLite store is not built on it until the closure is pinned

### Requirement: Gap closure without local C
A gap SHALL be closed, in order of preference, by plain SQL through the statement interface, by a change merged into leansqlite and pinned, or by a pinned fork of leansqlite carrying that change until it is merged. A gap SHALL NOT be closed by C code in this repository.

#### Scenario: Pragma-level need
- **WHEN** WAL mode is not exposed as a binding call
- **THEN** it is set by executing `PRAGMA journal_mode = WAL` through a statement, and the gap check records it as supported through SQL

### Requirement: Connection setup compatible with Rust
The writer connection SHALL open read-write and create the file if missing, SHALL use WAL journal mode, `synchronous = NORMAL` and a configurable busy timeout, and SHALL begin write transactions with `BEGIN IMMEDIATE`. Reader connections SHALL open read-only on the same file. Opening a file with the Lean build SHALL NOT change its journal mode, schema or statistics tables.

#### Scenario: Rust file opened by Lean
- **WHEN** a file written by the pinned Rust build is opened and closed by the Lean build without writes
- **THEN** its schema, rows, statistics tables and journal mode are unchanged

#### Scenario: Readers cannot write
- **WHEN** a write statement is attempted on a reader connection
- **THEN** it fails with a storage error and the file is unchanged

### Requirement: Exact value transfer
Every signed 64-bit integer SHALL round-trip through bind and read unchanged, including the minimum and maximum values. NULL SHALL be distinguishable from zero and from empty text. Text SHALL round-trip byte for byte as UTF-8, including embedded NUL characters. Doubles SHALL round-trip with the normalization SQLite applies to REAL columns (NaN stored as NULL, negative zero read back as positive zero), and the binding SHALL expose exactly that behaviour, not mask it.

#### Scenario: Integer extremes
- **WHEN** −2⁶³, −1, 0 and 2⁶³ − 1 are bound into an INTEGER column and read back
- **THEN** each value is returned unchanged

#### Scenario: Embedded NUL
- **WHEN** a text value containing a NUL character is stored and read back
- **THEN** the same bytes are returned

### Requirement: Typed errors with result codes
Every failure reported by SQLite SHALL reach the store as an error carrying the primary result code, the extended result code and the message. Aborts raised by the format-1 never-forget triggers SHALL be recognized and reported as the corresponding store violations.

#### Scenario: Trigger abort
- **WHEN** a statement that would delete a triple row is executed directly on a Lean connection
- **THEN** it fails, the error carries the constraint result code and the trigger's message, and the row is unchanged

### Requirement: No SQL table functions or user functions
The Lean build SHALL NOT register SQL table functions or SQL user functions on its connections. In particular `tm_path`, `rarray` and the Rust SQL UDFs SHALL be unavailable through SQL; paths remain available through every other surface. This is a listed deviation from the Rust build (D6, D8) and SHALL appear in the oracle's deviation registry. The file format SHALL be unaffected.

#### Scenario: tm_path through SQL
- **WHEN** `SELECT * FROM tm_path(1, 'knows+', 'REACH')` is prepared on a connection opened by the Lean build
- **THEN** preparation fails with a storage error, and the same file still opens and works in the Rust build
