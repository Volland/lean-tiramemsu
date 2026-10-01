# storage-format Specification

## Purpose
Defines the on-disk format version 1 that the Lean build shares with the Rust build. It covers the SQLite schema and never-forget triggers, connection settings, the `meta` counters, how files are created and opened, reserved names, and file interchange between the two builds.

## Requirements

### Requirement: Format-1 schema is identical to Rust
A new database SHALL contain exactly the format-1 objects, created from statement text identical to the pinned Rust build's:
- the STRICT tables `meta`, `term`, `tx`, `triple` and `pred_multi`, and the WITHOUT ROWID STRICT table `volatile`;
- the indexes `term_key`, `term_num`, `tx_instant`, `live_spo`, `live_pos`, `live_osp`, `hist_spo`, `hist_pos`, `hist_osp`, `valid_p`, `log_add` and `log_ret`;
- the view `event`;
- the triggers `triple_no_delete`, `triple_retract_once`, `triple_no_replace`, `term_no_replace`, `tx_no_replace`, `term_no_delete`, `term_no_update`, `tx_no_delete` and `tx_no_update`.

The `(type, name, tbl_name, sql)` rows of `sqlite_schema`, in creation order, SHALL be byte-identical to those of a fresh file created by Rust.

#### Scenario: Schema dump matches Rust
- **WHEN** a fresh file is created by the Lean build and another by the pinned Rust build
- **THEN** `SELECT type, name, tbl_name, sql FROM sqlite_schema ORDER BY rowid` returns identical rows from both

#### Scenario: STRICT rejects wrong types
- **WHEN** a raw SQLite connection inserts TEXT into `triple.s` of a Lean-created file
- **THEN** SQLite rejects the insert

### Requirement: Never-forget triggers protect every file
In every file, raw SQLite writes SHALL be aborted with these messages:

| Operation | Message |
|---|---|
| `DELETE` on `triple` | `tiramemsu: triples are never deleted` |
| An `UPDATE` on `triple` other than setting `t_ret` (with `ret_kind`) on a live row with all other content unchanged | `tiramemsu: only a single retraction is allowed` |
| An `INSERT`, including `INSERT OR REPLACE`, of an existing `triple.eid` | `tiramemsu: eids are never reused` |
| An `INSERT`, including `INSERT OR REPLACE`, of an existing `term.id` | `tiramemsu: term ids are never reused` |
| An `INSERT`, including `INSERT OR REPLACE`, of an existing `tx.t` | `tiramemsu: transaction numbers are never reused` |
| `DELETE` on `term` | `tiramemsu: terms are never deleted` |
| `UPDATE` on `term` | `tiramemsu: terms are immutable` |
| `DELETE` on `tx` | `tiramemsu: transactions are never deleted` |
| `UPDATE` on `tx` | `tiramemsu: transactions are immutable` |

The `meta`, `volatile` and `pred_multi` tables SHALL NOT be protected.

#### Scenario: Raw deletes and rewrites
- **WHEN** a plain SQLite connection runs `DELETE FROM term`, `UPDATE tx SET instant = 0`, and `REPLACE INTO term` with an existing id, against a Lean-created file holding rows
- **THEN** each statement fails with its message, and the rows are unchanged

#### Scenario: Second retraction
- **WHEN** a plain SQLite connection sets `t_ret = 12` on a `triple` row whose `t_ret` is 9
- **THEN** the update fails with `tiramemsu: only a single retraction is allowed`

#### Scenario: Legal retraction
- **WHEN** a plain SQLite connection sets `t_ret = 9, ret_kind = 0` on a live `triple` row
- **THEN** the update succeeds

### Requirement: Connection settings
Every engine connection SHALL use `synchronous = NORMAL` and `recursive_triggers = ON`. After the file is initialized or checked, the database SHALL use `journal_mode = WAL`.

#### Scenario: WAL after open
- **WHEN** a file is opened by the Lean build and `PRAGMA journal_mode` is queried on any engine connection
- **THEN** the result is `wal`

### Requirement: Creating a database
Opening a path that has no file, a zero-length file, or a SQLite file with no objects other than `sqlite_*` ones SHALL initialize it within one immediate transaction. That transaction SHALL create every format-1 object, then insert the `meta` rows in this order: `format_version` 1, `next_term` 1, `next_node` 1, `next_bnode` 1, `next_stmt` 1, `last_t` 0, `last_instant` 0, `multi_version` 0. If initialization fails, the open SHALL fail and leave no format-1 object in the file.

#### Scenario: Fresh counters
- **WHEN** a database is created
- **THEN** `meta` holds exactly the eight rows above, and `term`, `tx`, `triple`, `volatile` and `pred_multi` are empty

#### Scenario: Failed initialization leaves nothing
- **WHEN** initialization fails part-way
- **THEN** the open fails, and a later open initializes the file from scratch

### Requirement: Meta counters
`meta` SHALL hold exactly the integer keys `format_version`, `next_term`, `next_node`, `next_bnode`, `next_stmt`, `last_t`, `last_instant` and `multi_version`. Every engine id SHALL be allocated from its counter, never from an existing maximum. Every counter SHALL only increase. Allocated counter values SHALL respect the object-encoding bounds:
- `next_node`, `next_bnode` and `next_stmt` SHALL never exceed `2^48`, and `last_t` SHALL never exceed `2^48 − 1`;
- `next_term` SHALL never exceed `2^60`.

Opening a file whose `meta` lacks one of these keys SHALL fail without modifying the file.

#### Scenario: Missing counter
- **WHEN** a file whose `meta` has no `next_stmt` row is opened
- **THEN** the open fails, and the file is unchanged

#### Scenario: Counters resume after reopen
- **WHEN** a file whose `next_term` is 57 is closed and reopened, and a new term is interned
- **THEN** the new term receives id 57

### Requirement: Format version checks
Opening a file whose `meta.format_version` is greater than 1 SHALL fail with `FormatVersion { found, supported: 1 }` and SHALL leave the file unchanged. A version below 1 has no migration, so it SHALL fail in the same way. Opening a file that has objects but no `meta` table, or no `format_version` row, SHALL fail with `ForeignFile` and SHALL create nothing. Any future migration SHALL run in order inside the opening transaction. It SHALL only add tables, columns, indexes, views or triggers, and SHALL set `format_version` at its end, so a failed migration leaves the file at its original version.

#### Scenario: File from a newer build
- **WHEN** a file with `format_version = 2` is opened
- **THEN** opening fails with `FormatVersion { found: 2, supported: 1 }`, and the file's bytes are unchanged

#### Scenario: Unrelated SQLite database
- **WHEN** a SQLite file holding only a table `customers` is opened
- **THEN** opening fails with `ForeignFile`, and the file still holds only `customers`

### Requirement: Opening preserves contents
Opening an existing format-1 file SHALL NOT modify any row of `term`, `tx`, `triple`, `meta`, `volatile` or `pred_multi`.

#### Scenario: Reopen is read-only on data
- **WHEN** a Rust-written fixture is opened and closed by the Lean build
- **THEN** a dump of every table, in rowid order, is identical before and after

### Requirement: Reserved names
Format 1 SHALL NOT create the table `seal_key`, the table `term_fts`, or any object whose name starts with `vec_`. These names are reserved for later formats, alongside tag 15 `SEALED`.

#### Scenario: Reserved names are absent
- **WHEN** the schema of a fresh or reopened Lean-created file is inspected
- **THEN** no object is named `seal_key` or `term_fts`, and none starts with `vec_`

### Requirement: Planner statistics are outside the format
SQLite's `sqlite_stat1` and `sqlite_stat4` tables SHALL NOT be part of the format. The Lean build SHALL open files with or without them, SHALL NOT depend on them for any result, and is not required to create or refresh them. This is a listed deviation: Rust runs `PRAGMA optimize` at open, and the Lean build evaluates no SQL plans.

#### Scenario: Statistics present or absent
- **WHEN** a Rust-written file with `sqlite_stat1` rows and a Lean-written file without them are each opened by both builds
- **THEN** every open succeeds, and decoded contents are identical

### Requirement: Files interchange with Rust
A file written by the pinned Rust build SHALL open in the Lean build, and every ObjectId in its `triple` and `term` tables SHALL decode to the value Rust decodes it to. A file created by the Lean build, with terms interned by it, SHALL open in the Rust build, with the same decoded terms. This SHALL be checked by the differential oracle.

#### Scenario: Rust fixture read by Lean
- **WHEN** Rust writes a fixture with every tag, every literal edge case of the codec specs, and retracted statements, and Lean opens it
- **THEN** Lean's canonical dump of every statement and term equals Rust's

#### Scenario: Lean file read by Rust
- **WHEN** Lean creates a file and interns a random set of dictionary values, and Rust opens it
- **THEN** Rust opens it without error or migration, and decodes every term to the value Lean interned
