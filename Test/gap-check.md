# leansqlite gap check

Recorded result of the gap check of the sqlite-binding spec, for leansqlite
`f9cdb9eacb5c8b8ecc02ee9fd9e568d7d28c1416` with its bundled SQLite 3.51.1. Every row has an
executable probe in `Test/Probe.lean` (`tiramemsu-tests probe`; the large-file probe needs
`--large` and runs in the nightly job).

Status: **direct** (a leansqlite call does it), **via SQL** (a statement through the statement
API does it), **gap** (neither; closure given). No blocking gap was found, so leansqlite is
pinned unchanged: no upstream patch and no fork were needed.

| Need | Status | How | Probe |
|---|---|---|---|
| Open read-write-create | direct | `SQLite.FFI.openV2` with `READWRITE \| CREATE \| EXRESCODE` (the raw call is used because `OpenFlags` has no field for extended result codes) | `open-rwc` |
| Open read-only | direct | `openV2` with `READONLY \| EXRESCODE`; a missing file fails with `SQLITE_CANTOPEN` | `open-readonly` |
| WAL and `synchronous = NORMAL` | via SQL | `PRAGMA journal_mode = WAL`, `PRAGMA synchronous = NORMAL` | `wal-synchronous` |
| Busy timeout | direct | `SQLite.busyTimeout`; a blocked `BEGIN IMMEDIATE` waits about the timeout, then reports `SQLITE_BUSY` | `busy-timeout` |
| `BEGIN IMMEDIATE`, `COMMIT`, `ROLLBACK` | via SQL | `SQLite.exec` | `transactions` |
| Read transaction holding one snapshot | via SQL | `BEGIN` plus an immediate read of `meta` (a deferred transaction snapshots at its first read) | `read-snapshot` |
| `SAVEPOINT`, `ROLLBACK TO`, `RELEASE` | via SQL | `SQLite.exec` with a quoted name | `savepoints` |
| Prepared statements reused with reset and rebinding | direct | `prepare`, `reset`, `clearBindings`, per-connection cache keyed by SQL text | `statement-reuse` |
| Signed 64-bit integers, including extremes | direct | `bindInt64`, `columnInt64` | `int64-extremes` |
| Text, byte for byte, including NUL | gap, closed via SQL | `bindText` passes length −1 and `columnText` builds the string with `lean_mk_string`, so both stop at an embedded NUL. Closure: text is bound as its UTF-8 bytes with `bindBlob` and cast in SQL (`CAST(? AS TEXT)`), and read as `CAST(col AS BLOB)` decoded with `String.fromUTF8?`; the stored value has type `text` | `text-embedded-nul` |
| Blobs | direct | `bindBlob`, `columnBlob` | `bind-read-values` |
| NULL | direct | `bindNull`; `columnType` is read before any conversion | `null-vs-zero-vs-empty` |
| Doubles | direct | `bindFloat`, `columnDouble`; REAL normalization is exposed as is: NaN is stored as NULL, −0.0 reads back as +0.0 | `real-normalization` |
| NULL distinct from zero and empty text | direct | `columnType` | `null-vs-zero-vs-empty` |
| Ordered stepping with early stop | direct | `step`, then `reset` | `ordered-early-stop` |
| Changed-row count | direct | `SQLite.changes` (`sqlite3_changes64`) | `changes` |
| Primary and extended result codes with message | direct | failures arrive as `IO.Error.otherError code message`; connections are opened with `SQLITE_OPEN_EXRESCODE`, so `code` is the extended code and its low byte the primary one; the message is `sqlite3_errmsg` | `result-codes` |
| Connection used from another thread | direct | bundled SQLite is `THREADSAFE=1` (serialized); probe uses a dedicated task | `cross-thread` |
| Files larger than 2 GiB on 64-bit | direct | leansqlite compiles SQLite with `SQLITE_DISABLE_LFS`; on 64-bit platforms `off_t` is 64-bit, so it has no effect. Verified on macOS arm64 (2.1 GiB file written and read past the 2 GiB offset); Linux x86_64 runs it in the nightly CI job | `large-file-over-2GiB` (`--large`) |
| SQLite version and compile options | via SQL | `sqlite_version()` (3.51.1 ≥ 3.37.0), `pragma_compile_options` (`THREADSAFE=1`) | `version-compile-options` |
| STRICT tables, partial and expression indexes | direct | DDL through `SQLite.exec` | `version-compile-options` |
| No SQL table or user functions | direct | leansqlite registers no function unless `enableSha3` is called, which the build never does; `tm_path` and `rarray` fail to prepare | `tm-path-unavailable`, `no-user-functions` |

## Constraints found

These are not gaps in the need list, but they shape how the store uses leansqlite.

- **Import closure.** The `SQLite` root module and its higher layers (`SQLite.Blob`,
  `SQLite.QueryParam`, `SQLite.QueryResult`, `SQLite.Interpolation`) import Lean compiler
  modules (`Lean.Elab.*`, `Lean.Data.Json.*`). The runtime imports only `SQLite.FFI` and
  `SQLite.LowLevel`, so its import closure stays within Init, Std, leansqlite and Tiramemsu.
- **No explicit close.** leansqlite closes a connection (`sqlite3_close`) when the last
  reference to it and to its statements is dropped. `SqliteStore.close` drops the statement
  cache and every connection reference; the close-during-transaction test checks that the
  file is unlocked and uncommitted writes are gone afterwards.
