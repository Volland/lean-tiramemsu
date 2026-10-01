## Purpose

Defines `@tiramemsu/node` on the Lean backend: the same typed, synchronous TypeScript API as the Rust-backed package, reaching the shared library through koffi, shipped with prebuilt libraries so that installing it compiles nothing.

## ADDED Requirements

### Requirement: Public API and types unchanged

The package SHALL keep the npm name `@tiramemsu/node`, `type: module`, and the public API and types of the pinned Rust-backed package: `Database`, `View`, `Tx`, `Ref`, the term helpers, `TiramemsuError` and every exported type, with the same names, signatures and behaviour. Every wrapper source file other than the native loader SHALL be byte-identical to the pinned Rust commit. The package SHALL type-check under `tsc --strict`.

#### Scenario: Declaration diff is empty
- **WHEN** the generated `dist/index.d.ts` is compared with the one built from the pinned Rust package
- **THEN** the exported declarations are identical

#### Scenario: Wrapper files unchanged
- **WHEN** the wrapper and test files are hashed and compared with the pinned Rust commit
- **THEN** only the native loader differs

### Requirement: Native layer over the shared library

The package SHALL reach the database only through the C ABI, called synchronously through koffi. It SHALL provide the native class the wrapper expects: a constructor taking a path and an optional options string, and `call(op, args)` returning the result JSON text. A failure SHALL throw an `Error` whose message is `tiramemsu:` followed by the error JSON text, so the wrapper raises `TiramemsuError` with its `code`. Every string returned by the library SHALL be freed after it is copied, and a database object that is garbage-collected SHALL have its handle closed. On load the package SHALL check that the library's ABI version is 1 and fail with a message naming both versions otherwise.

#### Scenario: Error code reaches JavaScript
- **WHEN** `db.now().sparql("SELECT ?")` is called
- **THEN** it throws a `TiramemsuError` with `code` `Parse`

#### Scenario: Collected database is closed
- **WHEN** a thousand databases are opened, dropped and garbage-collected in one process
- **THEN** the process holds no more open database files than before

#### Scenario: Library from another ABI
- **WHEN** the package loads a library whose `tm_version` reports `abi` 2
- **THEN** the import fails with a message naming ABI 2 and the expected ABI 1

### Requirement: Prebuilt libraries, no compile at install

The published package SHALL carry one shared library for each of darwin-arm64, darwin-x64, linux-x64 (glibc), linux-arm64 (glibc) and win32-x64, and SHALL select the one for `process.platform` and `process.arch` at load. Installing the package SHALL run no compiler and no install script of its own. On a platform with no library the import SHALL fail with a message naming the platform and architecture. The package SHALL support the Node.js versions of the pinned Rust package (18 and later).

#### Scenario: Install without scripts
- **WHEN** the packed tarball is installed with `npm install --ignore-scripts` on each supported platform and `import { Database } from "@tiramemsu/node"` runs
- **THEN** the import succeeds and a query returns rows

#### Scenario: Package carries every platform
- **WHEN** the package is packed for release
- **THEN** the tarball holds `dist/` and one shared library for each of the five platforms

#### Scenario: Unsupported platform
- **WHEN** the package is loaded on a platform with no library
- **THEN** the import fails with a message naming the platform and architecture

### Requirement: Rust test suite passes unchanged

The test suite of the pinned Rust package (`test/`) SHALL pass, unmodified, against the Lean-backed package on every supported platform, in continuous integration on every change.

#### Scenario: Suite on the Lean backend
- **WHEN** `npm test` runs on any supported platform
- **THEN** every test of the pinned Rust suite passes

### Requirement: npm release

A release workflow SHALL build the five libraries, assemble and pack the package, install and smoke-test it on each platform it can run on, and publish `@tiramemsu/node` with provenance on a `v*` tag, or on a manual run only when publishing is requested. Publishing SHALL depend on a passing performance gate and on the conformance and ABI jobs. The first Lean-backed release SHALL take the next minor version after the last Rust-backed release.

#### Scenario: Gate fails
- **WHEN** the performance gate fails for a tagged release
- **THEN** the npm publish job does not run

#### Scenario: Rehearsal
- **WHEN** the workflow is run by hand without publishing
- **THEN** the packed tarball is uploaded as a workflow artifact and nothing is published
