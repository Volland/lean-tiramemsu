## Purpose

Defines the `tiramemsu` Python package on the Lean backend: the same typed, synchronous API as the Rust-backed package, reaching the shared library through ctypes, shipped as platform wheels that carry the library.

## ADDED Requirements

### Requirement: Public API and typing unchanged

The package SHALL keep the PyPI name `tiramemsu`, Python 3.9 and later, the `py.typed` marker, and the public API of the pinned Rust-backed package: `Database`, `View`, `Tx`, `Ref`, the term dataclasses, result types, `TiramemsuError` and `__version__`, with the same names, signatures, types and behaviour. Every wrapper module other than the native module SHALL be byte-identical to the pinned Rust commit, and the package SHALL pass `mypy --strict`.

#### Scenario: Public names unchanged
- **WHEN** the public names and signatures of `tiramemsu` are listed and compared with the pinned Rust-backed package
- **THEN** the lists are identical

#### Scenario: Strict types
- **WHEN** `mypy --strict` runs on the package
- **THEN** it reports no errors

### Requirement: Native layer over the shared library

The native module `tiramemsu._native` SHALL reach the database only through the C ABI, called through ctypes, and SHALL provide the class `Native` with a constructor taking a path and an optional options string and `call(op, args)` returning the result JSON text. A failure SHALL raise `RuntimeError` whose message is `tiramemsu:` followed by the error JSON text, so the wrapper raises `TiramemsuError` with its `code`. The interpreter lock SHALL be released for the duration of every library call. Every string returned by the library SHALL be freed after it is copied, a `Native` that is garbage-collected SHALL have its handle closed, and the module SHALL check on import that the library's ABI version is 1.

#### Scenario: Unknown option
- **WHEN** `Native(path, '{"bogusOption": 1}')` is constructed
- **THEN** it raises `RuntimeError` whose message starts with `tiramemsu:` and whose JSON has `code` `InvalidArgument`

#### Scenario: Threads query in parallel
- **WHEN** eight Python threads query one `Database` at the same time
- **THEN** every query returns the correct rows and the queries overlap in time

### Requirement: Wheels per platform

Releases SHALL publish one wheel for each of macOS arm64, macOS x86_64, manylinux x86_64, manylinux aarch64 and Windows x86_64, each carrying the platform's shared library and tagged `py3-none-<platform>`, because the library does not depend on the Python ABI. Installing a wheel SHALL compile nothing. No source distribution SHALL be published, and the package SHALL fail on import with a message naming the platform when no library is present.

#### Scenario: Wheel checks
- **WHEN** each Linux wheel is checked with `auditwheel` and each macOS wheel with `delocate`
- **THEN** the checks pass with the declared platform tags and no external library is required

#### Scenario: Smoke install
- **WHEN** a wheel is installed in a fresh virtual environment on its platform and `import tiramemsu` runs a query
- **THEN** the query returns rows and `tiramemsu.__version__` is the package version

### Requirement: Rust test suite passes unchanged

The test suite of the pinned Rust package (`tests/`) SHALL pass, unmodified, against the Lean-backed package on every supported platform, in continuous integration on every change.

#### Scenario: Suite on the Lean backend
- **WHEN** `pytest` runs on any supported platform
- **THEN** every test of the pinned Rust suite passes

### Requirement: PyPI release

A release workflow SHALL build the five wheels, smoke-test a wheel on Linux, macOS arm64 and Windows, and publish to PyPI through trusted publishing with no stored token, on a `v*` tag or on a manual run only when publishing is requested. Publishing SHALL depend on a passing performance gate and on the conformance and ABI jobs. The first Lean-backed release SHALL take the next minor version after the last Rust-backed release.

#### Scenario: Gate fails
- **WHEN** the performance gate fails for a tagged release
- **THEN** the PyPI publish job does not run

#### Scenario: Rehearsal
- **WHEN** the workflow is run by hand without publishing
- **THEN** every wheel is uploaded as a workflow artifact and nothing is published
