# build-toolchain Specification

## Purpose
Defines how lean-tiramemsu is built: one Lake project with a pinned toolchain and dependencies, a runtime library and a proof library kept apart, and a natively compiled executable, so that every later milestone builds and proves against the same fixed inputs.

## Requirements

### Requirement: Pinned toolchain and dependencies
The project SHALL pin the Lean toolchain to one exact release and SHALL pin every Lake dependency (Mathlib, leansqlite and their transitive dependencies) to an exact commit in the committed manifest. The pinned toolchain SHALL be the toolchain declared by the pinned Mathlib commit. A toolchain or dependency change SHALL update the toolchain file and the manifest in the same commit and SHALL pass every CI gate before it lands.

#### Scenario: Pins are consistent
- **WHEN** CI compares the project's toolchain file with the toolchain file of the pinned Mathlib commit
- **THEN** they name the same release, and the check fails the build if they differ

#### Scenario: Floating dependency rejected
- **WHEN** a dependency is declared without an exact commit in the manifest
- **THEN** CI fails and names the dependency

#### Scenario: Deliberate bump
- **WHEN** a commit changes the toolchain release
- **THEN** the same commit updates the manifest, and the full build, proof gates and tests run on it before merge

### Requirement: Two libraries and one executable
The project SHALL define a runtime library `Tiramemsu`, a proof library `TiramemsuProofs` and an executable `tiramemsu`. The default build SHALL build all three, so that a build that compiles the code also checks the proofs. Test, policy-checking and oracle executables SHALL be separate targets that the runtime library and the `tiramemsu` executable do not depend on.

#### Scenario: Fresh clone builds everything
- **WHEN** the default build runs on a fresh clone of the repository on a supported platform
- **THEN** the runtime library, the proof library and the `tiramemsu` executable are all built without error

#### Scenario: Broken proof fails the default build
- **WHEN** a theorem in the proof library no longer checks
- **THEN** the default build fails

### Requirement: Runtime import closure excludes Mathlib
Every module reachable by imports from the runtime library or the `tiramemsu` executable SHALL belong to Lean's `Init` or `Std`, to leansqlite, to the runtime library itself, or to an explicitly allowlisted toolchain module. Mathlib and its dependencies SHALL be importable only from the proof library and from non-shipped tooling targets (D7).

#### Scenario: Mathlib import in runtime code
- **WHEN** a runtime module imports any Mathlib module, directly or transitively
- **THEN** CI fails and reports the import chain

#### Scenario: Unlisted toolchain module
- **WHEN** a runtime module imports a module of the Lean compiler package that is not on the allowlist
- **THEN** CI fails and names the module

### Requirement: Native executable with the Lean runtime linked
The `tiramemsu` executable SHALL be produced by Lean's C backend and the platform C compiler, with the Lean runtime and the bundled SQLite linked statically (D1). It SHALL run on a machine without a Lean toolchain. It SHALL report its own version, the SQLite library version it links, and the highest storage format version it supports.

#### Scenario: Runs without a toolchain
- **WHEN** the built executable is copied to a directory and run with no Lean toolchain on the search path
- **THEN** its version command succeeds

#### Scenario: No dynamic Lean library
- **WHEN** the executable's dynamic library dependencies are listed
- **THEN** no Lean shared library appears, only system libraries

#### Scenario: Version report
- **WHEN** the version command runs
- **THEN** it prints the program version, the linked SQLite version and the supported format version `1`

### Requirement: Generated C is not source
Generated C SHALL remain a build artifact that is never committed, edited or reviewed. The repository SHALL contain no C, C++ or header source outside the directory reserved for the C ABI shim (D9).

#### Scenario: Stray C file
- **WHEN** a commit adds a `.c` or `.h` file outside the shim directory and outside build output
- **THEN** CI fails and names the file

### Requirement: Supported platforms
The project SHALL build and pass all gates and tests on 64-bit macOS on arm64 and 64-bit Linux on x86_64. 32-bit platforms SHALL NOT be supported.

#### Scenario: CI matrix
- **WHEN** CI runs for a commit
- **THEN** the build, proof gates and tests run on both supported platforms and the commit is accepted only if both pass
