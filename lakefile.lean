import Lake
open Lake DSL

/-
lean-tiramemsu: a verified Lean 4 port of tiramemsu.

Pins (see openspec/changes/m0-lean-foundation, task 1.2):
- toolchain: leanprover/lean4:v4.34.0 (= `lean-toolchain` of the pinned Mathlib commit)
- Mathlib:   v4.34.0 tag, commit 5ed2965256430c3649e86755f9576b54eca72435 (proofs and tooling only)
- leansqlite: commit f9cdb9eacb5c8b8ecc02ee9fd9e568d7d28c1416 (toolchain bump to v4.34.0)
-/
package tiramemsu where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5ed2965256430c3649e86755f9576b54eca72435"

require leansqlite from git
  "https://github.com/leanprover/leansqlite.git" @ "f9cdb9eacb5c8b8ecc02ee9fd9e568d7d28c1416"

/-- Runtime library: Lean core, Std and leansqlite only.
Sources live under `src/` because a root-level `Tiramemsu/` directory would collide with the
`tiramemsu` link to the Rust repository on case-insensitive filesystems (macOS). -/
@[default_target]
lean_lib Tiramemsu where
  srcDir := "src"

/-- Proof library: theorems about `Tiramemsu` definitions; the only library that may import Mathlib. -/
@[default_target]
lean_lib TiramemsuProofs where

/-- The `tiramemsu` executable (CLI and oracle driver). -/
@[default_target]
lean_exe tiramemsu where
  root := `Main

/-
Tooling (policy checker, oracle) lives under `tools/`: a root-level `Policy/` or `Oracle/` would
share a directory with the `policy/` and `oracle/` data directories on case-insensitive
filesystems.
-/

/-- Proof-policy checker. Tooling only: never linked into the runtime. -/
lean_lib Policy where
  srcDir := "tools"
  globs := #[.one `Policy.Toml, .one `Policy.Index, .one `Policy.Rules]

lean_exe «policy-check» where
  srcDir := "tools"
  root := `Policy.Main
  supportInterpreter := true

/-- Seeded policy violations, built only by the checker self-test. -/
lean_lib PolicyFixtures where
  srcDir := "tools/Policy/Fixtures"
  globs := #[.submodules `Fixture]

/-- Binding probes, model unit tests and refinement tests. -/
lean_lib Test where
  globs := #[.andSubmodules `Test]

lean_exe «tiramemsu-tests» where
  root := `Test.Main

/-- Differential oracle harness and benchmark. -/
lean_lib Oracle where
  srcDir := "tools"
  globs := #[.one `Oracle.Canon, .one `Oracle.Deviation, .one `Oracle.Driver, .one `Oracle.Scenario,
    .one `Oracle.Fixture, .one `Oracle.Bench, .one `Oracle.Tests, .one `Oracle.Codec, .one `Oracle.Interchange, .one `Oracle.Store, .one `Oracle.Query, .one `Oracle.QueryBench]

lean_exe oracle where
  srcDir := "tools"
  root := `Oracle.Main
