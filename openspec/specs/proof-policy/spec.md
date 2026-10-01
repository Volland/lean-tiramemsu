# proof-policy Specification

## Purpose
Defines the CI-enforced rules that make a proof in this project cover exactly the code that runs, and that make the set of proven requirements explicit and checkable (D7, D12).

## Requirements

### Requirement: No unfinished proofs or user axioms
Neither library SHALL contain a declaration whose proof or value depends on `sorry` or `admit`, and neither library SHALL declare an axiom. The check SHALL inspect the elaborated declarations, not only the source text.

#### Scenario: Sorry in a proof
- **WHEN** any declaration of either library depends on `sorry`, including through a macro or a helper lemma
- **THEN** the policy check fails and names the declaration

#### Scenario: User axiom
- **WHEN** a module of either library declares an `axiom`
- **THEN** the policy check fails and names the axiom

### Requirement: Verified modules are designated and total
The project SHALL keep a committed list of verified modules. A verified module SHALL import only Lean `Init`, `Std` and other verified modules. It SHALL NOT contain `partial`, `unsafe` or `opaque` declarations; any unbounded search SHALL use explicit fuel.

#### Scenario: Partial function in a verified module
- **WHEN** a verified module declares a `partial def`
- **THEN** the policy check fails and names the declaration

#### Scenario: Verified module imports shell code
- **WHEN** a verified module imports the SQLite binding or a non-verified runtime module
- **THEN** the policy check fails and reports the import

#### Scenario: Shell code may be partial
- **WHEN** a non-verified runtime module declares a `partial def`
- **THEN** the policy check does not report it

### Requirement: Implementation overrides need an equality theorem
In verified modules, `implemented_by` and `extern` SHALL be used only when a `@[csimp]` theorem states that the overridden definition equals its replacement.

#### Scenario: Override without csimp
- **WHEN** a verified definition carries `implemented_by` and no `@[csimp]` theorem relates it to the replacement
- **THEN** the policy check fails and names the definition

#### Scenario: Override with csimp
- **WHEN** a verified definition is replaced through a `@[csimp]` theorem
- **THEN** the policy check accepts it

### Requirement: No native_decide
No module of either library SHALL use `native_decide` or `decide` with native evaluation.

#### Scenario: native_decide anywhere
- **WHEN** any module of either library contains `native_decide`
- **THEN** the policy check fails and names the module and line

### Requirement: Axiom set of every theorem
Every theorem of the proof library SHALL depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. A theorem on the `bv_decide` allowlist MAY additionally depend on `Lean.ofReduceBool` and on the axioms that `Lean.ofReduceBool` itself depends on in the pinned toolchain.

#### Scenario: Unexpected axiom
- **WHEN** a theorem not on the allowlist depends on `Lean.ofReduceBool`
- **THEN** the policy check fails and lists the theorem and its axioms

#### Scenario: Standard axioms
- **WHEN** a theorem depends only on `propext`, `Classical.choice` and `Quot.sound`
- **THEN** the policy check accepts it

### Requirement: bv_decide confined to codec proofs
`bv_decide` SHALL appear only in proof modules of the codec, and the `bv_decide` allowlist SHALL name only theorems declared in those modules (D12). The allowlist SHALL be a committed file that changes only by explicit edit.

#### Scenario: bv_decide outside the codec
- **WHEN** a proof module outside the codec proofs uses `bv_decide`
- **THEN** the policy check fails and names the module

#### Scenario: Allowlist entry outside the codec
- **WHEN** the allowlist names a theorem that is not declared in a codec proof module
- **THEN** the policy check fails and names the entry

### Requirement: Theorem index for proven requirements
A requirement SHALL count as proven exactly when it has a scenario whose name begins with `Machine-checked`. A committed theorem index SHALL map every proven requirement of the project specs to one or more theorems of the proof library. The check SHALL fail when a proven requirement has no entry, when an entry names a requirement that does not exist or is not proven, or when a named theorem does not exist or fails the axiom rule. For specs of active changes, the same check SHALL run and report missing entries without failing, and SHALL run in failing mode on a change's own specs before that change is archived.

#### Scenario: Missing theorem
- **WHEN** the index names a theorem that does not exist in the proof library
- **THEN** the policy check fails and reports the requirement and the missing name

#### Scenario: Unindexed proven requirement
- **WHEN** a project spec has a requirement with a `Machine-checked` scenario and the index has no entry for it
- **THEN** the policy check fails and names the requirement

#### Scenario: Pending change
- **WHEN** an active change has a proven requirement whose theorem is not written yet
- **THEN** the check lists it as pending and does not fail, until that change's pre-archive run, which fails

### Requirement: Gates are self-tested and always on
Every rule of this capability SHALL run in CI on every commit on all supported platforms. The checker SHALL have a self-test with at least one seeded violation per rule, each of which it SHALL reject with that rule's identifier.

#### Scenario: Seeded violations
- **WHEN** the checker self-test runs over the seeded fixtures
- **THEN** each fixture is rejected by exactly the rule it violates, and the self-test fails if any fixture is accepted
