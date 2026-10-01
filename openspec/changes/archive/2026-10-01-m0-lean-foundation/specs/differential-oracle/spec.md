## Purpose

Defines how everything that is tested rather than proven is compared with the Rust reference: one pinned Rust build, a driver protocol both builds speak, canonical comparison over shared database files, an explicit deviation registry, and a report-only benchmark harness (D6, D14).

## ADDED Requirements

### Requirement: Rust build pinned after reserve-replica-id
The repository SHALL record exactly one Rust commit as the oracle. The recorded commit SHALL contain the Rust `reserve-replica-id` change as landed and archived (origin bits reserved, D15), and the recording SHALL name the evidence for this. Changing the pin SHALL be a deliberate commit that reruns every oracle comparison.

#### Scenario: Pin verified
- **WHEN** the pin check runs
- **THEN** it confirms that the recorded commit exists in the Rust repository and that its tree contains the archived `reserve-replica-id` change and no active one, and fails otherwise

#### Scenario: Pin before the prerequisite
- **WHEN** someone records a commit that predates the landing of `reserve-replica-id`
- **THEN** the pin check fails

### Requirement: Oracle built without touching the Rust repository
The oracle build SHALL be reproducible from the pinned commit alone and SHALL only read the Rust repository; it SHALL NOT change its working tree, index, branches or worktree list. The Rust driver used by the harness SHALL be part of this repository.

#### Scenario: Read-only build
- **WHEN** the oracle is built from a clean state
- **THEN** the Rust repository's status, branches and worktree list are the same before and after

### Requirement: Shared driver protocol
Both builds SHALL expose a driver that reads one JSON request per line and writes one JSON response per line, with the operations of the Rust JSON bridge plus open, close and raw-dump. A response SHALL be either a result or an error carrying an error code. An operation that a build does not implement yet SHALL return an unsupported error, never a wrong result. Raw dump SHALL emit every row of the `meta`, `term`, `tx`, `triple`, `volatile` and `pred_multi` tables in primary-key order.

#### Scenario: Unsupported operation
- **WHEN** the Lean driver receives an operation that a later milestone owns
- **THEN** it responds with an unsupported error

#### Scenario: Raw dump of a Rust file
- **WHEN** the Rust driver writes a set of transactions into a file and both drivers raw-dump that file
- **THEN** the two dumps are equal after canonicalization

### Requirement: Canonical comparison
Results SHALL be compared in a canonical form: object keys sorted; integers compared exactly at full 64-bit precision; unordered result sets compared as multisets; ordered results compared in order; doubles compared by their lexical form; errors compared by error code only, not by message.

#### Scenario: Large integer
- **WHEN** both builds return the integer 2⁶³ − 1
- **THEN** the comparison treats them as equal and treats 2⁶³ − 2 as different

#### Scenario: Unordered rows
- **WHEN** a query without ordering returns the same rows in different orders on the two builds
- **THEN** the comparison treats the results as equal

### Requirement: Scenarios over shared database files
A comparison scenario SHALL be a sequence of steps, each run by a named build, on one database file handed between the builds after each close. A step marked for comparison SHALL be run by both builds on copies of the same file, and its canonical results SHALL be compared. A mismatch SHALL be reported with the scenario, the step, the seed if any, and both canonical results, so that it can be rerun.

#### Scenario: Handoff
- **WHEN** a scenario has the Rust build write, the Lean build read and the Rust build read again
- **THEN** each build opens the file the previous step left, and every compared step either matches or reports the step and both results

### Requirement: Deviations are listed
Every accepted difference between the builds SHALL be an entry in a committed deviation registry with an identifier, a summary, the spec that states it and a matcher. A mismatch SHALL pass only if a registry entry matches it; any other mismatch SHALL fail. The registry SHALL contain, from this change on, the unavailability of `tm_path` and the SQL user functions on Lean connections.

#### Scenario: Unlisted difference
- **WHEN** a compared step differs and no registry entry matches the difference
- **THEN** the comparison fails

#### Scenario: Listed difference
- **WHEN** a compared step differs in a way that a registry entry's matcher covers
- **THEN** the comparison passes and reports the step as an accepted deviation with the entry's identifier

#### Scenario: Initial registry
- **WHEN** the registry is read at the end of this change
- **THEN** it contains entries for `tm_path` as a SQL table function and for the SQL user functions, each referencing the spec that states the deviation

### Requirement: Report-only benchmark harness
A benchmark harness SHALL build a deterministic fixture of a given size through the Rust build, time the same workloads on each build that supports them, grouped by the categories of the performance gate, check that both builds return equal results for every timed workload, and write a machine-readable report and a readable table with per-workload ratios against Rust and bytes per statement. Until the bindings milestone, the harness SHALL NOT fail on any ratio; it SHALL fail only on a harness error or a result mismatch (D14).

#### Scenario: Slow Lean build
- **WHEN** a workload runs ten times slower on the Lean build than on the Rust build
- **THEN** the report shows the ratio and the harness exits successfully

#### Scenario: Different results under benchmark
- **WHEN** a timed workload returns different results on the two builds
- **THEN** the harness fails and reports the workload

#### Scenario: Workload not yet supported
- **WHEN** the Lean build does not implement a workload's operations yet
- **THEN** the report lists the workload with Rust timings only and marks the Lean column as not available
