## Purpose

Defines the release gate that keeps the Node.js and Python packages on Rust until the Lean build is fast enough: fixed ratios against the pinned Rust build at 10⁶ statements, one measurement method, and results published with every release.

## ADDED Requirements

### Requirement: Release is blocked unless the gate passes

Publishing a Lean-backed Node.js or Python package SHALL require a passing gate run for the exact commit being released. The gate SHALL pass only if every threshold of this capability is met, and SHALL fail if any workload is missing, errors, or returns results that differ from the Rust build. There SHALL be no override; a threshold SHALL change only through an OpenSpec change.

#### Scenario: One threshold missed
- **WHEN** every workload meets its threshold except one acyclic BGP at 3.4× Rust
- **THEN** the gate fails, names that workload, and neither package is published

#### Scenario: Missing workload
- **WHEN** the path workloads did not run
- **THEN** the gate fails

### Requirement: Measurement method

The gate SHALL run the shared benchmark harness with the Lean build and the pinned Rust build on the same dedicated machine in the same job, on Linux x86_64. Read workloads SHALL use one database file of 10⁶ statements generated with a fixed seed and opened by both builds; write workloads SHALL start from an empty file on each build. Every workload SHALL run at least 2 warm-up and 10 measured repetitions, and its ratio SHALL be the median Lean time divided by the median Rust time. Both builds SHALL return the same results on every read workload.

#### Scenario: Same data for both builds
- **WHEN** the gate runs the read workloads
- **THEN** both builds read the same file, and the gate records its size and hash

### Requirement: Latency and throughput thresholds

At 10⁶ statements the gate SHALL require: writes (assert and supersede, singly and in batches) at most 2× Rust; point and 2-hop lookups under the now, asOf and validAt views at most 2× Rust; acyclic multi-pattern BGPs at most 3× Rust; cyclic and skewed patterns (triangles on hub-and-spoke and layered graphs) faster than Rust, ratio below 1; path queries (shortest, trail, reachability, all-shortest) at most 2× Rust; and a point lookup through each package's public API at most 2× the Rust-backed package.

#### Scenario: Cyclic pattern must win
- **WHEN** the layered-triangle workload measures a ratio of 1.0
- **THEN** the gate fails

#### Scenario: Binding overhead
- **WHEN** a `triples` point lookup through the Lean-backed Python package takes 2.5× the Rust-backed package
- **THEN** the gate fails

### Requirement: History costs at most 30 percent

On the churn workload the gate SHALL require the Lean build's as-of query throughput to be at least 70% of its own throughput on the same queries over a store without history.

#### Scenario: As-of throughput
- **WHEN** as-of throughput is 65% of the no-history baseline
- **THEN** the gate fails

### Requirement: Storage footprint identical

For the same sequence of operations, the Lean build's database SHALL have the same number of pages and the same bytes per statement as the Rust build's, measured after a full WAL checkpoint.

#### Scenario: Equal footprint
- **WHEN** both builds load the 10⁶-statement workload and checkpoint
- **THEN** their bytes per statement are equal

### Requirement: Results published per release

Every gate run SHALL produce a machine-readable result and a human-readable table with, per workload, the Lean and Rust medians, the interquartile ranges, the ratio, the threshold and the verdict, together with the machine, both build revisions and the dataset hash. Every release SHALL publish these results with the release notes and keep them in the repository under the release version. The same harness SHALL also run on macOS arm64, with its results published as report-only.

#### Scenario: Release carries its numbers
- **WHEN** a version is released
- **THEN** its gate table is attached to the release and stored in the repository under that version
