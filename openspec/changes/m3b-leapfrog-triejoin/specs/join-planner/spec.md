## Purpose

Chooses, for every join region of a query, between Leapfrog Triejoin and index nested-loop join, and fixes pattern order, variable order and index access from cached cardinality estimates. Any plan it can produce returns the reference results, so its heuristics affect speed only.

## ADDED Requirements

### Requirement: Plans cannot change results
Before a join plan runs, the engine SHALL check its validity. For INLJ, the pattern order is a permutation of the region's patterns. For LFTJ, the variable order lists each region variable exactly once and every pattern's index access fits that order. A plan that fails the check SHALL be replaced by the canonical plan (INLJ in text order) and SHALL be reported in explain as a planner fallback. Any valid plan SHALL return a result bag-equal to the reference denotation. Planner options, cached counts and their staleness SHALL therefore affect only speed.

#### Scenario: Same results under every routing option
- **WHEN** the property-test queries run with the LFTJ option set to `never`, `auto` and `always`
- **THEN** all three runs return bag-equal results

#### Scenario: Invalid plan falls back
- **WHEN** a test hook makes the planner emit a variable order that omits a region variable
- **THEN** the query returns the reference result through the canonical plan and explain shows a planner fallback

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** "every plan accepted by the validity check evaluates to a result bag-equal to the reference denotation" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Join regions
For each IR join, the planner SHALL form one region from its stored triple patterns: patterns whose predicate is a constant stored predicate or a variable. Virtual-predicate patterns, path patterns, inline values and nested operators SHALL be joined with the region's result by INLJ, in planner order.

#### Scenario: Virtual predicate outside the region
- **WHEN** a query joins a triangle of `:k` patterns with `?r tm:addedAt ?when`, where `?r` is the eid of one triangle pattern
- **THEN** explain shows the three `:k` patterns as an LFTJ region and the `tm:addedAt` pattern as a nested-loop step after it

### Requirement: Routing by cyclicity
The planner SHALL classify a region as cyclic exactly when GYO reduction does not eliminate the hypergraph whose hyperedges are the patterns' variable sets (eid variables included, constants ignored). With the LFTJ option `auto` (the default), it SHALL route a cyclic region to LFTJ and an acyclic one to INLJ. It SHALL route a cyclic region to INLJ when every pattern's estimate is at or below the small-input threshold. The option `always` SHALL route every region to LFTJ, and `never` SHALL route every region to INLJ.

#### Scenario: Triangle and four-cycle are cyclic
- **WHEN** the planner classifies `?a :k ?b . ?b :k ?c . ?c :k ?a` and a four-pattern cycle
- **THEN** both are cyclic and, on fixtures above the threshold, are routed to LFTJ

#### Scenario: Chains, stars and shared pairs are acyclic
- **WHEN** the planner classifies a three-pattern chain, a three-pattern star, and two patterns sharing the same two variables
- **THEN** all three are acyclic and routed to INLJ under `auto`

#### Scenario: Tiny cyclic region stays nested
- **WHEN** every pattern of a cyclic region has an estimate at or below the small-input threshold
- **THEN** the region is routed to INLJ under `auto`

### Requirement: Cardinality estimates from cached per-predicate counts
The planner SHALL estimate each pattern from cached per-predicate row counts for the pattern's index family, combined with a bounded probe of the pattern's constant prefix, capped at a fixed number of rows. Counts SHALL be refreshed after every commit made through the same database handle. A cache that may miss commits by other processes SHALL be discarded when a reader observes a newer committed transaction than the cache reflects. Deviation from Rust (D6): the planner reads neither `sqlite_stat1` nor `sqlite_stat4`, and runs no `ANALYZE` to plan joins.

#### Scenario: Rare predicate first after a load
- **WHEN** a skewed store holds 500 000 `:knows` rows and 50 `:rare` rows, and an acyclic BGP joins them on a shared variable
- **THEN** the chosen INLJ order starts from the `:rare` pattern

#### Scenario: Refresh after commit
- **WHEN** a transaction commits 10 000 new `:rare` rows and the same query is planned again on the same handle
- **THEN** the plan reflects the new counts without reopening the database

#### Scenario: Stale counts are harmless
- **WHEN** a test forces the cache to hold counts from before a large commit
- **THEN** the query result is unchanged and only the plan may differ

### Requirement: Deterministic plans
The plan for a region SHALL be a function of the IR, the snapshot of cached counts and probe results, and the planner options only. Ties SHALL be broken by the patterns' and variables' first position in the query text. Re-planning the same query on the same data SHALL produce the same plan.

#### Scenario: Golden plans
- **WHEN** the golden-plan suite plans its fixed queries against fixed count snapshots
- **THEN** routing, INLJ pattern order, LFTJ variable order and per-pattern index access match the recorded plans byte for byte

#### Scenario: Repeated planning
- **WHEN** one query is planned 100 times on an unchanged store
- **THEN** all 100 plans are identical

### Requirement: Explain shows the chosen join plan
Explain SHALL show, for every join region: the algorithm (LFTJ or INLJ), the routing reason (cyclic, acyclic, small input, forced by option, or planner fallback), the pattern order or variable order, each pattern's view, index family and order (or in-memory sorted copy), and its estimate. Deviation from Rust (D6): explain describes the Lean join plan instead of SQLite's `EXPLAIN QUERY PLAN`.

#### Scenario: Explain a triangle
- **WHEN** explain runs on the triangle query over the hub-and-spoke fixture
- **THEN** it shows an LFTJ region with reason cyclic, the chosen variable order, and for each pattern its index order in the `live_*` family and its estimate

### Requirement: Triangle and plan-quality benchmarks
The benchmark harness SHALL include the triangle fixtures ported from the Rust build: uniform out-degree 5, 300 hubs × 1 500 spokes in both directions plus noise, and three layers of 150, 300 and 600 nodes with three closing edges each. It SHALL also include a skewed plan-quality fixture with one huge class, one rare predicate and churned properties. Fixtures SHALL be generated deterministically and loaded into one database file that both builds read. The harness SHALL report Lean and Rust times and their ratio. The Lean build SHALL be faster than Rust on the hub-and-spoke and layered fixtures; until M6 this target is reported and does not fail the build (D14). The small-input threshold and the read-ahead buffer limit SHALL be set from these measurements, with the evidence recorded.

#### Scenario: Report against Rust
- **WHEN** the triangle benchmark runs
- **THEN** it reports, per fixture, edge count, triangle count (equal on both builds), Lean time, Rust time and ratio, and flags any skewed fixture where Lean is not faster without failing the build

#### Scenario: Plan quality report
- **WHEN** the plan-quality benchmark runs with fresh and with deliberately stale counts
- **THEN** it reports the time of each plan and the chosen orders, with results equal in both runs
