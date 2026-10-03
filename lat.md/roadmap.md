# Roadmap

Milestones M0–M6, each one OpenSpec change under `openspec/changes/`. v1 is M0–M3. See [[decisions#D4 Scope And Stages]].

## Milestones

Each milestone depends on the one above it; proofs are written with the code, never after.

| M | Change | Delivers |
|---|---|---|
| M0 | `m0-lean-foundation` | Lake project, two libraries, CI proof gates, leansqlite gap check, Store interface and contract, Rust oracle pin |
| M1 | `m1-verified-codec` | ObjectId with origin bits, literal canonicalization, term dictionary, byte-identical schema and triggers |
| M2 | `m2-verified-store` | Memory verbs, transactions, cascade, temporal views, speculation, volatile state, predicate schema, concurrency, merge laws |
| M3a | `m3a-ir-evaluator-paths` | IR and its denotation, nested-loop joins, path engine, provenance, bundles, Lean API and CLI |
| M3b | `m3b-leapfrog-triejoin` | Leapfrog Triejoin and the join planner |
| M4 | `m4-sparql-frontend` | SPARQL 1.1 query and update, RDF 1.2 annotations, temporal datasets |
| M5 | `m5-cypher-frontend` | openCypher read and write, dual view, temporal clauses |
| M6 | `m6-bindings-c-abi` | C ABI shim, JSON bridge, Node.js and Python packages, performance gate |

## Performance Gate

Benchmarks run against Rust on the same harness from M0 and are report-only until M6. See [[decisions#D14 Performance Gate At Bindings]].

Before the Node.js and Python packages switch to the Lean backend, at 10⁶ statements:

- writes (assert, supersede): at most 2× Rust;
- point and 2-hop lookups under now, asOf and validAt: at most 2× Rust;
- acyclic multi-pattern BGPs: at most 3× Rust;
- cyclic and skewed patterns (triangles, layered): faster than Rust;
- paths: at most 2× Rust;
- as-of throughput at least 70 % of the no-history baseline;
- bytes per statement: identical, by construction.

### Benchmark Harness

`oracle bench --n N` builds the fixture through the Rust driver, times each gate category on both builds, checks the results are equal, and writes `oracle/bench/report-N.json` and `.md`.

The fixture has the shape of the Rust `bench/engine-comparison` (about 11·N statements). Timings are taken inside each driver. The exit status reflects harness errors and result mismatches only; Lean columns read "n/a" until the milestone that implements the workload.

## Status

M0 (`m0-lean-foundation`) is implemented: the Lake project and pins, the policy checker, the store interface with its proven model, the SQLite store with refinement tests, and the differential oracle with its benchmark harness.

M1 (`m1-verified-codec`) is implemented: the proven codec, the term dictionary model and its SQLite refinement, storage format 1 and file interchange with Rust ([[codec]]). The codec benchmark is report-only; double printing is far slower than Rust and will need a faster algorithm under `@[csimp]` before the M6 gate.

M2 (`m2-verified-store`) is implemented: the store engine ([[engine]]) with its Tier 1 theorems ([[verification#Proven Store State Machine]]), the shell with the writer, reader pool and clocks, and the differential store oracle. The write benchmarks are report-only.

M3a (`m3a-ir-evaluator-paths`) is implemented except three Tier 2 proofs: the IR and its reference semantics, the index nested-loop evaluator (proven equal to the reference), the path engine (searches proven against the walk specification), provenance (erasure proven), bundles, the Lean API and the CLI. Open: provenance soundness and sufficiency (task 10.3) and the bundle round trip and re-import (11.3, 11.4), so the change is not ready to archive; see [[verification#Proven Query Semantics]].

