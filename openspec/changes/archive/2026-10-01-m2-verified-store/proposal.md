## Why

Tiramemsu's distinctive claims (never forget, idempotent assert, supersede replay that keeps every layer, cascade over layers, exact bitemporal time travel, side-effect-free speculation) are today only tested in Rust. M2 builds the store state machine in Lean once, generic over the M0 `Store` interface, and proves these claims as Tier 1 theorems over `ModelStore` (D2), while the same code runs on `SqliteStore` against the Rust file format (D3, D6). It is the first milestone that writes statements, so M3 (queries) cannot start before it.

## What Changes

- Add the write engine in `Tiramemsu`: transactions with gap-free `t` and monotone instants, the memory verbs (assert, create, retract, retract-matching, supersede, confirm, upsert, metadata, new node, new blank node), the retraction cascade, the predicate schema, named-graph membership verbs, and the volatile table, all written once against the M0 `Store` interface and the M1 codec.
- Add the read side needed by the engine and by tests: view selectors (now, asOf by `t` or instant, history, validAt) and the view reads triple lookup, value resolution, dependents, event log, graph members.
- Add speculation (`speculate`, `dryRun`) as a discarded pure state on the model and a savepoint on SQLite, with burned id counters.
- Add the shell `Db`: one mutex-guarded writer, a reader pool, Views pinned to one WAL snapshot (D10), an injectable clock.
- Add the 2P-set merge function on the model and its laws (D15). Merge is not a user operation.
- Add Tier 1 proofs in `TiramemsuProofs` (D2, D7): never-forget invariant preserved by every verb, idempotent assert, supersede replay, cascade = reflexive-transitive dependents closure, asOf = log replay, half-open validAt, monotone instants for any clock, speculation purity, merge laws. Every proven requirement gets a theorem-index entry (verification policy).
- Add refinement tests (`ModelStore` vs `SqliteStore`), differential tests against the pinned Rust oracle (D6), and N-readers-plus-1-writer concurrency tests checked against the model.
- Listed deviations from Rust (D6): transaction bodies and speculative callbacks are IO-free `TxM` programs, so re-entrant writes cannot be expressed rather than failing at runtime; a View holds one snapshot for its whole scope instead of one per read; instants are unbounded integers in the core and out-of-range values are rejected at the SQLite boundary instead of overflowing. Everything else (eids, report order, kinds, error kinds, file contents) is Rust-compatible.

## Capabilities

### New Capabilities

- `statement-lifecycle`: a statement is born live, is retracted at most once with a kind (explicit, cascade, supersede, cardinality), is never deleted or changed, and its eid is never reused. Proven as an invariant that every operation preserves.
- `transaction-log`: gap-free `t` from 1; `instant = max(clock, prev + 1)`, proven strictly increasing for any clock; a tx row for every committed transaction, including all-no-op ones; tx metadata as triples; atomic failure; transaction options and report; injectable clock.
- `memory-verbs`: assert (idempotent, New/Existing, Confirm policy), create (parallel edges), retract, retract-matching, supersede with layer replay and Patch rules, confirm, new node, the write pipeline checks. Proven: idempotence, and supersede replays exactly the live layers and retracts the old ones at `t`.
- `retraction-cascade`: retracting `e` retracts exactly the live dependents closure over subject and object references, proven equal to the reflexive-transitive closure; cycle termination; per-root `max_cascade`; `dependents` on any view.
- `temporal-views`: now, asOf(`t`), asOf(instant), history, validAt(`d`), combinable; triple lookup; event log. Proven: asOf `t` equals the now view of the log prefix up to `t`; validAt is half-open.
- `speculative-transactions`: `speculate` and `dryRun`, proven observationally pure on the model; burned ids are never reissued; no tx row.
- `volatile-state`: the volatile side table: transactional upserts, not statements, visible only under now.
- `predicate-schema`: `sys:cardinality sys:one` replacement, `sys:unique` with upsert, `sys:valueType`, `sys:subjectType`, `sys:isEdge`, schema-change conflicts.
- `named-graph-membership`: a graph is a node and membership is the layer statement `(e sys:inGraph g)`, at storage and verb level only (query-side `GRAPH` is M3/M4).
- `connection-concurrency`: one mutex-guarded writer, a reader pool, each View pinned to a WAL snapshot that is a committed prefix (D10).
- `merge-laws`: statements as a 2P-set; merge = union of statements with the earliest retraction; proven commutative, associative, idempotent and never-forget preserving (D15). Model function and theorems only.

### Modified Capabilities

None. There are no archived specs yet.

## Impact

- New Lean modules under `Tiramemsu/Engine/`, `Tiramemsu/View/`, `Tiramemsu/Model/Merge.lean`, `Tiramemsu/Shell/` and proofs under `TiramemsuProofs/Store/`. Runtime stays Lean core + Std; proofs may use Mathlib (D7).
- Depends on M0 (`Store` interface and contract, `ModelStore`, `SqliteStore`, CI proof gates, Rust oracle pin) and M1 (ObjectId with origin bits, term dictionary, schema and triggers).
- Uses `leansqlite` (D8) for savepoints, `BEGIN IMMEDIATE`, WAL read transactions; no new dependency.
- Extends the theorem index and the CI axiom check with the Tier 1 theorems; adds refinement, differential and concurrency test suites; adds report-only write benchmarks (D14).
- Unblocks M3a (the evaluator reads through the same views and `Store` scans).
