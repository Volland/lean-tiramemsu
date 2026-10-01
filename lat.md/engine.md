# Engine

The M2 store state machine: memory verbs, transactions, views and cascade, written once over the Store interface and proven on the model. See [[architecture#Store Abstraction]].

## Types

Retraction kinds, valid intervals, patches, assert results and options, transaction options and reports, events, and the engine error with Rust's variant names.

## Store Operations

The engine's store primitives as two free monads: `RProg` over reads, run on a snapshot reader, the writer or a model state, and `Op`, which adds the guarded writes a transaction body may perform.

## Reserved Namespaces

Engine IRIs (`sys:`, `tm:`, `rdf:`), the schema flags, and the rule that rejects user writes to reserved namespaces and tag IRIs, as in Rust.

## Intervals

Valid-time intervals: the emptiness check, the overlap test used by assert and cardinality one, and half-open membership of an instant with absent bounds unbounded.

## Transaction Bodies

A body is an IO-free `TxProg`, a free monad over `Verb`; the engine runs it in `EngM`, the transaction context over `SProg` body programs, so a nested write cannot be expressed.

## Cascade Walk

One breadth-first walk serves the retraction cascade (live statements, with the `max_cascade` limit) and the dependents read (statements visible in a view, no limit); its fuel is `next_stmt` plus one.

## Write Pipeline

Every written statement passes, in Rust's order: positions, reserved namespaces (user writes), interval, flag validation or value and subject type, idempotency (assert), uniqueness, cardinality one, allocation, self-reference, insert.

## Predicate Schema

The flags of a predicate are its live `sys:` flag statements, read at the current point of the transaction; value type, subject type, flag values and schema-change conflicts are checked as in Rust.

## Memory Verbs

Assert (idempotent, with `Return` or `Confirm`), create, metadata, confirm, upsert, retract, retract-matching, new node, new blank node and the volatile side table, each a program over the store operations.

## Supersede

Supersede retracts the cascade set of the root with kind `supersede` and replays it under fresh eids `σ` allocated in cascade order, skipping memberships, then links the new root with `sys:supersedes`.

## Named Graphs

A graph is an `IRI`, `NODE` or `BNODE`; membership is the engine-written statement `(e sys:inGraph g)`, added idempotently, removed by retraction, and never copied by supersede.

## Views

A view is a transaction-time selector (now, as-of a transaction or an instant, history) and a valid-time selector; lookups, values, dependents, the event log and graph reads are read programs.

## Transactions

The cores are generic over the store: a commit takes `t = last_t + 1` and `instant = max(now, last_instant + 1)`; a dry run or speculation runs in the savepoint `spec`, rolls back and burns advanced id counters.

## Model Instance

`Model.transact`, `Model.dryRun` and `Model.speculate` are the generic cores at the model store with the clock reading as an argument; the Tier 1 theorems are stated over them.

## Shell

`Db` holds one writer connection behind a mutex, a pool of reader connections, an injectable clock (system or manual) and the writer term cache; `withView` pins a view to one read transaction.

## JSON Bridge

`Tiramemsu.Shell.Bridge` turns the Rust bridge's JSON forms (terms, times, eids, `transact` operations, view reads, reports) into `TxProg` bodies and `ReadProg` queries for the oracle driver.

## Differential Store Oracle

`oracle store` runs seeded random scripts through the pinned Rust driver and the Lean driver with the same manual clock (`m2.*` operations), compares every result, the final dumps and view reads, then cross-opens each build's file in the other.

## Merge Laws

`Tiramemsu.Model.Merge` defines statements as a 2P-set keyed by eid: merge keeps every eid, the smallest content and the earliest retraction; it is a model function only, with no database operation.
