## Context

See proposal.md for motivation. Constraints that shape the design:

- M0 provides the `Store` interface (ordered range scans over `spo`/`pos`/`osp` live and history orders, appends of statement, term and tx rows, the single retraction update, counters, savepoints), the pure `ModelStore`, the leansqlite-backed `SqliteStore`, CI proof gates and the pinned Rust oracle. M1 provides `ObjectId` with origin bits (D15), the term dictionary and the byte-identical schema and triggers.
- The engine is written once, generic over `Store` (architecture, Store Abstraction). Theorems are stated over `ModelStore` only; `SqliteStore` is tied to it by refinement tests, never by axioms (D7, verification Trusted Base).
- Runtime code imports Lean core and Std only; verified modules are total (explicit fuel with a sufficiency theorem), no `partial`, no `implemented_by` without `@[csimp]` (D7).
- Behaviour, eids, report contents and file contents must match the pinned Rust build (D6). Rust reference: `tm-core/src/engine/*`, `read.rs`, `view.rs`, `clock.rs`, `tiramemsu/src/{db,view,pool}.rs`.

## Goals / Non-Goals

**Goals:**

- One generic engine whose model instance carries the Tier 1 theorems listed below, each mapped in the theorem index to the requirement it proves.
- Theorems that quantify over every transaction body, every clock reading and every view, not over hand-picked scripts.
- Rust-identical eid allocation order, so that differential tests compare files row for row.

**Non-Goals:**

- Query evaluation, `GRAPH` patterns, paths, bundles (M3a/M3b/M4). M2 offers only the view reads the engine and its tests need.
- Proving predicate-schema enforcement, named-graph verbs, volatile upserts or the shell: they are tested (scenario, refinement, differential, concurrency), not proven.
- A user-facing merge or replication operation (D15: laws only).
- Statistics upkeep (`PRAGMA optimize` cadence) beyond what affects files; `sqlite_stat*` tables are excluded from differential comparison.

## Decisions

### 1. Transaction bodies are a free monad over a verb signature

A body is a value `TxProg α`: `pure a` or `step (v : Verb β) (k : β → TxProg α)`, where `Verb` is an indexed inductive with one constructor per write verb (assert, create, retract, retractMatching, supersede, confirm, upsert, meta, newNode, newBNode, setVolatile, clearVolatile, addToGraph, removeFromGraph, clearGraph, createGraph, dropGraph) and per read (triples, values, dependents, schema, encode, lookup, decode). `ReadProg α` is the same construction over the read constructors only and is what speculative callbacks get. One interpreter `TxProg.run : TxProg α → TxM m α` runs it on any `[Monad m] [Store m]`, where `TxM m := StateT TxCtx (ExceptT Error m)` and `TxCtx` holds `t`, `instant`, options, counters and the report under construction.

- Why: theorems quantify over all bodies by induction on `TxProg`; continuations let a body use the eid returned by one verb in the next; the same body value runs on `ModelStore` and `SqliteStore`, so refinement tests and theorems talk about the same program; a body cannot perform IO, so a re-entrant write is unrepresentable (deviation from Rust, where it fails at runtime with a re-entrancy error).
- Alternatives: raw `TxM` closures (no induction principle, allow IO and re-entrancy); a subtype of `TxM` carrying a preservation proof (pulls proofs into the runtime library, against D7); a flat `List Op` script (no data dependency between operations).
- `TxProg : Type → Type 1` because `step` quantifies over `β`; `Monad` is universe-polymorphic, so do-notation works. Later milestones add `Verb` constructors (for example query reads for SPARQL Update); each needs its own preservation lemma, and read constructors get it for free.

### 2. Module layout

```
Tiramemsu/Engine/Types.lean      Row, Retraction, RetKind, Valid, Patch, Asserted, TxOptions, TxReport, Error cases
Tiramemsu/Engine/Interval.lean   Valid.check, overlaps, validAt
Tiramemsu/Engine/Prog.lean       Verb, TxProg, ReadProg, TxCtx, TxM, TxProg.run
Tiramemsu/Engine/Walk.lean       walk (BFS over a visibility predicate, fuel = row count + 1)
Tiramemsu/Engine/Schema.lean     PredicateSchema read, flag validation, schema-change conflicts
Tiramemsu/Engine/Pipeline.lean   write pipeline (positions → reserved → interval → schema → idempotency → unique → cardinality → alloc → self-ref → insert → pred_multi)
Tiramemsu/Engine/Verbs.lean      assert, create, retract, retractMatching, confirm, upsert, meta, newNode, newBNode
Tiramemsu/Engine/Supersede.lean
Tiramemsu/Engine/Graph.lean      membership verbs
Tiramemsu/Engine/Volatile.lean
Tiramemsu/Engine/Transact.lean   transactCore, dryRunCore, speculateCore (generic; savepoints through Store)
Tiramemsu/View/Spec.lean         TxSel (now | asOf (tx t | instant ms) | history), ValidSel (unfiltered | at d), visible
Tiramemsu/View/Read.lean         triples, values, dependents, eventsSince, graphMembers, graphs, resolveInstant, basisT
Tiramemsu/Model/Merge.lean       StmtSet, RowState.join, merge (pure, no user API)
Tiramemsu/Shell/Clock.lean       Clock := IO Int, systemClock, ManualClock (IO.Ref)
Tiramemsu/Shell/Pool.lean        reader pool
Tiramemsu/Shell/Db.lean          Db.open, transact, dryRun, speculate, withView
TiramemsuProofs/Store/{Invariant,Lifecycle,TxLog,Assert,Cascade,Supersede,Views,Speculation,Volatile,Merge}.lean
tests/Store/{Scenarios,Refinement,Differential,Concurrency}/…
```

### 3. Key types

- `Row := { eid : Eid, s p o : ObjectId, tAdd : Nat, ret : Option Retraction, valid : Valid }` with `Retraction := { t : Nat, kind : RetKind }` and `RetKind := explicit | cascade | supersede | cardinality` (codes 0–3). One `Option` for `t_ret` and `ret_kind` makes "kind set iff retracted" true by construction; the store maps it to the two columns.
- `Valid := { vFrom vTo : Option Int }`; `Patch := { o : Option Term, vFrom vTo : Option (Option Int) }` (outer `none` keeps, `some none` clears). `Patch` has no subject or predicate field, so patching them is unrepresentable in Lean; the M6 bridge rejects such JSON with `InvalidPatch`.
- Transaction numbers and id counters are `Nat`; instants and valid times are `Int`. `SqliteStore` rejects values outside `Int64` and counters beyond the 48-bit payload (D15) with a store error before writing (deviation from Rust overflow behaviour, unreachable in practice).
- `ModelStore` (M0) holds `rows` (ascending eid), `terms`, `txs : List (Nat × Int)`, `volatile`, `predMulti`, and counters `nextStmt nextNode nextBNode nextTerm lastT lastInstant multiVersion`. The model's savepoint is a saved copy.

### 4. Engine algorithms (Rust-compatible order)

- `walk vis root`: root first, then breadth-first; each expansion scans `s = x` and `o = x` among rows satisfying `vis`, unions, sorts by eid, appends unseen eids. `cascadeSet = walk live` (computed before any retraction, aborts with `CascadeLimitExceeded` when the size would exceed `maxCascade`), `dependents v = walk (visible v)` with no limit.
- `retractRoot e kind`: no-op `false` unless `e` live; subject-type retraction check; retract the cascade set in walk order, root with `kind`, others with `cascade` if `kind = explicit` else `kind`. Memberships go to the report's membership list.
- Supersede: load root (must be live), resolve patch, `InvalidPatch` on empty interval or no change, schema checks for the new root content, cascade set `C`, allocate `σ` in `C` order, retract `C` (kind supersede), unique and cardinality-one for the new root, insert replays in `C` order skipping `sys:inGraph` rows, insert the link `(σ root, sys:supersedes, root)`.
- Instant: `nextInstant prev now := max now (prev + 1)`; the shell reads the clock after taking the writer lock and `BEGIN IMMEDIATE`.
- Speculation on SQLite: `BEGIN IMMEDIATE; SAVEPOINT spec; ops; query on writer; ROLLBACK TO spec; RELEASE spec;` then write the advanced id counters (only if any advanced) and `COMMIT`; if that fails, burn in a separate writer transaction. On the model: run on a copy, keep the original with id counters raised to the copy's.

### 5. Shell (D10)

`Db` owns one writer connection behind a `Std.Mutex` and a pool of reader connections (default 4). `Db.withView spec f` takes a reader, opens a read transaction, reads `basisT` (the last committed `t` in that snapshot) and runs `f` against that one snapshot; the reader returns to the pool when `f` ends. A View is therefore pinned to one WAL snapshot for its whole scope (Rust pins per read; listed deviation). The term cache is append-only and is updated only after a successful commit.

### 6. Theorem statements (TiramemsuProofs)

`Model.transact now opts prog st : Except Error (α × TxReport × ModelStore)` is `transactCore` at the model instance with clock reading `now`; `Model.speculate`, `Model.dryRun` likewise. `live r := r.ret = none`. `StandsOn vis st x y := vis x ∧ (x.s = y.oid ∨ x.o = y.oid)`.

Invariant and order:

- `WF st`: eids strictly ascending; every eid counter `< nextStmt`; `1 ≤ tAdd ≤ lastT`; `ret = some x → tAdd ≤ x.t ≤ lastT`; no row has its own eid as `s` or `o`; every interval nonempty; subjects subject-capable, predicates IRIs; `txs.map (·.1) = range' 1 lastT`; instants strictly increasing; `lastInstant` = last instant or 0.
- `Extends a b`: every row of `a` is in `b` with equal eid and content, and equal `ret` or `a`'s `ret = none` and `b`'s `ret = some x` with `x.t > a.lastT`; `a.txs` is a prefix of `b.txs`; `a.terms` is a prefix of `b.terms`; id counters non-decreasing; rows of `b` not in `a` have eid counter `≥ a.nextStmt`. `Extends` is a preorder.

| Requirement (capability) | Statement |
|---|---|
| Never-forget invariant (statement-lifecycle) | `WF st → Model.transact now opts prog st = .ok (a, r, st') → WF st' ∧ Extends st st'` for all `now`, `opts`, `prog`; same for `Model.dryRun` and `Model.speculate` (states differ only in id counters). Proof: per-`Verb` lemmas over the in-transaction form `WFIn t`, closed under `pure`/`bind` by induction on `TxProg`. |
| Retracted once, eid never reused (statement-lifecycle) | corollaries of `Extends`: `r.ret = some x → (find b r.eid).ret = some x`; new eids `≥ a.nextStmt`, and `nextStmt` never decreases across commits, dry runs and speculation. |
| Gap-free log, tx row always (transaction-log) | `Model.transact … st = .ok (_, r, st') → st'.txs = st.txs ++ [(st.lastT + 1, nextInstant st.lastInstant now)] ∧ r.t = st.lastT + 1`, for every `prog` including `pure ()`. |
| Monotone instants for any clock (transaction-log) | `∀ prev now, prev < nextInstant prev now`; with the previous row, `WF` (strict instants) holds after any sequence of commits whatever the clock readings. |
| Idempotent assert (memory-verbs) | if `s p o` pass the type checks and the smallest live overlapping match is `e`, `assert s p o v .return` returns `.existing e` and leaves `rows` unchanged; `assert x; assert x` returns `(a, .existing a.eid)` and has the rows of a single `assert x`. |
| Supersede replay (memory-verbs) | on success at `t` with cascade set `C` and `σ m = nextStmt + index C m`: every `m ∈ C` has `ret = some ⟨t, supersede⟩`; the new rows are exactly `(C.filter (¬ membership)).map (replay σ patch root) ++ [link]` in that order; `replay` rewrites `s`,`o` through `σ` (identity outside `C`), keeps `p` and valid time, and applies the patch to the root only; every other row is unchanged except cardinality-one retractions of the new root's other objects, which have kind `cardinality`. |
| Cascade = closure (retraction-cascade) | `WFIn t st → live e → (cascadeSet st e).toFinset = {x | ReflTransGen (StandsOn live st) x e}`, the list is `Nodup` with head `e`, the fuel bound suffices, and the limit error occurs iff the closure has more than `maxCascade` elements; `retract e` retracts exactly that set, root `explicit`, rest `cascade`. |
| Dependents on any view (retraction-cascade) | `(dependents st v e).toFinset = if visible v e then {x | ReflTransGen (StandsOn (visible v) st) x e} else ∅`; `dependents st now e = cascadeSet st e` as lists. |
| As-of = log replay (temporal-views) | `(triples st (asOf (.tx t))).map key = replay (events st) t` (sorted by eid), and `WF a → WF b → Extends a b → triples b (asOf (.tx a.lastT)) = triples a now` (rows masked as of `t`). |
| Instant resolution (temporal-views) | `resolveInstant st ms = max {t | instant t ≤ ms} ∪ {0}`, monotone in `ms`, and `resolveInstant st (instant t) = t`. |
| Half-open validAt (temporal-views) | `validAt d ⟨a?, b?⟩ ↔ (a? = none ∨ a ≤ d) ∧ (b? = none ∨ d < b)`; `overlaps i j ↔ ∃ d, validAt d i ∧ validAt d j` for nonempty `i j`; `triples st ⟨sel, at d⟩ = (triples st ⟨sel, unfiltered⟩).filter (validAt d)`. |
| Speculation purity (speculative-transactions) | `Model.speculate now ops q st = .ok (r, st') →` `st'` equals `st` except id counters, every view read on `st'` equals the read on `st`, `r` is `q` evaluated on the speculative state, and every id allocated inside is below `st'`'s counters. `Model.dryRun` returns the report that `Model.transact` would. |
| Views ignore volatile (volatile-state) | `triples`, `dependents`, `eventsSince` do not depend on `volatile`; `values` under `asOf`/`history` returns only statement objects. |
| Merge laws (merge-laws) | `lookup (merge a b) e = join (lookup a e) (lookup b e)`; `merge` is commutative, associative, idempotent on strictly sorted `StmtSet`s; if `a` and `b` agree on content per eid, merge keeps every eid and content, keeps every retraction (live in merge iff live wherever present), and preserves row-level `WF`. |

`join` on per-eid states: absent is the bottom; content ties break by the lexicographic order of rows so the laws hold unconditionally; retraction is `none ⊔ r = r`, `some x ⊔ some y = some (min x y)` under `(t, kind)` lexicographic order ("earliest retraction").

### 7. Test strategy for unproven requirements

- Scenario tests: every spec scenario is a `lake test` case, run on both `ModelStore` and `SqliteStore`.
- Refinement: a seeded generator of random `TxProg` values (all verbs, random failures, dry runs, speculation, manual clock) runs on both stores; every result, report, error kind, every view read at every `t`, and the table contents must be equal.
- Differential (D6): the same scripts run through the pinned Rust oracle with the same manual clock on separate files; canonical dumps of `triple`, `term`, `tx`, `meta`, `volatile`, `pred_multi` and the reports must be equal. Cross-open: files written by one build are read by the other.
- Concurrency: N reader tasks and one writer task on one file; each reader records `basisT` and its reads; afterwards the model replays the writer's committed log and each recorded read must equal the model read `asOf basisT` (exact by the as-of theorem).

### 8. Store operations M2 relies on

Beyond the M0 list: volatile upsert/delete/point lookup, `pred_multi` insert-if-absent, a point lookup by eid, savepoint/rollback-to/release, and a read of `meta.last_t` inside a read transaction. If M0's interface does not contain one of these, M2 adds it with a contract test and a refinement case.

## Risks / Trade-offs

- [Proof effort for supersede and BFS order] → Prove set-level statements first (closure, retracted set, replayed set), then list order from the shared `walk`; the exact Rust order is also covered by differential tests.
- [Free-monad interpretation overhead] → One closure call per verb, negligible next to SQLite I/O; checked by the report-only write benchmarks (D14).
- [Model and engine drift, e.g. `ModelStore` scans not matching the store contract] → Contract tests from M0 plus verb-level refinement over random programs.
- [Pinned views hold a reader for their whole scope] → Pool waits rather than fails; scopes are callbacks, so a reader cannot leak; long scopes are documented as costly.
- [IO-free bodies are less flexible than Rust closures] → Callers do IO before the transaction and pass values in; reads of uncommitted state are verbs; later milestones extend `Verb`.
- [Merge on retractions compares local `t` across replicas] → Merge is not a user operation; the laws hold for any total order, and the order is revisited when replication is designed.
