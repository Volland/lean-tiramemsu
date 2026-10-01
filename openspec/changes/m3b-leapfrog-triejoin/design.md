## Context

See proposal.md for motivation. State after M3a: the logical IR has a reference denotation (bags of solution mappings) and an index nested-loop join (INLJ) proven equal to it for every pattern order. Stored triple rows are reached only through the M0 `Store` interface: ordered range scans over `spo`, `pos`, `osp` in the `live_*` and `hist_*` families, each scan taking a key prefix, an inclusive lower bound on the next key column, and the pattern's view predicate. The store contract (verification.md, Trusted Base) promises that a scan returns exactly the matching rows in key order. Keys are ObjectIds stored as SQLite `INTEGER`, so key order is signed 64-bit order (Rust data-model, ObjectId: low-bit tags keep signed order within a tag).

Constraints: D7 (runtime library uses Lean core and Std only; verified code total; no `partial`, `unsafe`, `native_decide`), D3 (no SQL evaluation), D13 (both joins proven order-independent, planner unproven), D14 (benchmarks report-only until M6).

## Goals / Non-Goals

**Goals:**
- One LFTJ implementation, generic over `Store`, that is the code the proofs talk about.
- A proof chain whose only store assumption is the scan contract, with violations detected at run time.
- A planner that is cheap (no SQL statistics, bounded probes), deterministic, explainable, and unable to change results.
- Beat the Rust build on the skewed cyclic fixtures of Rust `bench/triangles`.

**Non-Goals:**
- Proving planner heuristics optimal or proving any complexity bound for LFTJ (worst-case optimality is a design argument, measured by benchmarks).
- New index orders or schema changes (file format stays Rust format 1, D6).
- Joining path patterns, virtual-predicate patterns, optionals or subqueries inside LFTJ; they stay with M3a operators.
- Parallel (multi-task) LFTJ; one query runs on one Lean task (D10).

## Decisions

### 1. The LFTJ region of a join

Within one IR `Join`, the region is the set of *stored* triple patterns (constant or variable predicate, not a virtual predicate). Path patterns, virtual-predicate patterns (`tm:addedAt`, `sys:subject`, volatile keys, …), `Values` and nested operators are joined with the region's output by INLJ in planner order.
Correctness rests on bag-join commutativity and associativity, so the region is just one more join operand.
*Alternative:* virtual predicates as LFTJ tries. Rejected: they are functional in the eid, have no index order of their own, and would need a second trie kind with its own proofs for no measured gain.

### 2. Trie access kinds per pattern

For a variable order σ, each pattern gets one access kind, chosen by the planner and checked by the validity gate:

| Kind | Condition (index column order `c1 c2 c3`) | Level iterator |
|---|---|---|
| `contiguous ord` | the pattern's variable columns appear in σ-rank order and every column before a variable column is a constant or an earlier-ranked variable | one range scan per seek on prefix `(bound columns)` with a lower bound |
| `skipScan ord` | variable columns in σ-rank order, but a constant column follows a variable column | seek candidate `v`, then confirm with an existence seek on `(prefix, v, constants up to the next variable column)`; on miss, seek `v+1` |
| `materialized` | no rotation puts the variables in σ-rank order (only patterns with three variables, or an eid ranked before the pattern's own variables) | one scan of the constant prefix through the best index, filtered, projected, sorted lexicographically in σ order, grouped |

A repeated variable inside one pattern (`?x p ?x`) occupies one level; its later column is treated as bound once the variable is. With only rotations `spo`, `pos`, `osp`, every pattern with a constant has a non-materialized access for every σ; only three-variable patterns can need materialization.
*Alternative:* materialize every non-prefix level. Rejected: the hub-and-spoke triangle would materialize 1.1 M rows per pattern. *Alternative:* add `sop`, `pso`, `ops` indexes. Rejected: file-format change (D6) and +60 % index size.

### 3. Level iterator over SQLite with a read-ahead buffer

A store-backed level iterator keeps the bound prefix, the current key, and a buffer of up to `B` rows read from the last range scan. `seek k` gallops inside the buffer when `k` is within it and issues a new scan with lower bound `k` otherwise; `next` is `seek (key + 1)` (end of iterator at `Int64.max`). `B` starts at 8 and doubles on each consecutive buffer hit up to 256, so dense sequential levels amortise the per-statement cost of leansqlite and sparse leapfrog seeks do not over-read. The pattern's leaf group (rows sharing the full key) is read from the same buffer.
*Alternative:* one prepared-statement step per seek. Rust's LFTJ note (Rust `lat.md/query.md`, LFTJ) names the per-statement cost as what must be amortised; kept as the `B = 1` degenerate case for tests.

### 4. Termination by key headroom, contract checked

Every iterator operation returns a key `k' ≥ k` for `seek k` or ends. The implementation checks `k' ≥ k` (and strict increase across `next`) and raises `QueryError.storeContract` otherwise. The leapfrog loop is defined by well-founded recursion on `(remaining levels, Int64.max - lowerBound)` (lexicographic), with the run-time check supplying the decrease proof. Hence the operator is total for any store, including a lying one, and no fuel is needed. Under the scan contract the check never fires (proven).
*Alternative:* fuel equal to the sum of pattern sizes. Rejected: sizes are unknown on SQLite without counting scans, and a fuel-exhaustion path would need its own sufficiency theorem.

### 5. Bag multiplicities at the leaves

The trie levels are the variables of σ (including eid variables of region patterns). When a pattern's last level is bound, its *leaf group* is the rows with that full key under the view. Its multiplicity is 1 under `SetOfTriples` with no eid variable, the group size under `BagOfEids` with no eid variable, and with an eid variable the group's eids form that variable's level (sorted in memory, distinct by construction). An output mapping is emitted with multiplicity equal to the product of the leaf multiplicities. This is exactly the bag natural join of M3a's per-pattern denotations, which carry the `graph_set` flag. `match_mode = RelIsomorphism` and filters stay as IR operators above the join, as in INLJ.

### 6. Streaming core, list specification

The runtime core is `lftjFold : LftjPlan → Store → (β → Mapping → m β) → β → m β`, so a three-million-row triangle count never materialises. The proofs use `lftjList` (fold with cons) and a lemma `lftjFold f b = (lftjList …).foldlM f b`.

### 7. Planner: validity gate makes heuristics irrelevant

The planner produces `JoinPlan := inlj (order : List PatIx) | lftj (σ : List Var) (access : PatIx → Access)` per region. Before execution `JoinPlan.valid region : Bool` checks that the order is a permutation of the region's patterns, σ is a duplicate-free permutation of the region's variables, and each access kind satisfies the condition of Decision 2. An invalid plan (a planner bug) is replaced by the canonical plan (INLJ in text order), and explain shows a `planner-fallback` note. All heuristics below are unverified.

- **Routing:** GYO reduction over the hypergraph whose hyperedges are the variable sets (eid variables included) of the region's patterns. Cyclic goes to LFTJ, acyclic to INLJ, subject to option `lftj := auto | always | never` (default `auto`) and threshold `lftjSmallRows`: if every pattern's estimate is ≤ `lftjSmallRows`, INLJ is used even for cyclic regions. Initial value 256, recalibrated by the benchmark (task 7.4).
- **Estimates:** pattern estimate = min(per-predicate count for its family, bounded probe). The probe counts the rows of the constant prefix scan, up to a cap of 1024. A variable predicate uses the family's total row count (M0 counters). `AsOf`/`History` use `hist` counts and `valid At` uses the unfiltered count (an upper bound).
- **Count cache:** `PredCounts`, an immutable map `(pred, family) → Nat` behind an `IO.Ref`, stamped with the last `t` it reflects. Entries are filled lazily by a counting scan of `*_pos` prefix `(p)`. After each commit through this process the writer applies the transaction's per-predicate deltas and swaps in the new map. When a reader sees a snapshot whose last `t` differs from the stamp plus known deltas (another process wrote), it drops the cache. Readers use whatever map is current; staleness changes speed only.
- **INLJ order:** greedy. Start at the smallest estimate, then repeatedly take the connected pattern (sharing a bound variable) with the smallest estimate after binding. Ties are broken by text position. Cartesian steps come only when nothing connected is left.
- **LFTJ σ:** greedy. The first variable comes from the smallest-estimate pattern: the one occurring in the most region patterns. Then repeatedly add the unchosen variable that co-occurs with chosen variables in the most patterns, ties by the smallest estimate of a containing pattern, then first text occurrence. Eid variables that occur in one pattern only go last. A repair pass tries bounded adjacent swaps (at most |σ|²) that remove a `materialized` access for a pattern whose estimate exceeds `lftjSmallRows`, and keeps the first swap that does. Each pattern's access is then the non-materialized kind with the fewest skip-scan levels, ties by order `spo`, `pos`, `osp`.
- **Determinism:** the plan is a pure function of (IR, count snapshot, options); no hashing order, clock or randomness is consulted.
*Alternative:* reuse SQLite statistics (`sqlite_stat4`). Rejected: Lean evaluates the joins and Rust's `ANALYZE` cadence would become a Lean dependency; bounded probes are exact for the selective cases that matter.

### 8. Module layout

```
Tiramemsu/Exec/Lftj/Key.lean         -- Int64 key order, successor, headroom measure
Tiramemsu/Exec/Lftj/Access.lean      -- Access kinds, fits check (Decision 2)
Tiramemsu/Exec/Lftj/LevelIter.lean   -- contiguous / skipScan / materialized iterators, buffer
Tiramemsu/Exec/Lftj/Leapfrog.lean    -- leapfrog intersection over k level iterators
Tiramemsu/Exec/Lftj/Triejoin.lean    -- lftjFold, leaf groups, multiplicities, lftjList
Tiramemsu/Plan/Region.lean           -- region extraction from Join
Tiramemsu/Plan/Cyclic.lean           -- GYO reduction
Tiramemsu/Plan/Stats.lean            -- PredCounts cache, probes, commit hook
Tiramemsu/Plan/Order.lean            -- INLJ order, LFTJ sigma, access choice
Tiramemsu/Plan/JoinPlan.lean         -- JoinPlan, valid, fallback, exec dispatch
Tiramemsu/Plan/Explain.lean          -- join-plan section of explain
TiramemsuProofs/Exec/Lftj/{Leapfrog,LevelIter,Triejoin,Total}.lean
TiramemsuProofs/Plan/JoinPlan.lean
bench/triangles/  bench/plan-quality/  tests/Lftj/  tests/Plan/
```

### 9. Theorem statements (Tier 2)

Notation: `S` a `Store` instance with pure scans, `st : S.State`, `ScanContract S st` the M0 contract predicate (satisfied by `ModelStore` for every state, by an M0/M2 theorem), `⟦·⟧` M3a's reference denotation (a `List Mapping` read as a bag), `~` is `List.Perm`.

1. Leapfrog intersection (requirement *Leapfrog intersection is exact*):
   `theorem leapfrog_spec (ls : List (List Key)) (hne : ls ≠ []) (hs : ∀ l ∈ ls, l.Sorted (· < ·)) : (leapfrog ls).Sorted (· < ·) ∧ ∀ x, x ∈ leapfrog ls ↔ ∀ l ∈ ls, x ∈ l`.
2. Iterator refinement, one per kind (requirement *Trie iterators are faithful*): with `rest it : List Key` the model of an iterator,
   `theorem seek_rest (hc : ScanContract S st) : rest (it.seek k) = (rest it).dropWhile (· < k)`, and
   `theorem level_keys (hc) (hfit : Access.fits σ P a) : rest (open S st P a σ prefix) = sortedDistinct ((⟦P⟧ st).filterMap (proj σ prefix))`.
3. Leaf multiplicity (requirement *Bag multiplicities are preserved*):
   `theorem leaf_count (hc) : leafMult S st P a key = ((⟦P⟧ st).filter (agrees key)).length` under `BagOfEids`, and `= if … then 1 else 0` under `SetOfTriples` without eid variable.
4. Main theorem (requirement *LFTJ equals the reference join for every variable order*):
   `theorem lftj_perm_denote (σ : List Var) (hσ : σ.Nodup ∧ σ.Perm (vars ps)) (acc) (hacc : ∀ P ∈ ps, Access.fits σ P (acc P)) (hc : ScanContract S st) : lftjList S st ⟨σ, acc⟩ ps = .ok r ∧ r ~ ⟦Join ps⟧ st`.
   Corollary `lftj_perm_denote_model` drops `hc` for `ModelStore`.
5. Totality and contract (requirement *LFTJ is total and detects contract violations*): totality is the definitions' acceptance with `termination_by` under the proof-policy gates; plus
   `theorem lftj_no_contract_error (hc : ScanContract S st) : lftjList S st p ps ≠ .error .storeContract`.
6. Streaming (supporting): `theorem lftjFold_eq (f b) : lftjFold S st p ps f b = (lftjList S st p ps).bind (·.foldlM f b)`.
7. Plan gate (join-planner requirement *Plans cannot change results*):
   `theorem execRegion_valid (p : JoinPlan) (hv : p.valid ps = true) (hc) : execRegion S st p ps = .ok r → r ~ ⟦Join ps⟧ st`, from item 4 and M3a's INLJ theorem, plus
   `theorem join_split (ps qs) : ⟦Join (ps ++ qs)⟧ st ~ ⟦Join [Join ps, Join qs]⟧ st` if M3a does not already provide it.

Each theorem is registered in the theorem index against its requirement; `#print axioms` must stay within `propext`, `Classical.choice`, `Quot.sound` (no `bv_decide` here, D12).

### 10. Test strategy for unproven parts

- **SqliteStore refinement (Tier 4):** property tests generate random stores (assert, retract, supersede, re-assert, valid-time episodes), random BGPs of 1 to 6 patterns with shared, repeated and eid variables, random per-pattern views, and random valid σ. They check `lftjList` on `SqliteStore` against `ModelStore` and against `⟦·⟧`, with `B ∈ {1, 2, 256}` to exercise buffer edges, and keys near `Int64.min` and `Int64.max`.
- **Faulty store:** a test `Store` wrapper that returns out-of-order keys must yield `storeContract`, never wrong rows.
- **Rust oracle:** the triangle fixtures and the skewed fixture are queried on the same `.db` file by the pinned Rust build and by Lean; result multisets (or counts) must be equal. This check is a hard test, unlike the timing ratios.
- **Planner:** golden tests over fixed IR and fixed count snapshots for routing, σ, access kinds, INLJ order and explain text; GYO unit cases (triangle, 4-cycle, chain, star, two patterns sharing two variables); differential test that `lftj = never | auto | always` return bag-equal results on all property-test queries.
- **Benchmarks:** `bench/triangles` ports the Rust fixtures with a deterministic generator (fixed seed, own PRNG, edge list written once and loaded into one `.db` read by both builds). Fixtures: uniform out-degree 5 (500 k edges); 300 hubs × 1 500 spokes both ways plus 200 k noise edges; layered 3 × 150, 300 and 600 with 3 closers each. `bench/plan-quality` ports the skewed fixture: one huge class, one rare predicate, churned properties. Reports are median of 5 with ratios against Rust.

## Risks / Trade-offs

- [Per-seek leansqlite overhead dominates on uniform graphs, where Rust already matches an intersection join] → adaptive buffer (Decision 3), and the uniform ratio is reported; the M6 gate requires only "faster" on skewed cyclic shapes.
- [Skip-scan levels degrade when a subject has many predicates but not the constant one] → planner prefers contiguous access, and skip-scan is driven by the other iterators in leapfrog, which bound the seeks; measured in the plan-quality fixture.
- [Materialized tries for three-variable patterns can be large] → repair pass avoids them above `lftjSmallRows`; memory reported by the benchmark.
- [Proof of the main theorem is the largest Tier-2 proof] → split into the generic model lemma (tries as sorted lists, independent of the store) and per-kind refinement lemmas, so store details never enter the join proof.
- [Count cache drift with external writers] → stamp check against the snapshot's last `t`; drift affects speed only, by construction of the validity gate.
- [M0 scan interface lacks a lower bound or row limit] → this change adds none; if absent, M0 is amended before task 2, since a seek without a lower bound would make LFTJ quadratic.

## Open Questions

- The exact default for `lftjSmallRows` and the buffer cap `B` are calibrated by benchmark (tasks 7.3 and 7.4); the specs only require that they exist and cannot affect results.
