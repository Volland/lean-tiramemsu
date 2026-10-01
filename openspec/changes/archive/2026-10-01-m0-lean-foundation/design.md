## Context

The repository holds only `lat.md/` and empty change folders; there is no Lean code. The Rust reference (`../tiramemsu`, linked as `tiramemsu/`) reaches SQLite through a small `Executor` trait (prepared statements, `BEGIN IMMEDIATE`, savepoints, read snapshots) and a writer + reader pool; its schema (format 1) has nine triple indexes, never-forget triggers and a `meta` counter table. The port keeps the file but moves all query evaluation into Lean (D3), so the only thing asked of SQLite is a sorted index with appends, one retraction update and range scans. See proposal.md for motivation and `lat.md/verification.md` for the trust boundary.

Constraints: runtime imports Lean core + Std + leansqlite only (D7, D8); proofs may use Mathlib; no hand-written C except the M6 ABI shim (D9); the Rust repository is read-only from here.

## Goals / Non-Goals

**Goals:**
- A store interface precise enough that M2/M3 theorems over `ModelStore` transfer to `SqliteStore` by testing alone, with no axiom.
- Policy gates that are mechanical (environment inspection, not grep where avoidable) and self-tested against seeded violations.
- An oracle that can be extended operation by operation as M1–M5 add behavior, without redesign.

**Non-Goals:**
- Schema creation, migrations and ObjectId encoding (M1). M0 works on files that already carry the format-1 schema.
- Engine verbs, views as queries, joins (M2, M3). The contract only exposes view predicates on single-index scans.
- Concurrency in the shell (writer mutex, reader pool on tasks): M2. M0 provides the per-connection primitives the pool needs.
- Performance targets (D14): benchmarks report only.

## Decisions

### 1. Lake layout

```text
lean-toolchain                 pinned release = Mathlib's lean-toolchain at the pinned Mathlib rev
lakefile.lean                  require mathlib @ rev, require sqlite (leansqlite) @ rev
Tiramemsu.lean                 runtime root
Tiramemsu/Store/Types.lean     rows, View, ScanSpec, StoreError            [verified]
Tiramemsu/Store/Order.lean     per-family keys, signed/NULL-first compare  [verified]
Tiramemsu/Store/Interface.lean ReadStore / WriteStore classes              [verified]
Tiramemsu/Store/Model.lean     ModelState, ModelStore instance             [verified]
Tiramemsu/Sqlite/Conn.lean     connection open, pragmas, tx, savepoints    [shell]
Tiramemsu/Sqlite/Sql.lean      fixed SQL text per family / op              [shell]
Tiramemsu/Sqlite/Store.lean    SqliteStore instance                        [shell]
Tiramemsu/Shell/Version.lean   versions reported by the CLI                [shell]
Main.lean                      `tiramemsu` exe: version, driver
TiramemsuProofs.lean, TiramemsuProofs/Store/{Order,Model}.lean
Policy/Main.lean               `policy-check` exe (imports Lean; never linked into runtime)
Policy/Fixtures/*.lean         seeded violations, built only by the checker self-test
Test/Main.lean                 `tiramemsu-tests` exe: binding probes, refinement
Oracle/Main.lean               `oracle` exe: differential harness + bench
oracle/rust-driver/            Cargo crate speaking the driver protocol over tiramemsu-json
oracle/RUST_PIN                pinned commit + evidence of reserve-replica-id
oracle/deviations.toml         registry of accepted differences
policy/verified-modules.txt    module prefixes that are verified
policy/toolchain-imports.txt   toolchain modules beyond Init/Std the runtime may import (initially empty)
policy/bv-decide-allowlist.txt theorem names allowed Lean.ofReduceBool (initially empty; M1 fills)
policy/theorem-index.toml      proven requirement -> theorem names
testdata/format1-schema.sql    DDL extracted from an empty file made by the pinned Rust build
scripts/ci.sh                  the one entry point CI and developers run
```

`lakefile.lean` over `lakefile.toml`: the import-closure and fixture targets need a little Lake scripting. Alternative rejected: separate Lake packages for proofs and runtime (two manifests to keep in sync, and toolchain pin duplicated). Mathlib is a workspace dependency, but only `TiramemsuProofs` and `Policy` import it; the policy checker proves the runtime closure is Mathlib-free.

`Lean` package modules (e.g. `Lean.Data.Json`) are not "core" for D7: runtime use requires listing the module in `policy/toolchain-imports.txt`, reviewed per entry. **[Decision beyond D1–D15]**

### 2. Verified vs shell modules

`policy/verified-modules.txt` lists module prefixes (`Tiramemsu.Store.Types`, `.Order`, `.Interface`, `.Model`; M1+ append theirs). A verified module imports only `Init`, `Std` and other verified modules, so leansqlite and `IO`-performing shell code cannot leak into anything a theorem talks about. Alternative rejected: a naming convention (`Tiramemsu.Verified.*`) — it forces module renames when code moves between tiers.

### 3. Store types and order

```lean
abbrev Id := Int64                       -- SQLite INTEGER; ObjectId codec arrives in M1
structure TripleRow where
  eid s p o tAdd : Int64
  tRet vFrom vTo retKind : Option Int64
structure TermRow  where id tag : Int64; lex : String; dt : Option Int64; lang : Option String; num : Option UInt64 -- f64 bits
structure TxRow    where t instant : Int64
structure VolatileRow where s key value updatedAt : Int64
inductive TxSel    | now | asOf (t : Int64) | history
inductive ValidSel | unfiltered | at (d : Int64)
structure View     where tx : TxSel; valid : ValidSel
inductive Family   | liveSpo | livePos | liveOsp | histSpo | histPos | histOsp | validP | logAdd | logRet
inductive Bound    | incl (v : Int64) | excl (v : Int64)
structure ScanSpec where family : Family; pre : Array Int64; lo hi : Option Bound; view : View
inductive Violation | idReused | retractOnce | termKeyTaken | instantTaken
inductive StoreError | violation (v : Violation) | notFound | invalidScan | misuse (what : String)
                     | sqlite (code ext : UInt32) (msg : String)
```

Keys (`Order.lean`) mirror the SQLite index definitions with the rowid appended, so the contract order is the order SQLite stores:

| Family | Key | Max prefix | Row filter |
|---|---|---|---|
| liveSpo/Pos/Osp | (s,p,o)/(p,o,s)/(o,s,p), t_ret, v_from, v_to, eid | 3 | t_ret = none |
| histSpo/Pos/Osp | perm, t_add **desc**, t_ret, v_from, v_to, eid | 3 | – |
| validP | p, v_from, v_to, eid | 1 | t_ret = none |
| logAdd | t_add, eid | 0 | – |
| logRet | t_ret, ret_kind, eid | 0 | t_ret ≠ none |

Values compare as signed 64-bit integers; `none` sorts before every value (SQLite NULL ordering). Bounds constrain the first key column after the prefix by value (so for `hist*` with a full prefix they bound `t_add` while order is descending); a row whose bounded column is `none` never satisfies a bound (SQL three-valued logic). `liveSpo` with a non-`now` view is `invalidScan`, as is a prefix longer than the family allows. The view predicate is the Rust mapping (D6): now ⇔ `t_ret = none`; asOf t ⇔ `t_add ≤ t ∧ (t_ret = none ∨ t_ret > t)`; at d ⇔ `(v_from = none ∨ v_from ≤ d) ∧ (v_to = none ∨ v_to > d)`.

Term `num` is f64 bits normalized the way SQLite stores REAL: NaN becomes `none`, −0.0 becomes +0.0 (SQLite stores integral REALs as integers). The model applies the same normalization on append, so the refinement test compares like with like. Term numeric range scans (`term_num`) and tx-instant ranges other than "latest at or before" are not in the M0 contract; the milestone that needs them adds them. **[Decision beyond D1–D15]**

### 4. Interface

```lean
class ReadStore (m : Type → Type) where
  scan      : ScanSpec → β → (β → TripleRow → m (ForInStep β)) → m β   -- ordered, early exit
  triple    : Int64 → m (Option TripleRow)
  termById  : Int64 → m (Option TermRow)
  termByKey : (tag : Int64) → (lex : String) → Option Int64 → Option String → m (Option Int64)
  txByT     : Int64 → m (Option TxRow)
  txAtOrBefore : (instant : Int64) → m (Option TxRow)                 -- greatest instant ≤ i
  counter   : String → m (Option Int64)
  volatileGet : (s key : Int64) → m (Option VolatileRow)
  volatileOf  : (s : Int64) → m (Array VolatileRow)                   -- ordered by key
  predMulti   : Int64 → m Bool
class WriteStore (m) extends ReadStore m where
  insertTriple : TripleRow → m Unit
  retract      : (eid t kind : Int64) → m Unit
  insertTerm   : TermRow → m Unit
  insertTx     : TxRow → m Unit
  setCounter   : String → Int64 → m Unit
  volatilePut  : VolatileRow → m Unit
  volatileDel  : (s key : Int64) → m Unit
  addPredMulti : Int64 → m Unit                                        -- idempotent
  begin commit rollback : m Unit
  savepoint rollbackTo release : String → m Unit
```

Readers are separate handles: `beginRead : m Snapshot` / `endRead`, with `ReadStore` provided on the snapshot. On the model, `beginRead` returns `committed`; on SQLite, a reader connection inside a read transaction.

Both run in a monad with `MonadExcept StoreError m`. Model: `StateT ModelStore (Except StoreError)`; a reader snapshot is a plain `ModelState` and reads run in `ReaderT ModelState (Except StoreError)`. SQLite: `ReaderT Conn IO` with errors lifted. Scans are folds with `ForInStep` so LFTJ (M3b) seeks via `lo` and stops early without materializing; alternatives rejected: returning `Array` (memory on large scans) and a cursor object (stateful, awkward to model).

`ModelStore = { committed : ModelState, current : ModelState, inTx : Bool, sps : List (String × ModelState) }`, `ModelState = { triples : List TripleRow, terms, txs, meta, volatile, predMulti }`. Each write checks its violation, and on error returns it with the state unchanged; this mirrors SQLite's statement-level abort (a failed statement does not end the transaction). Writes outside a transaction, `commit` without `begin`, nested `begin`, savepoint ops outside a transaction or with an unknown name are `misuse` in both stores (SqliteStore tracks its own state and never sends such SQL, so SQLite's implicit-transaction behaviour of `SAVEPOINT` never arises).

### 5. Theorems (TiramemsuProofs/Store)

Proven requirements are those in `store-contract` marked "Machine-checked". Informal → Lean-ish:

- Key order is a strict total order on rows with distinct eids, per family:
  `theorem keyLt_strictOrder (f) : IsStrictOrder TripleRow (keyLt f)` and
  `theorem keyLt_total (f) {a b} (h : a.eid ≠ b.eid) : keyLt f a b ∨ keyLt f b a`.
- Scan exactness and ordering, for a well-formed state (`WF st := st.triples.Pairwise (·.eid ≠ ·.eid)`) and a valid spec:
  `theorem scanList_mem (st spec) (hv : spec.Valid) : r ∈ st.scanList spec ↔ r ∈ st.triples ∧ spec.Matches r`
  `theorem scanList_sorted (hwf : WF st) : (st.scanList spec).Pairwise (keyLt spec.family)`
  `theorem scan_invalid (hv : ¬ spec.Valid) : st.scanList? spec = .error .invalidScan`
  `theorem scan_fold (st spec init f) : ModelStore.scan spec init f = foldWithExit (st.scanList spec) init f` (the monadic interface is the list fold).
- Well-formedness and atomicity of writes:
  `theorem op_wf (op) (hwf : WF s.current) : op.run s = .ok (_, s') → WF s'.current`
  `theorem op_error_unchanged (op) : op.run s = .error e → (state observed after the error) = s` (stated over the `tryCatch` result).
  `theorem retract_spec : retract eid t k` succeeds iff a row with that eid has `tRet = none`, and then the new state differs only in that row's `tRet := some t, retKind := some k`; it fails with `retractOnce` if the row is retracted and `notFound` if absent.
  `theorem insert_no_loss : insertTriple`/`insertTerm`/`insertTx` success ⇒ old rows ⊆ new rows and exactly one row added.
- Transactions and savepoints:
  `theorem rollback_restores : (begin *> ops *> rollback).run s` ends with `current = committed = s.committed` whenever it succeeds.
  `theorem rollbackTo_restores : (savepoint n *> ops *> rollbackTo n).run s` ends with the `current` it had after `savepoint n`, `n` still on the stack.
  `theorem commit_publishes : commit` sets `committed := current` and clears the stack.

Mathlib may be used (e.g. `List.Pairwise`, `List.Sorted`, order classes). No `decide` on large terms, no `bv_decide` (not codec). Each theorem appears in `policy/theorem-index.toml` under its requirement.

### 6. SqliteStore

Every read is one prepared statement with fixed SQL text per (family, prefix length, bound shape, view shape), an explicit `ORDER BY` equal to the family key (`eid` last; `t_add DESC` for history), and the view predicate in the Rust verbatim form (`t_ret IS NULL` for now, so the partial indexes qualify). Order is therefore guaranteed by SQL semantics, not by the plan; a test asserts with `EXPLAIN QUERY PLAN` that each shape uses the family's covering index and no temporary B-tree for ordering. Statements are prepared once per connection and reset between uses. `retract` is `UPDATE triple SET t_ret=?, ret_kind=? WHERE eid=? AND t_ret IS NULL`; with zero changed rows it looks the row up to report `notFound` or `retractOnce`. The never-forget triggers stay in force: they are the second line of defence and their `RAISE(ABORT)` messages map to the same violations.

`beginRead` issues `BEGIN` and then a read of `meta`, because a deferred SQLite transaction takes its WAL snapshot only at the first read; without it, the snapshot point would drift to the first scan.

Schema: until M1 creates it, tests create files by executing `testdata/format1-schema.sql`, which is extracted (`sqlite_master.sql` in rowid order, plus the initial `meta` rows) from an empty database created by the pinned Rust build, and checked against it in CI. **[Decision beyond D1–D15]**

### 7. leansqlite gap closure

Order of preference when the gap check finds something missing: (a) express it as SQL through the statement API (`PRAGMA journal_mode=WAL`, `BEGIN IMMEDIATE`, `SAVEPOINT`, `PRAGMA busy_timeout`); (b) upstream a patch to leansqlite and pin the merged commit; (c) pin a fork of leansqlite carrying the patch until it is upstreamed. Never C in this repository (D8, D9). If (b)/(c) cannot close a blocking gap, the change stops and D8 is revisited with the owner. **[Interpretation of D8's fallback]**

### 8. Policy checker

`policy-check` is a Lean executable that imports the built environments of `Tiramemsu` and `TiramemsuProofs` and inspects them; only source-level facts use text scans.

- Environment: every constant declared in either library — `collectAxioms` contains no `sorryAx` and no axiom declared in our modules; theorems' axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, plus `Lean.ofReduceBool` and the axioms it depends on in the pinned toolchain (e.g. `Lean.trustCompiler`) only for names in `bv-decide-allowlist.txt`. Verified modules: no `unsafe` constant, no `opaqueInfo` (catches `opaque` and `partial`), `implemented_by`/`extern` only where a `@[csimp]` theorem equates the two constants; import closure within verified modules + Init + Std.
- Source: no `native_decide` or `decide +native` token anywhere in both libraries; `bv_decide` token only in modules under `TiramemsuProofs.Codec`; every allowlist entry lives under `TiramemsuProofs.Codec`.
- Import closure: modules reachable from `Tiramemsu` and `Main` have roots in {Init, Std, SQLite (leansqlite), Tiramemsu} ∪ toolchain-imports allowlist; in particular no `Mathlib`, `Batteries`, `Aesop`, `Qq`, `Plausible`, `ProofWidgets`.
- Repository: no `.c`/`.h`/`.cpp` file outside `abi/` (D9) and outside `.lake/`.
- Theorem index: parse `openspec/specs/**/spec.md`; a requirement is proven if it has a scenario whose name begins with `Machine-checked`. Every proven requirement has ≥ 1 index entry, every entry names an existing requirement that is proven, and every listed theorem exists in `TiramemsuProofs` and passes the axiom rule. For specs of active changes the same check runs in report mode (pending entries listed, not failing); each change's final task runs it in strict mode on its own specs before archive. **[Decision beyond D1–D15]**

Self-test: `Policy/Fixtures` holds one module per rule with a seeded violation; the checker's self-test builds each and asserts it is rejected with the expected rule id. Alternative rejected: grep-only checks (miss `sorry` via macros and `partial` via `termination_by` tricks, and cannot see axioms).

### 9. Differential oracle

- Pin: `oracle/RUST_PIN` records the commit hash and the evidence path (the archived `reserve-replica-id` folder). The check is read-only: `git -C tiramemsu cat-file -e <pin>`, `git ls-tree` shows the archived change and no active one.
- Build: `git -C tiramemsu archive <pin>` unpacked into `.oracle/rust-<pin>/` (ignored), and `oracle/rust-driver` built with a path dependency on its `bindings/json` crate. Nothing is written into the Rust repository. Alternative rejected: `git worktree add` (writes the Rust repo's `.git`), a cargo git dependency (needs a remote and network).
- Driver protocol (both `oracle/rust-driver` and `tiramemsu driver`): JSON lines on stdin/stdout. Requests `{"id":n,"op":name,"args":{…}}`; responses `{"id":n,"ok":…}` or `{"id":n,"err":{"code":…}}`. Ops are the Rust JSON-bridge operation names plus driver ops `open`, `close`, `rawDump`. Both drivers answer `unsupported` for ops they do not implement yet; the harness skips a step only when the Lean side says `unsupported` and the step is marked as owned by a later milestone. **[Decision beyond D1–D15: Rust driver lives in this repo, not in the Rust repo]**
- Canonical form: object keys sorted; integers exact (arbitrary precision, never via f64); unordered result sets sorted by their canonical serialization; ordered results kept; errors compared by code only; doubles compared by lexical form (D11). `rawDump` emits every row of `meta`, `term`, `tx`, `triple`, `volatile`, `pred_multi` ordered by primary key — on Rust via plain rusqlite SQL, on Lean via `SqliteStore` reads.
- Shared files: a scenario is a list of steps, each tagged with the build that runs it; both builds operate in turn on one `.db` file (handoff after `close`), and results of steps marked `compare` are run on a copy by the other build and compared.
- Deviations: `oracle/deviations.toml` entries `{id, summary, spec, match}`; a mismatch passes only if a listed matcher covers it. First entries: `tm_path` and SQL UDFs/`rarray` unavailable on Lean connections.
- Bench: `oracle bench --n N` builds a deterministic fixture (same shape as Rust `bench/engine-comparison`: ~11·N statements, retracted names, `knows` edges) through the Rust driver, times workloads grouped by the gate categories of `lat.md/roadmap.md#Performance Gate` on each build that supports them, checks the results are equal, and writes JSON + Markdown with ratios. Exit status reflects harness errors and result mismatches only, never ratios (D14).

### 10. Test strategy (all M0 requirements except the two Machine-checked ones)

- Toolchain/build: CI on macOS arm64 and Linux x86_64 from a clean clone; `otool -L`/`ldd` on the executable shows no Lean shared library; executable runs with the toolchain removed from `PATH`.
- Policy: checker self-test against seeded fixtures; checker run on the real libraries.
- Binding: `tiramemsu-tests probe` — one probe per gap-check item (value round-trips at Int64 extremes, NULL vs 0, text with NUL, REAL normalization, savepoint semantics, snapshot isolation across two connections, >2 GiB file on 64-bit in the nightly job).
- Store contract: `tiramemsu-tests refine` — a seeded generator (core `StdGen`, no external library) emits sequences mixing valid and invalid writes, transaction and savepoint control, reader begin/end and all reads; each op runs on `ModelStore` and `SqliteStore` (one writer connection, up to three reader connections, interleaved on one thread) and every result is compared, including error variants. On mismatch the sequence is shrunk by delta debugging and written to `testdata/refine/` as a permanent regression case. CI: 200 seeds × 300 ops; nightly: 5 000 seeds × 1 000 ops plus runs starting from Rust-written fixture files.
- Oracle: the harness's own tests (canonicalization, deviation matching) plus the M0 scenario "Rust writes, Lean `rawDump` equals Rust `rawDump`".

## Risks / Trade-offs

- [leansqlite pins a toolchain different from Mathlib's] → choose the Mathlib rev whose toolchain leansqlite builds on; else bump leansqlite via upstream PR/fork (Decision 7); the gap check records the outcome.
- [`SQLITE_DISABLE_LFS` in leansqlite limits file size] → probe a >2 GiB file on 64-bit platforms; Rust fixtures reach 3.4 GB. Treated as a blocking gap if it fails.
- [Rust files carry `sqlite_stat1/4` and Rust runs `PRAGMA optimize`; the Lean build evaluates queries itself] → statistics tables are left untouched by M0; M1 decides whether the Lean build maintains them, so files stay readable either way.
- [The contract is trusted] → kept narrow (ordered scans, one update, atomic commits, WAL snapshots) and tested by refinement from the first commit; no axiom mentions SQLite.
- [Refinement tests single-threaded] → they cover snapshot semantics by interleaving connections; true parallel stress belongs to the M2 shell and pool.
- [Prerequisite outside this repo (reserve-replica-id)] → every task except the pin and oracle runs without it; the pin task blocks only Group 8.
- [`ORDER BY` on rowid tail might add a sort step on some SQLite versions] → correctness is unaffected; the plan test flags it and it is reported, not hidden.
- [Model proofs in an "unproven infrastructure" milestone add work] → limited to scan exactness, order and write atomicity, which every M2/M3 theorem needs anyway and which exercises the theorem index end to end. **[Decision beyond D1–D15]**
