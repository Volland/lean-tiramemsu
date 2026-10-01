## Context

See proposal.md (Why). M5 starts from v1 plus M4: the proven M3 IR with its denotation, the INLJ/LFTJ evaluator, the path engine (`REACH`, `TRAIL`, `ANY_SHORTEST`, `ALL_SHORTEST`, virtual layer hops, hop cap and state guard), the proven M2 store (memory verbs, cascade, supersede replay, views, predicate schema, vocabulary, volatile state), and the engine written once over the `Store` interface (`ModelStore`, `SqliteStore`). Constraints that shape the design:

- Front-end lowering is proof Tier 3: tested, not proven (D2, verification Proof Tiers). Nothing in M5 adds theorems; it must not weaken any existing one.
- Runtime code imports Lean core and Std only (D7). There is no openCypher parser, regex engine, tz database or full Unicode case mapping in Std, and no hand-written C beyond the ABI shim (D1, D8, D9).
- All evaluation runs in Lean; SQLite only serves range scans (D3).
- Results, written statements, transaction reports and error kinds must match the pinned Rust build on shared files, with every deviation listed (D6).
- Rust reference behaviour: `tm-cypher` (parser adapter over `open-cypher` 0.2.1, sema, IR lowering for patterns and views, a Rust interpreter for values) and its openCypher TCK run with a 1 269-line expected-failure list.

## Goals / Non-Goals

**Goals:**

- Same Cypher subset, extensions and results as the pinned Rust build, on either store implementation.
- Every graph-matching decision (patterns, label and property-map existence, isomorphism, paths, time views) executes in the proven IR evaluator and path engine, so the only unproven logic is lowering and value-level evaluation.
- Every Cypher write is a sequence of M2 verbs inside one M2 transaction, so the M2 theorems (never forget, idempotent assert, supersede replay, cascade closure, speculation purity) cover Cypher writes by construction.
- A conformance harness strong enough to stand in for proofs at Tier 3: Rust differential, TCK, cross-dialect, generated queries.

**Non-Goals:**

- A formal semantics of openCypher, or proofs about lowering (overview Non-Goals, D2).
- Constructs Rust rejects (`FOREACH`, `LOAD CSV`, `CALL … IN TRANSACTIONS`, schema commands, quantified path patterns, GQL path modes, pattern comprehension, user procedures, durations, `time`/`localtime`): they stay `Unsupported`.
- Cypher syntax for time-respecting paths or graph sets (also "later" in Rust).
- Performance targets (D14: report-only until M6).

## Decisions

### 1. Split: proven IR for patterns, tested interpreter for values (not covered by D1–D15)

Each `MATCH` / `OPTIONAL MATCH` / `EXISTS` / `MERGE`-match is lowered to one IR operator tree and evaluated by the M3 evaluator. Incoming rows enter the tree as an IR `values` relation over their graph-typed columns (ObjectIds), so joins with earlier clauses also run in the proven evaluator. Cypher values that the IR cannot hold (lists, maps, paths, temporal values with offsets) stay in the interpreter row, keyed by a row index column carried through the IR. Expressions, functions, projection, aggregation, ordering, `UNWIND`, `UNION`, `CALL` composition and procedures run in a tested Lean interpreter, as in Rust.

- Alternative: extend the IR with Cypher values and functions. Rejected: it widens the Tier 2 proof surface (denotation of lists, maps, regex, time zones) for no claim the project makes.
- Alternative: evaluate patterns in the interpreter too. Rejected: it would bypass the proven joins and paths, the point of the port.

### 2. Hand-written parser with byte spans (not covered by D1–D15)

A recursive-descent parser with a Pratt expression parser, over UTF-8 byte offsets of the original text, parses the openCypher grammar and the extensions natively (`USE` time clauses, `MATCH REPEATABLE ELEMENTS` / `DIFFERENT RELATIONSHIPS`, `CALL { }` bodies). There is no span-preserving prepass: spans point into the original text by construction. Constructs outside the subset are parsed far enough to be named in an `Unsupported` error.

- Contract with Rust: same accept/reject decision, same error kind, same span start offset. Message text is free: deviation **DV-C1**, because Rust's messages come from `open-cypher`.
- Alternatives: binding `open-cypher` (Rust, needs C glue, forbidden by D1/D9); a parser generator (none in core/Std).
- The parser is fuel-free structural recursion on the token array position with a termination proof by `decreasing_by` on remaining length, so it needs no `partial`.

### 3. Module layout

```
Tiramemsu/Cypher/
  Syntax/Span.lean Token.lean Lexer.lean Ast.lean Parser.lean
  Sema/Scope.lean Kinds.lean Check.lean          -- scopes, kinds, aggregates, params, write rules
  Value/Core.lean Order.lean Equality.lean Json.lean
  Value/Temporal.lean TzData.lean                -- TzData generated
  Value/Text.lean CaseData.lean Regex.lean       -- CaseData generated
  Lower/Names.lean Classify.lean Pattern.lean Path.lean Time.lean
  Exec/Row.lean Expr.lean Funcs.lean Project.lean Agg.lean Subquery.lean Union.lean Procs.lean
  Write/Plan.lean Create.lean Merge.lean Set.lean Delete.lean
  Api.lean                                        -- View.cypher, Tx.cypher, Db.cypherWrite
tests/Cypher/   unit and scenario tests (one per spec scenario)
tests/Tck/      Gherkin runner, vendored TCK 2024.3, expected-failures.txt
tests/Dialect/  cross-dialect corpus and fixtures
tools/gen/      tz and Unicode table generators
```

Cypher modules are not verified modules (verification Proof Policy applies only to Tiers 0–2), but the library-wide rules hold: no `sorry`, `admit` or user `axiom`; `partial` only where noted in code review, never in `Lower/`.

### 4. Key types

```lean
structure Span where start stop : Nat                     -- UTF-8 byte offsets
inductive CypherError
  | parse (span : Span) (msg : String)
  | unsupported (feature : String) (span : Option Span)
  | eval (msg : String)
  | core (e : Tiramemsu.Error)                            -- M2 errors: UniqueViolation, …
inductive CValue
  | null | bool (b : Bool) | int (i : Int64) | float (f : Float) | str (s : String)
  | date (day : Int) | dateTime (ms : Int) (offsetSec : Int) | localDateTime (ms : Int)
  | list (xs : Array CValue) | map (kvs : Array (String × CValue))
  | node (n : NodeVal) | rel (r : RelVal) | path (p : PathVal)
inductive Kind | node | rel | dual | path | value     -- dual = rel used in node position
structure TimeSel where tx : TxSel; valid : Option Instant   -- TxSel = now | asOf t | history
structure Program where ast : Query; names : NameTable; params : Params; writes : Bool
def compile (vocab : Vocab) (text : String) (params : Params) : Except CypherError Program
def runRead  [Store σ] (v : View σ) (p : Program) : Except CypherError Table
def runWrite [Store σ] (tx : Tx σ) (p : Program) : Except CypherError (Table × TxReport)
def lowerMatch (sc : Scope) (m : MatchClause) (sel : TimeSel) (flags : EdgeFlags) (input : Ir.Op) :
    Except CypherError Ir.Op
```

`Int64` arithmetic is checked (overflow is `eval`, as Rust's `checked_*`). `Float` is hardware arithmetic (trusted base); float-to-text uses the D11 shortest round-trip printer with Cypher formatting rules (`1.0`, `1.0E20`) reproduced from Rust.

### 5. Pattern lowering

- Names (labels, types, keys) resolve through the vocabulary at compile time, also under `USE AS OF`, as in Rust.
- Classification: a predicate is a relationship or a property from the object kind, overridden by `sys:isEdge` flags read once per distinct view in the query, before lowering of the clause that uses that view; `rdf:type` is label-only; untyped patterns exclude `sys:`.
- Label and property-map constraints lower to semi-joins (IR `exists`), so duplicates and episodes never multiply rows.
- A relationship variable is one IR eid variable; using it in node position reuses the same variable (dual view), so both forms bind the same eid without a join.
- Isomorphism: within one clause, pairwise `eid ≠ eid'` filters over fixed relationship positions; positions inside variable-length or shortest matches are checked against the path's relationship list on result rows, as in Rust. `REPEATABLE ELEMENTS` emits no filters; with a variable-length pattern it is `Unsupported`.
- Variable-length `*m..n` lowers to an IR path pattern in `TRAIL` mode over `sys:anyRelationship` or the type alternatives, inverted for `<-`, alternated for undirected, with `max_hops = n` or the open option `path_max_hops` (default 15). `shortestPath` / `allShortestPaths` lower to `ANY_SHORTEST` / `ALL_SHORTEST` with minimum 0 or 1. A recursive pattern with no bound endpoint is `Unsupported`; `PathLimitExceeded` surfaces unchanged.
- Each lowered tree carries the `TimeSel` of its scope; statement time properties read the IR virtual predicates (`tm:txAdded`, …) under that view.

### 6. Writes

`Write/Plan.lean` turns each write clause, per row, into M2 verb calls on the open transaction: `create` for `CREATE` relationships, `assert` (idempotent) for labels and node properties, `upsert` for unique-key `MERGE`, `supersede` with a patched object or valid bound for `SET` rules 6 and `validFrom`/`validTo`, `retract` (with cascade, kind `explicit`) for `REMOVE`/`DELETE`, cardinality replacement for `sys:one`. The `DeleteConnectedNode` check runs once before commit. Any error aborts the M2 transaction, which leaves no trace (M2 atomicity). Clauses see earlier writes because later reads go through the transaction's own view. `MERGE` match-or-create is atomic because there is one writer (D10).

### 7. Time clauses

`Lower/Time.lean` resolves each scope's `TimeSel` from the inherited one by per-selector override; `AS OF <datetime>` resolves to `t` through the M2 instant-to-transaction lookup inside the read's snapshot. Write queries reject a non-`Now` top-level selector before execution.

### 8. Regex, time zones, Unicode (not covered by D1–D15)

- `=~` uses a Lean Pike-VM regex engine (linear time) for the Rust `regex` crate syntax, anchored as `^(?:p)$`. `\p{…}` / `\P{…}` are `Unsupported`: deviation **DV-C2**. Alternative: binding PCRE or Rust `regex` (needs C, forbidden by D9); a backtracking engine (exponential, unlike Rust).
- Named zones use a generated offset-transition table from the IANA release that the pinned Rust build's `chrono-tz` embeds; `toLower`/`toUpper` use a generated full case-mapping table from the Unicode version of the pinned Rust toolchain. A CI check compares both versions with the Rust pin's `Cargo.lock` and toolchain file.

### 9. Proven requirements and theorem statements

None of the M5 requirements is proven (Tier 3). The specs therefore carry no machine-checked scenarios. Correctness rests on these existing theorems, used unchanged:

- M3: for every IR tree `q` and store state `S`, `eval S q = denote S q` for every join order (D13); the path engine returns exactly the rows of the path-mode denotation within the hop bound, or `PathLimitExceeded`.
- M2: every verb sequence never removes a statement row (never forget); `supersede` replays annotations; `retract` retracts exactly the dependents closure; an aborted transaction leaves the state unchanged; views are log replays.

### 10. Test strategy (for every requirement)

- Scenario tests: each spec scenario is one Lean test on `ModelStore` and on `SqliteStore` (doubles as a refinement check for the Cypher workload).
- Rust differential (cypher-conformance): canonical results, transaction reports, written rows and error kind + span start, on shared `.db` files; plus generated queries from a grammar-based generator over the fixtures, seeded and reproducible, with failing seeds kept as regression tests.
- TCK: the vendored openCypher TCK 2024.3 (same commit as Rust) runs end to end; `expected-failures.txt` starts as the Rust allowlist at the pin; an unexpected pass or failure fails CI; a difference from the Rust list must name a DV entry.
- Cross-dialect: the shared corpus (≥ 40 pairs plus divergence pairs) runs SPARQL (M4) and Cypher on the same Lean store; the same corpus runs on Rust as a sanity check.
- Comparison rules: floats bit-exact except transcendental function results (≤ 1 ulp, libm); nondeterministic functions (`rand`, `randomUUID`, no-argument `datetime()`, `timestamp()`, `*.realtime/statement/transaction`) compared by type only.

## Risks / Trade-offs

- [Parser acceptance differs from `open-cypher` on odd inputs] → TCK plus a parse-only differential over the TCK, corpus and generated queries comparing accept/reject and span start; any intended difference becomes a DV entry.
- [Regex dialect drift] → regex differential over the `regex` crate's own test patterns (excluding `\p`), DV-C2 for property classes.
- [tz / Unicode table drift from Rust] → generated tables, version check in CI.
- [Interpreter-side bugs escape proofs] → the interpreter never decides which graph rows match; a bug there shows as a value or ordering difference, which the differential and TCK catch.
- [Float text formatting differs from Rust] → reuse the D11 printer and fuzz `toString(float)` against Rust.
- [Rust spec and Rust code disagree, e.g. volatile values need both `Now` and unfiltered valid time in code, only `Now` in the Rust spec] → the pinned build is the oracle; the fresh spec states the code behaviour.
- [Large intermediate row sets in the interpreter] → report-only benchmarks (D14); rows stream between IR batches.

## Open Questions

- Whether the M3 IR exposes a relationship-isomorphism match mode, or lowering keeps emitting pairwise filters: either is invisible to the specs and tasks.
