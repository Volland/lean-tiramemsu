## Context

See proposal.md for motivation. After v1 the Lean build has:

- M1: the codec (ObjectId with origin bits, canonical literals, doubles as bits with the shortest round-trip printer, date-times with offsets) and the term dictionary.
- M2: the memory verbs (assert, retract with cascade, supersede, graph membership operations), transactions on the single writer, views (`Now | AsOf t | History` × `Unfiltered | At d`), predicate schema checks, and the theorems of tier 1.
- M3a: the logical IR (`TriplePattern` with eid variable, view and graph selector, `Join`, `LeftJoin`, `Filter`, `Union`, `Minus`/`Exists` via expressions, `Extend`, `Aggregate`, `Project`, `OrderLimit`, `PathPattern`, `Values`), its denotation, the evaluator proven equal to it, the path engine (`REACH` for SPARQL), virtual predicates, the provenance-annotated evaluator with its soundness theorem, and the Lean API and CLI.
- M3b: Leapfrog Triejoin and the planner, proven order-independent (D13).

The Rust front end (`crates/tm-sparql`) uses `spargebra` and lowers to the Rust IR, then generates SQL. In Lean there is no SPARQL parser to reuse and no SQL generation (D3), so M4 writes the parser and lowers straight to the M3 IR, which is then run by the proven evaluator. SPARQL lowering is proof tier 3: tested, not proven (D2). Runtime code imports Lean core and Std only (D7).

## Goals / Non-Goals

**Goals:**
- Same accepted language, same results, same errors (kind and `Unsupported` feature name) as the pinned Rust build for every request in the Rust SPARQL corpus, except entries of the deviation register.
- Every SPARQL query result is, by construction, the M3 evaluator applied to the lowered plan, so M3's theorems apply to what runs.
- Updates write only through M2 verbs inside one M2 transaction, so M2's theorems apply to what is written.
- A total parser: no `partial`, no `unsafe`, no panics on any input.

**Non-Goals:**
- A formal semantics of SPARQL 1.1 or a proof that lowering is correct (non-goal of the port; tier 3 is tested).
- SPARQL protocol (HTTP), federation, entailment regimes, `LOAD`, RDF/XML input, `DESCRIBE`.
- Making SPARQL faster than Rust; SPARQL benchmarks are report-only until M6 (D14).
- The cross-dialect SPARQL-versus-Cypher suite; it needs the Cypher front end and belongs to M5.

## Decisions

### 1. Hand-written lexer and recursive-descent parser in Lean, total by construction

`Tiramemsu/Sparql/Lex.lean` turns the text into an `Array Token` with byte spans (structural recursion on the remaining bytes; every step consumes at least one byte). `Tiramemsu/Sparql/Parse.lean` is a recursive-descent parser for the SPARQL 1.1 query and update grammar plus the SPARQL 1.2 triple-term, reifier and annotation productions. Recursion is on an explicit `fuel : Nat` initialised to `tokens.size + 1`; every recursive call into a nested production happens after consuming its opening token, so fuel never runs out on a finite text. Running out of fuel returns a `Parse` error, never a panic; a property test checks it is unreachable. Errors report the first token that cannot continue any production, as 1-based line, column (in characters) and byte offset, plus the expected token classes.

Alternatives: porting `spargebra`'s PEG grammar (its quirks are exactly what we do not want to copy); Lean's own `Parser`/syntax-category machinery (needs the elaborator environment at run time and gives poor positions); parser combinators with `partial` (violates the totality goal for no gain).

Consequence: where `spargebra` 0.4.7 deviates from the SPARQL grammar (grammar gaps, case-sensitive boolean keywords, right-associative `a - b - c`, a `FILTER` in a nested group inside `OPTIONAL` merged into the join condition, a triple term accepted in subject position), Lean follows the W3C grammar. These are registered deviations of class `parser-quirk` (decision 10). Error positions can differ from the `peg` furthest-failure heuristic, so the differential harness compares `Parse` errors by kind only, except for corpus entries that pin a position.

### 2. Three stages: syntax, algebra, IR; all checks before any read

`Syntax.lean` (AST with spans) → `Algebra.lean` (SPARQL 1.1 §18 translation: group graph patterns to `Join`/`LeftJoin`/`Filter`/`Union`/`Minus`/`Extend`/`Graph`/`Service`, in-scope variable sets, aggregate extraction, path translation of `/ | ^` to joins and unions) → `Lower/*.lean` (M3 IR). Static checks run on the algebra: `BIND` over an in-scope variable, undeclared prefixes, relative IRIs without `BASE`, time IRI grammar and placement, graph names, reifier rules, unsupported features and functions, provenance restrictions. `prepare : Env → String → Except Error Prepared` is pure, so a rejected request never touches a store.

Alternative: AST straight to IR (as `spargebra`'s algebra effectively is in Rust). Rejected because scoping, aggregate extraction and the dataset rules are easier to test and to compare against the W3C syntax suites on a separate algebra value.

### 3. Environment snapshot and the entry points

```lean
structure Env where
  baseView    : View          -- the view the text was submitted on
  vocab       : String        -- the database @vocab IRI (meaning of `v:`)
  prefixes    : List (String × String)  -- the database prefix table
  speculative : Bool
  nowMs       : Int           -- NOW() for the whole request

inductive Prepared | query (p : QueryPlan) | update (p : UpdatePlan)
inductive SparqlResult
  | solutions (s : Solutions) | boolean (b : Bool)
  | graph (ts : Array RdfTriple) | update (r : TxReport)
structure SparqlOptions where provenance : Bool := false
```

The shell builds `Env` from the view's own snapshot (vocabulary current at compile time, as in Rust). The Lean API gains `View.sparql` and `View.sparqlWith`; an update prepared on a current, non-speculative view runs on the writer. The CLI gains `tiramemsu sparql <db> <text|@file> [--provenance] [--format json|nt]`.

### 4. Lowering targets the M3 IR as is

- Triple patterns lower to `TriplePattern` with `graph_set = SetOfTriples`, `match_mode = Homomorphism`, `missing = Unbound`; an unbound eid uses the canonical-eid semantics of the IR (one match per distinct `(s, p, o)`).
- Blank nodes in patterns, reifiers and triple terms lower to hidden variables (a reserved name space that `SELECT *` and results never show).
- Constants are encoded with the M1 canonical encoding through a read-only dictionary lookup; an unknown constant lowers to an empty pattern, never an error.
- Recursive paths (`*`, `+`, `?`) lower to one `PathPattern` in `REACH` mode carrying the block's view and graph selector; `/`, `|`, `^` lower to joins and unions. Negated property sets are `Unsupported("negated property sets")`; a recursive path with no endpoint bound by a constant or a joined pattern is the path engine's `Unsupported`, with Rust's feature text.
- `GRAPH`, `FROM`, `FROM NAMED`, `WITH`, `USING` lower to the IR graph selector (`none | const g | var ?g | anyOf gs`) on triple and path patterns, which M3a lowers to `(e sys:inGraph g)` under the pattern's own view.
- `tm:` statement-time predicates and `sys:subject|object|predicate` lower to the IR's virtual predicates.
- Expressions lower to IR `Expr`; SPARQL functions map to entries of the IR scalar-function table. M4 adds missing entries (regex, Unicode case mapping, `ENCODE_FOR_URI`, date accessors) as total Lean functions; the M3a evaluator theorems are stated over the function table, so new entries need no new proof.

Alternative: a SPARQL-specific evaluator for awkward constructs. Rejected: anything outside the IR would not be covered by M3's theorems.

### 5. Time scopes resolve to IR views at plan time

`Dataset.lean` parses time IRIs (`asOf/<t>`, `asOf/<date or dateTime>`, `validAt/<…>`, `history`) and folds `FROM`/`USING` and nested `SERVICE` scopes innermost-first into a `View` per pattern, each part (transaction time, valid time) replaced independently. `asOf/<instant>` is resolved to a transaction number by a read of the `tx` table in the same snapshot the query runs on (M2's instant lookup), between `prepare` and execution. Rust resolves it inside the SQL statement; both read one snapshot, so results agree.

### 6. Results are written in Lean, byte-identical to Rust

`Results/Term.lean` renders values as RDF terms (skolem IRIs, canonical lexical forms, date-times in their stored offset, lower-cased language tags). `Results/Json.lean` writes SPARQL 1.1 JSON with Rust's member order and escaping (compact, `"provenance"` between `head` and `results`); `Results/NTriples.lean` writes N-Triples, RDF 1.2 N-Triples when a triple term occurs. The target is byte-identity with Rust for the same rows in the same order, so the M6 bridge can switch backends without wrapper changes.

### 7. Provenance reuses the M3a provenance evaluator

`Provenance.lean` asks the lowering to keep every stored triple pattern's eid (hidden `~prov<N>` variables, reifier variables reused, eids leaving subqueries aliased), runs the M3a provenance evaluator, then: (a) expands each canonical eid to all visible eids with the same `(s, p, o)` in that pattern's view (sibling lookup through the `Store` scans of the same snapshot); (b) merges `DISTINCT` rows into the first one, unioning provenance, before `OFFSET`/`LIMIT`; (c) unions group provenance in aggregates. Virtual predicates, `FILTER EXISTS`/`NOT EXISTS`/`MINUS` and recursive paths contribute nothing, as in Rust.

### 8. Updates are plans of M2 verbs

`Update/Plan.lean` checks the request (unsupported operations named before anything else, reifier rules, graph names, `sys:`/`tm:` reservations) and builds `List UpdateOp`. `Update/Run.lean` runs the operations in order inside one M2 transaction: `WHERE` is evaluated by the M3 evaluator over the transaction's current state (so later operations see earlier ones), templates are instantiated (fresh blank nodes per solution, skipped triples for unbound or ill-positioned terms), deletes become `retract` (all live eids of the content, or exactly the bound eid), inserts become idempotent `assert`, `GRAPH` blocks become membership `addToGraph`/`removeFromGraph`, and graph management becomes the M2 graph operations. There is no other write path, so no SPARQL request can delete a row.

### 9. Theorems (proven requirements only)

Proofs live in `TiramemsuProofs/Sparql/` and instantiate M2/M3 theorems; nothing about lowering is proven.

| Requirement (capability) | Statement |
|---|---|
| Execution through the proven evaluator (`sparql-query`) | For every prepared query, running it on a `ModelStore` equals the IR denotation of its plan, post-processed by the query form; hence independent of join order and planner choice. |
| Query provenance option, soundness clause (`sparql-query`) | Every eid in a row's provenance is a statement visible in the view of some stored triple pattern of the plan, and has the content that pattern matched in some solution that projects to the row. |
| Updates never delete rows (`sparql-update`) | A successful update request changes the store only by appending rows and setting `t_ret` once on live rows. |
| INSERT DATA asserts idempotently (`sparql-update`) | Running a ground, blank-node-free `INSERT DATA` twice in a row adds no statement row the second time. |
| DELETE DATA retracts with cascade (`sparql-update`) | The eids retracted by a `DELETE DATA` of live content equal the M2 dependents closure of its live eids. |

Lean-ish signatures:

```lean
theorem sparql_run_eq_denote {env text plan} (h : prepare env text = .ok (.query plan))
    (st : ModelStore) :
    runQuery st plan = finish plan.form (Ir.denote st (resolveTimes st plan).ir)

theorem sparql_provenance_sound {env text plan} (h : prepare env text = .ok (.query plan))
    (hp : plan.provenance = true) (st : ModelStore) :
    ∀ row ∈ (runSelectProv st plan).rows, ∀ e ∈ row.prov,
      ∃ tp ∈ plan.storedPatterns, Visible st tp.view e ∧
        ∃ μ ∈ Ir.denote st plan.preProjection, μ ⊒ row.bindings ∧ Matches st tp μ e

theorem sparql_update_never_forget {req st st' rep} (h : runUpdate st req = .ok (st', rep)) :
    NeverForget st st'           -- M2's relation: rows ⊆, only t_ret set once

theorem sparql_insert_data_idem {ts st st₁ st₂ r₁ r₂} (hg : Ground ts) (hb : NoBlank ts)
    (h₁ : runUpdate st (.insertData ts) = .ok (st₁, r₁))
    (h₂ : runUpdate st₁ (.insertData ts) = .ok (st₂, r₂)) :
    st₂.statements = st₁.statements ∧ r₂.asserted = []

theorem sparql_delete_data_cascade {ts st st' rep} (h : runUpdate st (.deleteData ts) = .ok (st', rep)) :
    rep.retracted.toFinset = Dependents.closure st (liveEids st ts)
```

`runQuery` and `runUpdate` are the same definitions the API calls with `SqliteStore`; the theorems are over `ModelStore`, and `SqliteStore` is linked by the M0 refinement tests (tier 4). The theorem index maps each requirement above to its theorem name; CI fails if one is missing.

### 10. Conformance: Rust oracle first, W3C second, one deviation register

- **Rust oracle:** a small `tm-oracle` binary built from the pinned Rust commit (M0) reads a script (fixture operations with a deterministic clock, then requests) and prints canonical JSON results. Fixtures are written by Rust into a `.db`, compared table by table with the same fixture written by Lean, then both builds run every request on copies of the Rust-written file (and a sample on the Lean-written file, so either reads the other's files).
- **Corpus:** the Rust `tm-sparql` golden files (`.rq`, `.ru`, `.ttl`, `.srj`, `.nt`, `.err`; the `.ir` snapshots are not used), every SPARQL scenario of the Rust facade tests (`sparql_*.rs`, `recipes.rs`), the recipes of `lat.md/recipes.md`, and every scenario in these specs.
- **Generated queries:** a deterministic grammar-based generator in the test tree (no extra dependency) produces queries over the fixture vocabulary; both builds run them; failing seeds are kept as regression cases.
- **Comparison:** SELECT rows as multisets of canonical terms, ordered on the sort keys when `ORDER BY` is present; `ASK` by boolean; `CONSTRUCT` up to blank-node isomorphism; JSON documents byte-compared when the order is fixed; updates by the resulting `triple`, `tx` and `term` tables; errors by kind and `Unsupported` feature; provenance as a set per row.
- **W3C:** the W3C `rdf-tests` SPARQL data pinned by commit, the same in-scope categories as the pinned Rust runner. Inputs that need a Turtle or results-format parser are converted once, by a converter built from the pinned Rust oracle crate, into N-Triples and canonical results JSON, committed with source hashes; the Lean runner reads only those. `expected-failures.toml` starts as a copy of Rust's `expected-deviations.toml`, each entry tagged with a class; entries of class `parser-quirk` or `rust-executor-limit` are removed once Lean passes them and move to the deviation register.
- **Deviation register:** `test/conformance/deviations.toml`, entries `{id, against = rust|w3c|both, class, description, tests}`. Classes: `design` (shared with Rust: canonical literal collapse, relative IRIs rejected, default graph is the union, membership-only graph deletes, every reifier is a stored statement, unsupported functions), `value-semantics` (shared with Rust, owned by IR function semantics: decimal arithmetic as `xsd:double`, string functions drop language tags, `AVG` of an empty group unbound, `xsd:date` drops its timezone), `parser-quirk` and `rust-executor-limit` (Lean follows SPARQL; Rust does not: e.g. `COUNT(DISTINCT *)`, `GROUP_CONCAT(DISTINCT …; SEPARATOR …)`, expressions mixing stored and computed values, aggregate errors on non-numeric input, the exact `MINUS` domain rule), and `error-detail` (parse positions and messages). Both harnesses fail on any difference that no entry covers, and on any entry that no longer matches a difference.

Rule for `Unsupported`: every `Unsupported` that a Rust **spec** names is kept with the same feature text (contract, D6); Rust `Unsupported` results that are only listed in its W3C deviation file as executor limits are not kept.

### 11. Regex and Unicode tables in Lean

Std has neither a regex engine nor full Unicode case mapping. M4 adds a total Pike-VM regex (linear time, no backreferences) for the XPath syntax and flags `i`, `s`, `m`, `x`, matching what the Rust `regex` crate accepts; patterns Rust rejects give the same error result. `UCASE`/`LCASE` use case tables generated from the Unicode version of the pinned Rust toolchain and committed as Lean data. Both are differential-tested on generated strings.

Alternative: FFI to a C regex library. Rejected: hand-written C beyond the ABI shim is out (D1, D9).

## Risks / Trade-offs

- [M3a IR lacks a construct SPARQL needs (graph selector on paths, a virtual predicate, an aggregate form, a scalar function)] → task 1 audits the IR against the Rust IR feature list before parsing work starts; gaps are added to the IR with their denotation, in M3a style, so the M3 theorems keep covering execution.
- [A fresh parser accepts or rejects different texts than `spargebra`] → the W3C syntax suites, the whole Rust corpus and generated queries run through both parsers; every acceptance difference must be a registered `parser-quirk` entry.
- [Byte-identical JSON drifts (number forms, escaping, member order)] → the JSON writer is compared byte-for-byte on every ordered corpus query; doubles use the M1 printer, already fuzzed against Rust (D11).
- [Regex and Unicode semantics drift from Rust] → pinned Unicode version, differential tests on generated patterns and strings; any residual difference is a registered entry.
- [Executing everything in Lean is slower than Rust's SQL for some SPARQL shapes] → report-only benchmarks (D14); the M6 gate decides the switch.
- [Following SPARQL where Rust had executor limits changes some answers] → each case is a registered `rust-executor-limit` entry naming its tests, so bridge users can see exactly where results differ.
- [The W3C converter depends on the pinned Rust crate] → it only converts data and expected results, never runs queries; the converted files are committed with source hashes and checked in CI.
