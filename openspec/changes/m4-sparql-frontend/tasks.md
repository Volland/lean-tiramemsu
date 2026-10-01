## 1. Prerequisites and IR audit

- [ ] 1.1 Audit the M3a IR against the Rust IR feature list used by `tm-sparql` (graph selector on triple and path patterns, canonical-eid semantics, virtual predicates incl. `tm:addedAt`/`tm:retractedAt`, aggregate forms, scalar-function table, provenance hooks); record gaps in a checklist file under `test/conformance/`
- [ ] 1.2 Close each IR gap in M3a style (definition, denotation, evaluator case) and re-run the M3 proof build; done when the checklist is empty and `lake build TiramemsuProofs` passes the proof-policy gate
- [ ] 1.3 Create the module skeleton `Tiramemsu/Sparql/{Lex,Syntax,Parse,Algebra,Check,Env,Dataset,Lower/*,Construct,Provenance,Results/*,Update/*,Api}.lean` and `TiramemsuProofs/Sparql/`; CI checks the runtime modules import only core and Std

## 2. Conformance infrastructure

- [ ] 2.1 Build `tm-oracle` from the pinned Rust commit: reads a script (fixture verbs with a deterministic clock, `NOW()` instant, requests) and prints canonical JSON results, reports and errors; CI fails if the commit differs from the pin
- [ ] 2.2 Write the Lean counterpart `tiramemsu-conform` reading the same script format
- [ ] 2.3 Implement canonical comparison: multiset rows, sort-key order, CONSTRUCT blank-node isomorphism, byte-compare of ordered JSON, table-level store comparison, error kind and feature comparison, provenance sets
- [ ] 2.4 Create `test/conformance/deviations.toml` with the five classes and the entries already known from the design (parser quirks, executor limits, error detail, shared design and value-semantics entries); the harness fails on uncovered differences and stale entries
- [ ] 2.5 Import the corpus: Rust golden `.rq`/`.ru`/`.ttl`/`.srj`/`.nt`/`.err`, SPARQL scenarios of the Rust facade tests and recipes, and one script per scenario of the four behavior specs; add the corpus-completeness check
- [ ] 2.6 Fixture parity test: every fixture written by Rust and by Lean gives identical `triple`, `tx` and `term` tables

## 3. Lexer and parser

- [ ] 3.1 Lexer with byte spans, all SPARQL 1.1 and 1.2 tokens, case-insensitive keywords, string escapes and numeric literal forms, by structural recursion (no `partial`)
- [ ] 3.2 Syntax AST with spans for queries, updates, prologue, triple terms, reifiers and annotation blocks
- [ ] 3.3 Recursive-descent parser for the full query grammar with explicit fuel; left-associative operators; parse errors with line, column, byte offset and expected classes
- [ ] 3.4 Update grammar: `INSERT DATA`, `DELETE DATA`, `DELETE/INSERT … WHERE`, `DELETE WHERE`, `WITH`, `USING`, graph management and the unsupported operations recognised by keyword
- [ ] 3.5 Prologue: `BASE` resolution (RFC 3986), `PREFIX` overrides, predeclared prefixes from `Env`, undeclared-prefix and relative-IRI errors
- [ ] 3.6 Parser tests: W3C positive and negative syntax categories, parse-position cases, print-then-parse round trip on the corpus, and a random-input termination test (one million inputs, no crash, no fuel exhaustion)

## 4. Algebra and static checks

- [ ] 4.1 Translate syntax to the SPARQL algebra: group patterns, `OPTIONAL` with its filters as join condition, nested-group filter scoping, `MINUS`, `EXISTS`, `BIND`, `VALUES`, subqueries, aggregate extraction, `/ | ^` path translation
- [ ] 4.2 In-scope variable analysis: `SELECT *` order, hidden variables, `BIND` over in-scope variable as `Parse` error
- [ ] 4.3 Unsupported-feature checker with the Rust feature texts (DESCRIBE, SERVICE, functions, custom aggregates, negated property sets, triple functions, triple term in VALUES, ORDER BY with DISTINCT, provenance combinations); test each text against the oracle
- [ ] 4.4 Graph-name checks (`InvalidGraphName`, `tm:` IRI in `GRAPH` as `Parse` naming `SERVICE`, `GRAPH ?g` over subquery or empty block)

## 5. Temporal dataset

- [ ] 5.1 Time IRI parser (`asOf/<t>`, `asOf/<date|dateTime>`, `validAt/…`, `history`) with the `Parse` error naming the IRI
- [ ] 5.2 Scope folding: `FROM`/`USING` defaults per part, conflict detection, `FROM NAMED` time IRIs ignored, nested `SERVICE` innermost-first, `SILENT` kept transparent
- [ ] 5.3 Resolve `asOf/<instant>` to a transaction through the M2 instant lookup in the request snapshot
- [ ] 5.4 Tests: every `sparql-temporal-dataset` scenario on both builds

## 6. Lowering to the IR

- [ ] 6.1 Triple patterns and BGPs: canonical-eid semantics, homomorphism, constants through the dictionary (unknown constant gives an empty pattern), blank nodes as hidden variables, skolem IRIs to ids
- [ ] 6.2 Graph pattern operators and subqueries to `Join`, `LeftJoin`, `Filter`, `Union`, `Minus`/`Exists`, `Extend`, `Values`, `Project`
- [ ] 6.3 Expressions to IR `Expr`; map every supported function to the scalar-function table; add missing total functions (Pike-VM regex engine with a syntax-independent core shared with M5 and an XPath-flags front end, Unicode case tables generated from the pinned Rust toolchain's Unicode version, `ENCODE_FOR_URI`, date accessors, casts)
- [ ] 6.4 Differential tests for regex and case mapping on generated patterns and strings
- [ ] 6.5 Aggregates, `GROUP BY` expressions, `HAVING`, `COUNT(DISTINCT *)`, `GROUP_CONCAT` separators; solution modifiers and value ordering
- [ ] 6.6 Property paths: recursive paths to `PathPattern` (`REACH`) with view and graph selector, virtual hops, Rust's unbound-endpoint `Unsupported`
- [ ] 6.7 Named graphs: `GRAPH <g>`, `GRAPH ?g`, `FROM`, `FROM NAMED` to the IR graph selector; layer patterns inside `GRAPH` use the block's selector
- [ ] 6.8 RDF 1.2: reifiers, `rdf:reifies`, triple terms, nested annotation blocks to triple patterns over eids; `rdf:reifies` never a stored predicate
- [ ] 6.9 Statement-time virtual predicates to the IR virtual predicates
- [ ] 6.10 Tests: golden corpus queries pass against the oracle for each group above

## 7. Results

- [ ] 7.1 Term rendering: skolem IRIs, canonical literals via the M1 printers, date-times in stored offset, lower-cased language tags
- [ ] 7.2 SPARQL JSON writer byte-identical to Rust (member order, escaping, `"provenance"` placement); byte-compare on every ordered corpus query
- [ ] 7.3 CONSTRUCT instantiation (skips, fresh blank nodes, set in first-occurrence order, RDF 1.2 reification triples) and the N-Triples / RDF 1.2 N-Triples writer

## 8. Query execution and its theorem

- [ ] 8.1 `prepare` (pure) and `runQuery` over the `Store` interface: resolve times, run the M3 evaluator, finish by query form; `View.sparql`, `View.sparqlWith`, CLI `sparql` subcommand
- [ ] 8.2 Prove that running a prepared query on `ModelStore` equals the IR denotation of its plan post-processed by its form, by instantiating the M3 evaluator theorem; add it to the theorem index
- [ ] 8.3 Tests: every `sparql-query` scenario, join-order permutation test, and a no-scan check for rejected requests

## 9. Query provenance and its theorem

- [ ] 9.1 Provenance instrumentation in lowering (hidden eid variables, reifier reuse, subquery aliasing) and the restrictions (`ASK`, `CONSTRUCT`, updates, empty `DISTINCT` subquery)
- [ ] 9.2 Post-processing: sibling-eid expansion per pattern view, `DISTINCT` merge before `OFFSET`/`LIMIT`, group and subquery unions, membership eids under `GRAPH` and single `FROM`
- [ ] 9.3 Prove provenance soundness for SPARQL from the M3a soundness theorem plus lemmas that sibling expansion and unions preserve it; add it to the theorem index
- [ ] 9.4 Tests: provenance scenarios and "rows unchanged with provenance" over the whole SELECT corpus on both builds

## 10. Updates and their theorems

- [ ] 10.1 Update planning: operation list, unsupported operations named before any other check, reifier restrictions, reserved predicates, non-current view rejection
- [ ] 10.2 Update runner inside one M2 transaction: `WHERE` on the in-transaction state, template instantiation, retract (all live eids or the bound eid), idempotent assert, membership add/remove, graph management, report with memberships apart
- [ ] 10.3 Prove that a successful update only appends rows and sets retractions once, from M2's never-forget theorem; add it to the theorem index
- [ ] 10.4 Prove ground blank-node-free `INSERT DATA` idempotence from M2's idempotent-assert theorem; add it to the theorem index
- [ ] 10.5 Prove that `DELETE DATA` retracts exactly the dependents closure of its live eids from M2's cascade theorem; add it to the theorem index
- [ ] 10.6 Tests: every `sparql-update` and `sparql-rdf12-annotations` update scenario, rollback on failure (no tx row, no terms), and table-level comparison with the oracle

## 11. W3C suite

- [ ] 11.1 Pin the W3C `rdf-tests` commit; build the converter from the pinned Rust oracle crate and commit converted N-Triples and canonical results JSON with source hashes; CI verifies the hashes
- [ ] 11.2 Lean W3C runner for the Rust in-scope categories, with the Rust value-based comparison rules and blank-node isomorphism
- [ ] 11.3 Create `expected-failures.toml` from Rust's list with a class per entry; remove `parser-quirk` and `rust-executor-limit` entries the Lean build passes and record each in the deviation register
- [ ] 11.4 Runner fails on unlisted failures and on listed passes

## 12. Generated-query differential

- [ ] 12.1 Deterministic grammar-based generator over fixture vocabularies covering every supported construct
- [ ] 12.2 CI run of at least 10 000 generated requests on both builds with the seed recorded; failing seeds stored as regression cases

## 13. CI, documentation and validation

- [ ] 13.1 CI jobs for the differential harness, the generated run and the W3C runner, triggered by changes to the front end, IR, evaluator or store; SPARQL benchmarks report-only
- [ ] 13.2 Update `lat.md/` (architecture: SPARQL front end modules; verification: tier 3 test strategy, inherited theorems and the deviation register; roadmap: M4 status) with links to the new sections
- [ ] 13.3 Run `lat check` and fix every reported link or section error
- [ ] 13.4 Run `openspec validate m4-sparql-frontend --strict` and fix until it passes
