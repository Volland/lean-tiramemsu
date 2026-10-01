## 1. Harness and oracle first

- [ ] 1.1 Add the Cypher mode to the M0 differential harness: run a query with parameters on the Lean and the pinned Rust build over one `.db` file and print canonical results (columns, rows, error kind, span start)
- [ ] 1.2 Implement the canonical value comparison of cypher-conformance "Comparison rules" (bit-exact floats, 1-ulp transcendental tolerance, type-only nondeterministic functions) with unit tests
- [ ] 1.3 Create the deviation registry file with DV-C1 and DV-C2 and the harness hook that accepts a mismatch only when an entry covers it and fails on stale entries
- [ ] 1.4 Vendor the openCypher TCK at the Rust pin's release and commit, and copy the Rust expected-failure list as `tests/Tck/expected-failures.txt`
- [ ] 1.5 Add the scenario-test runner that executes each test on both `ModelStore` and `SqliteStore` and compares results (cypher-conformance "Store-independent results")

- [ ] 1.6 Reconcile with M3a's staged IR deviations (`Unnest`, `RowNumber`, `Lookup`, null-safe join keys, volatile opt-in on patterns, `collect`): for each, either lower it through the tested value interpreter (design decision 1) or add it to `query-ir` as a MODIFIED delta in this change with its denotation and proof obligations; record the outcome in design.md

## 2. Generated tables

- [ ] 2.1 Write `tools/gen` for the IANA tz offset-transition table at the tzdata version of the Rust pin's `chrono-tz`; generate `Value/TzData.lean`
- [ ] 2.2 Reuse the Unicode case tables generated in M4 (task 6.3 of m4-sparql-frontend); extend the generator only if Cypher needs mappings M4 did not emit
- [ ] 2.3 Add the CI check that compares both versions with the Rust pin's `Cargo.lock` and toolchain file

## 3. Values

- [ ] 3.1 Define `CValue`, `NodeVal`, `RelVal`, `PathVal` and the JSON encoding of the Rust JSON bridge; round-trip tests against Rust JSON output
- [ ] 3.2 Implement checked `Int64` arithmetic, Float arithmetic and float-to-text through the D11 printer with Cypher formatting; fuzz `toString(float)` against Rust
- [ ] 3.3 Implement Cypher equality, three-valued comparison and the cross-type `ORDER BY` order; tests from cypher-read "WHERE and three-valued logic" and "Ordering, SKIP and LIMIT"
- [ ] 3.4 Implement Date, DateTime (instant + offset), LocalDateTime parsing, printing and named-zone resolution; tests for offsets, `[Europe/Kyiv]` and millisecond precision
- [ ] 3.5 Implement the literal ↔ `CValue` mapping of cypher-read "Result value model" and cypher-write "Value encoding on write", including 60-bit inline versus `xsd:integer`
- [ ] 3.6 Reuse M4's Pike-VM regex engine (m4-sparql-frontend task 6.3) and add only a Rust `regex` syntax front end with `^(?:p)$` anchoring and `Unsupported` for `\p`/`\P`; differential against the `regex` crate test patterns

## 4. Parser

- [ ] 4.1 Implement the lexer over UTF-8 byte offsets (escaped names, parameters, string escapes, numbers, comments)
- [ ] 4.2 Define the AST with spans, including `USE` time clauses, match modes, `CALL { }` bodies, shortest-path forms and variable-length quantifiers
- [ ] 4.3 Implement the recursive-descent parser for clauses and patterns and the Pratt expression parser, structurally terminating without `partial`
- [ ] 4.4 Recognise and name every construct of cypher-read "Unsupported constructs" and cypher-write "Unsupported write features"
- [ ] 4.5 Run the parse-only differential (accept/reject, error kind, span start) over the TCK queries, spec scenarios and corpus; fix or register every difference

## 5. Semantic analysis

- [ ] 5.1 Implement scopes for `WITH`, `CALL` imports, `UNION` branches and subquery shadowing, with `Parse` errors spanning the reference
- [ ] 5.2 Implement variable kinds including the dual-view rule (relationship variable allowed in node position, node variable never in relationship position)
- [ ] 5.3 Check aggregate placement, missing parameters, `UNION` columns, `USE` placement and selector conflicts, `SKIP`/`LIMIT` literals
- [ ] 5.4 Check write rules: write clause on a view handle, non-`Now` top-level `USE` in a write query, variable-length in `CREATE`/`MERGE`, `MERGE` type count, read-only time metadata
- [ ] 5.5 Resolve labels, types and keys through the compile-time vocabulary; the function registry with case-insensitive names; scenario tests of cypher-read "Compile-time errors with spans"

## 6. Pattern lowering to the M3 IR

- [ ] 6.1 Implement `sys:isEdge` flag reading per view and the property/relationship/label classification; tests of cypher-read "Property-graph projection of statements"
- [ ] 6.2 Lower node patterns, the unlabelled node scan exclusions, `` `@id` `` identity, labels and property maps as IR semi-joins; tests of "Node patterns and labels" and "Node identity"
- [ ] 6.3 Lower relationship patterns (directions, undirected with self-loop guard, type alternatives, untyped without `sys:`, property maps) with one eid variable per relationship
- [ ] 6.4 Lower relationship isomorphism and `REPEATABLE ELEMENTS` / `DIFFERENT RELATIONSHIPS` (IR match mode if M3 provides one, else pairwise eid filters)
- [ ] 6.5 Feed incoming rows into the IR as a `values` relation with a row-index column, and implement `OPTIONAL MATCH` and `EXISTS` on top
- [ ] 6.6 Lower dual-view node positions to the shared eid variable and statement ends to statement nodes; tests of cypher-dual-view read requirements
- [ ] 6.7 Lower variable-length patterns to `TRAIL` path patterns with anchoring check, hop cap and path binding, and isomorphism against path relationships on result rows; tests of "Variable-length relationships"
- [ ] 6.8 Lower `shortestPath` / `allShortestPaths` to `ANY_SHORTEST` / `ALL_SHORTEST` with the minimum-length and single-relationship checks; tests of "Shortest path patterns" and "Named paths"

## 7. Interpreter

- [ ] 7.1 Implement expression evaluation (literals, parameters, operators, string predicates, `=~`, indexing, slicing, map projection, `CASE`, list comprehension) with `Eval` errors
- [ ] 7.2 Implement the full function registry of cypher-read "Expressions and functions", entity functions on both dual-view forms, and temporal functions
- [ ] 7.3 Implement property access with multi-values in eid order, `keys`/`properties`, and volatile fallback under the now view only; tests of "Property access" and "Volatile values as virtual properties"
- [ ] 7.4 Implement `WITH`/`RETURN` projection, `DISTINCT`, `ORDER BY`/`SKIP`/`LIMIT`, `UNWIND`
- [ ] 7.5 Implement grouping and the aggregate set, including empty-input rows; tests of "Aggregation"
- [ ] 7.6 Implement `CALL` subqueries (uncorrelated and importing), `UNION`/`UNION ALL`, and `db.labels` / `db.relationshipTypes` / `db.propertyKeys`
- [ ] 7.7 Add `View.cypher`, the `cypher` CLI subcommand, and the read differential over all cypher-read and cypher-dual-view scenarios

## 8. Time clauses

- [ ] 8.1 Implement `TimeSel` resolution with per-selector override from handle and enclosing scopes, and instant-to-transaction lookup in the query snapshot
- [ ] 8.2 Apply each scope's view to patterns, property reads and label tests, including imported variables in `CALL` bodies
- [ ] 8.3 Implement statement time properties through the IR virtual predicates, their `tm:` CURIE forms, `tm:retractKind`, shadowing and `keys()` exclusion
- [ ] 8.4 Scenario tests and read differential for every cypher-temporal-clauses read requirement

## 9. Writes

- [ ] 9.1 Add `Tx.cypher` and `Db.cypherWrite`, running a query inside one M2 transaction and returning rows plus the report; abort on any error
- [ ] 9.2 Implement `CREATE` nodes, relationships, paths and `validFrom`/`validTo` through M2 `create`/`assert`
- [ ] 9.3 Implement the seven-rule `SET` ladder through `assert`, `supersede`, cardinality replacement and `retract`; tests of cypher-write "SET property"
- [ ] 9.4 Implement `SET +=`, `SET =`, labels, `REMOVE`, and valid-time `SET` with variable rebinding and `InvalidPatch`
- [ ] 9.5 Implement `DELETE` (relationship, statement node, node with end-of-query `DeleteConnectedNode` check) and `DETACH DELETE`
- [ ] 9.6 Implement `MERGE` by unique key (upsert) and by pattern, with `ON CREATE` / `ON MATCH`; concurrent-merge test on the writer
- [ ] 9.7 Map M2 schema and namespace errors to the query; write the dual-view layer writes; write differential over all cypher-write scenarios with table comparison

## 10. Conformance

- [ ] 10.1 Port the Gherkin runner and run the TCK end to end; reconcile the expected-failure list with Rust, registering every difference
- [ ] 10.2 Write the cross-dialect fixtures and the ≥ 40-pair corpus with the completeness check, plus the divergence pairs
- [ ] 10.3 Run the cross-dialect suite on the Lean store with the M4 SPARQL front end, and the same corpus on the Rust build as a sanity check
- [ ] 10.4 Build the grammar-based query generator (reads and writes), seed handling and regression capture; run it in CI with a fixed budget
- [ ] 10.5 Verify the proof library is untouched by M5: the axiom audit and theorem index still pass, and no `Tiramemsu/Cypher` module is imported by `TiramemsuProofs`
- [ ] 10.6 Add the Cypher workloads to the report-only benchmark run (D14)

## 11. Documentation and validation

- [ ] 11.1 Update `lat.md/` (architecture front ends, verification Tier 3 harnesses, roadmap M5 status, a Cypher section with DV-C1 and DV-C2) and add `@lat:` refs from the conformance tests
- [ ] 11.2 Run `lat check` and fix every reported link or ref
- [ ] 11.3 Run `openspec validate m5-cypher-frontend --strict` and fix until it passes
