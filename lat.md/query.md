# Query

The M3a query core: the logical IR, its executable reference semantics, the index nested-loop evaluator, the path engine, provenance, fact bundles and the Lean API. See [[decisions#D13 Hybrid Joins Proven Order-Independent]].

## Logical IR

The algebra every front end produces (`Tiramemsu.IR`): view-scoped triple and path patterns, inline values, Join, LeftJoin, Union, Filter, Extend, Aggregate, Project and OrderLimit.

Expressions carry `EXISTS` subtrees, so `Expr` and `Op` are one mutual inductive. A query is an operator tree plus three semantic flags (match mode, missing values, graph set) with SPARQL and Cypher presets. Cypher-only operators (`Unnest`, `RowNumber`, `Lookup`, null-safe join keys, volatile patterns) arrive with M5.

### Scope

Per operator, the variables it exposes in order of first binding and those that may be missing (Rust `scope`); certain variables are exposed and never missing.

The result columns are the root `Project`'s variables, otherwise every exposed variable in order of first binding. The variable table of a query (every variable of the tree, `EXISTS` subtrees included) fixes the positions of the semantics' rows.

### Validation

`validate` applies one local rule per node (`checkOp`, `checkExpr`) to the whole tree before any read and reports the first problem as `InvalidQuery`; `bindParams` replaces parameters.

Rules: an `Extend` rebinding a variable its input binds, colliding aggregate outputs, a non-`COUNT` aggregate without argument, ragged values rows, variables in values cells, repeated values variables, a negative or non-integer skip or limit, a virtual-predicate pattern binding an eid or selected by graph, an empty graph set or one holding a variable, a projected variable the input cannot bind, and a function applied to the wrong number of arguments. The last two are Lean additions (Rust accepts them).

The reference semantics runs the same local rule at each node it evaluates, so validation soundness is a theorem about two definitions.

## Reference Semantics

`denote` (`Tiramemsu.Sem.Denote`) is the meaning of a query: a total, computable function from a model store state to a bag of rows, used as specification and as test oracle.

Patterns compare decoded values, so the reference semantics never looks up the dictionary: a constant that is not stored matches nothing by construction.

### Values And Order

The Rust class ranks and memcmp sort keys (`value_key`) order values; an injective total key breaks ties, so the canonical value and row orders are linear.

Ordering comparisons need equal class ranks and compare sort keys; equality compares numbers by value, date-times by instant and other typed literals by identity. Integer and decimal `+ - *` are exact; `/` and every double operation use hardware binary64 (trusted base), as the Rust build divides in REAL.

### Rows And Bags

A row is positional over the variable table (`List (Option Value)`), so merge and compatibility are pointwise; a bag is a list read up to permutation.

Under `Null3VL` compatibility depends on the inputs' schemas (their possible variables): a variable both can bind joins only when both rows bind it to equal values. The n-ary join is a left fold of the binary bag join from the unit relation.

### Expressions

An expression is resolved against the variable table (positions for variables, bags for `EXISTS`) and evaluated on a row to a value or an error, with Kleene `AND`/`OR`/`NOT`.

`EXISTS q` holds when the bag of `q` has a row that agrees with the current row on every variable both bind. `REGEX` and `REPLACE` are `Unsupported` until the SPARQL front end (M4).

### Operators

The bag operators shared by `denote` and the evaluator: filter, extend, left join, projection, aggregation, ordering and the relationship-isomorphism filter.

Aggregates fold in the canonical value order, so each is a function of its group's multiset; `OrderLimit` sorts by its keys (missing smallest under `Unbound`, largest under `Null3VL`, as Rust places NULLs) with ties broken by the canonical row order.

## Index Nested-Loop Join

Joins of triple patterns are evaluated as index nested loops in a planner-chosen order, scanning each pattern once per partial row with its bound positions as the key prefix; every order computes the reference join.

### Explain

`Tiramemsu.Exec.Explain` describes the plan from the query alone: per join the greedy order, per pattern the index or eid lookup, key prefix, family and pushed conjuncts; per path its mode, automaton size and direction.

### Sorted Range Scans

The evaluator reads statements only through the store's range scans: an index order, a view and a key prefix give the visible statements in ascending key order, plus seeks and lookup by eid.

## Paths

The path engine (`Tiramemsu.Path`) evaluates regular path expressions over stored and virtual layer hops in one view, in four modes, optionally graph-scoped and time-respecting.

### Path Text

SPARQL 1.1 property-path syntax plus `{m,n}`, parsed to raw atoms with byte offsets; atoms resolve through the database vocabulary only when the text needs it.

A negated property set is `Unsupported` (Rust reports a parse error, a listed deviation). Errors are `Parse` of dialect `Path` with the byte offset of the problem.

### Automaton

An expression resolves to a regular expression over letter classes (inverse pushed to atoms, repetition unrolled) and compiles to a DFA by Brzozowski derivatives with normalized states.

The alphabet is refined as in Rust: a stored predicate mentioned in a direction where the wildcard also occurs splits into its relationship and non-relationship letters, and the wildcard's other letter excludes mentioned predicates. More than 4 096 states is `Unsupported("path expression too complex")`.

States are interned in a hash map keyed by the expression itself, so a transition always targets a state equal to the derivative. The proofs (`TiramemsuProofs/Path/`) define the declarative language of a path expression (`^e` reads `e`'s words reversed with directions flipped), show `toRE` has exactly those words, that every symbol agrees on a letter and its refined class, that derivatives are left quotients, and that the built automaton accepts exactly the expression's words with a unique run.

### Hops

Neighbours of a node for one letter class are read through the sorted range scans of the path's view; virtual hops step between a statement and its parts.

The wildcard follows a statement when its predicate is not `rdf:type`, not a `sys:` IRI and not flagged `sys:isEdge false`, and either is flagged `sys:isEdge true` or has an IRI, node, blank node, statement or transaction object (Rust's relationship view).

### Search

Breadth-first search over `(node, DFA state)` layers with explicit fuel; every new search state is charged to the `pathMaxStates` budget, so the fuel `pathMaxStates + 1` layers suffices and exceeding the budget fails with `PathLimitExceeded`.

REACH emits each end once with its minimal hop count; TRAIL keeps an arena of partial trails and refuses a repeated hop identity; the shortest modes keep layered predecessors. Rows come in non-decreasing hops, then by hop key (eid, kind, direction).

Each layer is a fold of a named step (`trailStep`, `reachTimedStep`, `shortestStep`, `anyStep`) over the layer's transitions, and the class neighbours are `fetchRaw` filtered by the graph scope, so the proofs of [[query#Paths#Path Specification]] can state one invariant per step.

### Path Specification

The proofs state path results against a declarative specification (`TiramemsuProofs/Path/Spec`) written without automata or search: `lang e`, walks over a hop relation, and the hops of a store view.

`lang e` is the set of hop-letter words of an expression; `IsWalk R x w y` is a walk of a hop relation `R` (each step a letter and the neighbour reached); `ViewHop` is the hop relation of a store view (stored hops both ways over visible statements, virtual hops between a statement and its parts); trails, graph scoping (`HopRel.scoped`), hop-rule threading (`walkTau`) and reversal are defined on walks.

The search theorems assume `HopsExact`: the hop layer of a search lists exactly the hops of `R`, routed by the automaton's transition function (and `HopsNodup`, each hop once, for path-returning modes). That `fetchClass` over the sorted range scans lists exactly `ViewHop` is not yet proven.

### Path Patterns

A path pattern runs laterally inside its join: from the start when the outer row or a constant binds it, else from the end with the inverse expression (rows reversed), else `Unsupported`.

The reference semantics and the evaluator share one engine (`Tiramemsu.Path.Engine`): the reference semantics runs it on the model state, the evaluator as a read program. A `Var(?g)` selector evaluates once per graph with a visible membership; a bound path binds its self-describing JSON text (Rust's decoded `path_json`). Without a hop bound, `TRAIL` uses `pathMaxHops` (15), as Rust's `tm_path`.

## Provenance

On request, every result row carries the ascending, duplicate-free eids of the stored statements that support it (`Tiramemsu.Prov`); without it nothing changes.

The provenance evaluator computes its rows with the plain bag operators and threads citations beside them: a match cites its statement (under `SetOfTriples` every visible eid of the matched content), joins and left joins unite, unions keep the branch's, filters and `EXISTS` add nothing, paths in `TRAIL` and the shortest modes cite their hops, a distinct projection and an aggregate unite their merged rows' citations.

## Fact Bundles

A bundle moves a belief with its layers and evidence between databases (`Tiramemsu.Bundle`): exported from any view as a read program, imported as a transaction-body program.

Export collects the root's dependents plus the downward closure of their statement references, excludes transaction-referencing statements, reserved predicates (`sys:inGraph` excepted) and references to invisible statements (propagated), then orders by references with ties by eid and labels anonymous nodes by first appearance. Import checks structure and cycles before writing, then asserts in order (memberships through `addToGraph`), minting one fresh node per label.

### Bundle JSON

The JSON form `tiramemsu-bundle/1` is written as Rust's `serde_json` writes it: compact, object keys sorted (`Tiramemsu.Shell.BundleJson`, unverified, tested by round trips and byte comparison).

## Lean API

`Tiramemsu.Api` mirrors the Rust facade: `Db.open` with `OpenOptions`, `transact`, speculative `with`, views (`now`, `asOf`, `history`, `validAt`) and their reads, `execute`, `path`, `pathWith`, `bundle`, `importBundle` and `explain`.

Execution validates and binds parameters before any read, then evaluates in one snapshot of a pooled reader; a speculative query runs the evaluator on the writer inside the speculation's savepoint. Errors carry Rust's variant names. Listed deviations: explain returns the Lean plan, there is no `tm_path` table function, SQL UDFs or host abstraction, double `SUM`/`AVG` fold canonically, the path state count is Lean's own, and N-Triples bundles, SPARQL and Cypher arrive later.

## Command-Line Tool

`tiramemsu <db> <command>` (`Tiramemsu.Cli`) runs the API: `info`, `assert`, `retract`, `triples`, `values`, `dependents`, `path`, `bundle` and `import-bundle`, one JSON value per line.

Read commands take `--as-of`, `--history` and `--valid-at`; terms are `<iri>`, CURIEs over the database prefixes, quoted literals, numbers, booleans and skolem ids. An error prints `{"kind", "message"}` on standard error with exit status 1, a usage error exits with 2; each write command is one transaction.

## Differential Query Oracle

`oracle query` (`tools/Oracle/Query.lean`) compares the query core with the pinned Rust build on Rust-written files: the drivers' `m3.*` operations execute IR given as JSON (`Tiramemsu.Shell.IrJson`), paths, bundles and sort keys.

Both builds read the same file. Results compare canonically (bags unless the root orders), path rows in order, bundles by their JSON bytes and sort keys byte for byte; accepted differences go through `oracle/deviations.toml`.
