## Purpose

The path engine shared by path patterns in the IR and the API: regular path expressions over stored and virtual layer hops, evaluated by a bounded search whose results are proven equal to a declarative regular-path specification, in four modes, under views, graph scopes and time-respecting order.

## ADDED Requirements

### Requirement: Path expression language
A path expression SHALL be built from atoms, inverse (`^`), sequence (`/`), alternation (`|`), zero-or-more (`*`), one-or-more (`+`), zero-or-one (`?`) and bounded repetition `{m,n}`, `{m,}`, `{n}`. Atoms SHALL be a stored predicate IRI, the virtual hops `sys:subject`, `sys:object` and `sys:predicate`, or the wildcard `sys:anyRelationship`. The meaning of an expression SHALL be a regular language over hop letters (a hop class and a direction), defined directly by the operators. A walk SHALL match when its letter word is in the language.

#### Scenario: Sequence and alternation
- **WHEN** `knows/(worksAt|livesIn)` is evaluated from `alice`, who knows `bob`, who works at `acme` and lives in `paris`
- **THEN** the ends are `acme` and `paris`

#### Scenario: Bounded repetition
- **WHEN** `knows{2,3}` is evaluated over the chain `a → b → c → d → e`, starting from `a`
- **THEN** the ends are `c` and `d`

#### Scenario: Unknown predicate
- **WHEN** an atom names an IRI that is not in the dictionary
- **THEN** the atom matches no hop and no error is raised

### Requirement: Path text syntax
Path text SHALL follow SPARQL 1.1 property-path syntax and precedence (`^` and postfix operators bind tighter than `/`, which binds tighter than `|`) plus `{m,n}`, `{m,}` and `{n}`. Atoms SHALL be `<iri>`, CURIEs over declared prefixes and `sys:`, `tm:`, `rdf:`, `xsd:`, or bare names resolved through the database vocabulary. Malformed text SHALL fail with a `Parse` error of dialect `Path` carrying the byte span. A negated property set SHALL fail with `Unsupported`.

#### Scenario: Precedence
- **WHEN** `^a/b|c` is parsed
- **THEN** it means `((^a)/b)|c`

#### Scenario: Parse error span
- **WHEN** `knows/(worksAt` is parsed
- **THEN** it fails with `Parse` of dialect `Path` whose span points at the end of the text

#### Scenario: Negated property set
- **WHEN** `!knows` is parsed
- **THEN** it fails with `Unsupported`

### Requirement: Hop semantics
A forward stored atom `p` SHALL step from `x` to `y` over each statement `(x p y)` visible in the path's view; its inverse over the same statements from `y` to `x`. A forward virtual hop SHALL step from a visible statement `e` to its subject, object or predicate, and have no neighbours from a value that is not a visible statement; its inverse SHALL step from `x` to every visible statement whose part is `x`. The wildcard SHALL step over visible statements in the relationship view only: object a node or statement, or predicate flagged `sys:isEdge true`; never `rdf:type`, never a `sys:` predicate, never a virtual hop. All hops of one evaluation SHALL use the path's one view.

#### Scenario: Paths cross layers
- **WHEN** `belief9 supportedBy e1`, `e1 = (alice worksAt acme)`, and `supportedBy/sys:subject` is evaluated from `belief9`
- **THEN** the only end is `alice`

#### Scenario: Virtual hop from a plain node
- **WHEN** `sys:subject` is evaluated from the node `alice`
- **THEN** no row is returned and no error is raised

#### Scenario: Retracted statement not traversed under Now
- **WHEN** `e1` is retracted and `sys:subject` is evaluated from `e1` under `Now` and under `AsOf` before the retraction
- **THEN** the first returns no row and the second returns the subject

### Requirement: Automaton compilation
An expression SHALL compile to a deterministic automaton over a refined alphabet of hop letters whose language equals the expression's language, so each hop sequence has exactly one run and no path is produced twice by an ambiguous expression. Bounded repetition SHALL be unrolled. An expression whose automaton would exceed 4 096 states SHALL fail with `Unsupported("path expression too complex")` before any store read.

#### Scenario: Ambiguous expression yields no duplicates
- **WHEN** `(knows|knows)*` is evaluated in `ALL_SHORTEST` mode
- **THEN** every path appears once

#### Scenario: Too complex
- **WHEN** an expression needs more than 4 096 automaton states
- **THEN** evaluation fails with `Unsupported("path expression too complex")`

#### Scenario: Machine-checked automaton
- **WHEN** the proofs library builds
- **THEN** "a compiled automaton accepts exactly the words of its expression's language, and its run on a word is unique" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Reachability mode
In `REACH` mode the result SHALL be each distinct end `y` such that some walk from the start to `y` of at most `max_hops` hops matches the expression, exactly once, with `hops` the length of a shortest such walk and no path value. With `*`, `?` or a minimum of 0, the start SHALL match itself with 0 hops even when it appears in no statement or is a literal. Rows SHALL come in non-decreasing hops, then by the end's raw ObjectId.

#### Scenario: Set semantics over a diamond
- **WHEN** `knows+` is evaluated from `a` over `a→b, a→c, b→d, c→d`
- **THEN** `d` is returned once with 2 hops

#### Scenario: Zero-length match of a literal
- **WHEN** `knows*` is evaluated from the literal `"x"`
- **THEN** exactly one row is returned, with end `"x"` and 0 hops

#### Scenario: Machine-checked reachability
- **WHEN** the proofs library builds
- **THEN** "REACH rows are exactly the ends of matching walks within the bound, each once, with minimal hop counts" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Trail mode
In `TRAIL` mode the result SHALL be one row per distinct matching path of at most `max_hops` hops in which no relationship identity repeats. The identity of a stored hop SHALL be its eid in either direction; of a virtual hop, the pair (statement eid, virtual predicate). Nodes MAY repeat. Parallel statements with equal `(s, p, o)` SHALL give distinct trails.

#### Scenario: Parallel edges give distinct trails
- **WHEN** two parallel statements `a knows b` exist and `knows` is evaluated from `a` in `TRAIL` mode
- **THEN** two rows are returned

#### Scenario: Stored edge and virtual hop of one statement
- **WHEN** `sys:subject/worksAt` is evaluated in `TRAIL` mode from `e1 = (alice worksAt acme)`
- **THEN** the trail `e1 → alice → acme` is returned, traversing `e1` first as a virtual hop and then as a stored edge

#### Scenario: Machine-checked trails
- **WHEN** the proofs library builds
- **THEN** "TRAIL rows are exactly the matching trails within the bound, each once" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Shortest modes
In `ANY_SHORTEST` mode the result SHALL be, per distinct end, the one matching path of minimal length whose hop-key sequence is lexicographically smallest. In `ALL_SHORTEST` mode it SHALL be, per distinct end, every distinct matching path of minimal length, each once. A hop key SHALL order by eid, then stored before virtual, then forward before inverse.

#### Scenario: Deterministic among ties
- **WHEN** two shortest paths of length 2 reach `d`, one whose first hop is statement `e5` and one whose first hop is statement `e3`
- **THEN** `ANY_SHORTEST` returns the path through `e3`

#### Scenario: All shortest
- **WHEN** the diamond `a→b→d`, `a→c→d` is searched from `a` in `ALL_SHORTEST` mode
- **THEN** both 2-hop paths to `d` are returned once each

#### Scenario: Machine-checked shortest paths
- **WHEN** the proofs library builds
- **THEN** "ANY_SHORTEST returns the hop-key-least minimal matching path per end and ALL_SHORTEST every minimal matching path exactly once" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Termination and search bound
Every mode SHALL terminate on graphs with cycles, self-loops and statement-layer cycles, without a hop bound in `REACH`, `ANY_SHORTEST`, `ALL_SHORTEST` and `TRAIL`. The search SHALL run on explicit fuel whose bound (nodes × automaton states for `REACH` and the shortest modes; distinct relationship identities for `TRAIL`) is proven sufficient, so fuel exhaustion never truncates a result.

#### Scenario: Reachability on a cycle
- **WHEN** `knows*` is evaluated on the cycle `a→b→c→a` without a hop bound
- **THEN** evaluation terminates with ends `a`, `b`, `c`

#### Scenario: Machine-checked fuel sufficiency
- **WHEN** the proofs library builds
- **THEN** "searching with the stated fuel bound returns the same rows as searching with any larger fuel" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Search-state guard
One evaluation SHALL hold at most `path_max_states` search states (default 1 000 000, set per database). Exceeding it SHALL fail with `PathLimitExceeded { limit }`, never return a truncated result, and leave the database unchanged.

#### Scenario: Guard trips on explosive trails
- **WHEN** `knows*` is evaluated in `TRAIL` mode on a dense graph with `path_max_states = 1000`
- **THEN** evaluation fails with `PathLimitExceeded { limit: 1000 }`

### Requirement: Endpoint binding
A path SHALL be evaluated from its start when the start is bound, else from its end with the inverse expression, returning rows whose start and end are the pattern's and whose path values read in start-to-end order. When neither endpoint is bound at evaluation time it SHALL fail with `Unsupported` ("path needs a bound endpoint"). A path pattern with a hop bound SHALL never report a path longer than it.

#### Scenario: Only the end is bound
- **WHEN** `(?x, knows+, carol)` is evaluated with `?x` unbound
- **THEN** the rows are those of the walks into `carol`, with `?x` bound to each start and paths in start-to-end order

#### Scenario: Machine-checked evaluation from the end
- **WHEN** the proofs library builds
- **THEN** "evaluating from the end with the inverse expression yields exactly the reversed rows of evaluating from the start" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Path rows
Each row SHALL carry the start, the end, the hop count, and the arrival (absent unless the search is time-respecting). In `TRAIL`, `ANY_SHORTEST` and `ALL_SHORTEST` modes each row SHALL also carry a path value: hops + 1 nodes and, per hop, the traversed statement's eid, its predicate (a reserved id outside the dictionary naming the `sys:` IRI for a virtual hop) and its direction. Rows of the path-returning modes SHALL come in non-decreasing hops, then by hop-key sequence. For the same state, view, start, expression, mode and bound, the rows and their order SHALL be identical on every run.

#### Scenario: Path value contents
- **WHEN** `knows/sys:subject` is evaluated from `belief9` in `TRAIL` mode
- **THEN** the path value has three nodes and two hops, the second naming `sys:subject`

### Requirement: Graph-scoped evaluation
A path MAY carry a graph set G. A hop SHALL then be taken only when its statement has a membership `(e sys:inGraph g)`, `g ∈ G`, visible in the path's view: the statement stepped over for a stored hop or wildcard, the statement whose part is stepped to or from for a virtual hop. Zero-hop rows SHALL NOT depend on G; an empty G or graphs without memberships SHALL leave only zero-hop rows. A path pattern with graph selector `Var(?g)` SHALL be evaluated once per graph with a visible membership in the view and bind `?g`.

#### Scenario: Path confined to a graph
- **WHEN** `a knows b` is in graph `g1`, `b knows c` is in no graph, and `knows+` is evaluated from `a` with G = `[g1]`
- **THEN** the only end is `b`

#### Scenario: Machine-checked graph scoping
- **WHEN** the proofs library builds
- **THEN** "a graph-scoped row is exactly an unscoped row of the same evaluation whose every hop statement has a visible membership in G" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Time-respecting evaluation
A path evaluation MAY be time-respecting with an optional start instant `after`. A time τ SHALL start at `after` (or −∞). A stored hop over a statement valid `[v_from, v_to)` SHALL be taken only when `v_to` is unbounded or `v_to > τ`, and SHALL set τ to `max(τ, v_from)`; a virtual hop SHALL always be allowed and keep τ. The view and a graph set SHALL still apply. In `REACH` mode each end SHALL be reported once with the length of its shortest time-respecting walk and its earliest arrival over all time-respecting walks within the bound; `TRAIL` SHALL return every time-respecting trail with its own arrival; the shortest modes SHALL return the minimal-length time-respecting paths with their arrivals. The arrival SHALL be absent when it is −∞.

#### Scenario: A longer walk can arrive earlier
- **WHEN** `a knows d` is valid from 2025, `a knows b`, `b knows c` and `c knows d` are valid from 2020, and `knows+` is evaluated time-respecting from `a`
- **THEN** `REACH` reports `d` with 1 hop and arrival 2020

#### Scenario: A start instant cuts early facts
- **WHEN** `a knows b` is valid `[2020, 2021)` and the search starts after 2022
- **THEN** `b` is not reached

#### Scenario: Machine-checked earliest arrival
- **WHEN** the proofs library builds
- **THEN** "the hop rule is monotone in τ, time-respecting REACH reports the earliest arrival over all time-respecting walks within the bound, its search bound suffices, and a later start instant reaches no more ends and arrives no earlier" holds as a theorem whose axioms satisfy the proof policy
