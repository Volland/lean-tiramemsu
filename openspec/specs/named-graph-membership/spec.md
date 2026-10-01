# named-graph-membership Specification

## Purpose
Defines named graphs at storage and verb level: a graph is a node, membership is the layer statement `(e sys:inGraph g)` on a statement's eid, written only by the engine's membership verbs. Query-side graph selection belongs to later milestones.

## Requirements

### Requirement: Graph and membership model

A graph SHALL be named by an `IRI`, `NODE` or `BNODE` id; any other id SHALL fail with `InvalidGraphName { term }` and write nothing. A membership SHALL be an ordinary statement `(m, e, sys:inGraph, g)` with its own eid, transaction time, valid time and layers. A statement SHALL keep one eid however many graphs it is in. No column, table or format change SHALL be introduced.

#### Scenario: One statement in two graphs
- **WHEN** `e1` is added to `g1` and to `g2`
- **THEN** `e1` is the only statement for its triple and has two live memberships

#### Scenario: Literal as graph name
- **WHEN** `e1` is added to the literal `"g"`
- **THEN** the call fails with `InvalidGraphName` and no membership exists

### Requirement: Adding and removing memberships

Adding a live statement `e` to `g` SHALL assert `(e sys:inGraph g)` idempotently over the given valid interval (unbounded by default) and return the membership eid and whether it is new; the report SHALL list new memberships separately from asserted statements. Adding a retracted or unknown statement SHALL fail with `NotLive(e)`; adding a statement whose predicate is in `sys:` or `tm:` SHALL fail with `ReservedNamespace`. Removing `e` from `g` SHALL retract its live memberships in `g` with kind `explicit`, leave `e` live, and return whether one was live.

#### Scenario: Idempotent add
- **WHEN** `e1` is added to `g1` twice in one transaction
- **THEN** both calls return the same membership eid and the second reports it as not new

#### Scenario: Remove from one graph keeps the statement
- **WHEN** `e1` is in `g1` and `g2` and is removed from `g1`
- **THEN** the `g1` membership is retracted and `e1` and its `g2` membership stay live

#### Scenario: Schema statements cannot be members
- **WHEN** the statement `(:email sys:unique true)` is added to `g1`
- **THEN** the call fails with `ReservedNamespace`

### Requirement: Graph management verbs

Create-graph SHALL assert `(g rdf:type sys:Graph)` idempotently. Clear-graph SHALL retract every live membership in `g` and no member statement, returning the membership eids. Drop-graph SHALL clear `g` and retract its `sys:Graph` declaration, leaving every other statement about `g` live, and return the retracted eids, memberships first.

#### Scenario: Drop keeps other metadata
- **WHEN** `g1` has members, a declaration and `(g1 :startedBy :agent7)`, and `g1` is dropped
- **THEN** the memberships and the declaration are retracted and `(g1 :startedBy :agent7)` stays live

### Requirement: Membership predicate is engine-owned

A user assert or create with predicate `sys:inGraph` SHALL fail with `ReservedNamespace(urn:tiramemsu:sys:inGraph)`; only the membership verbs SHALL write it.

#### Scenario: Direct membership write rejected
- **WHEN** a transaction asserts `(e1 sys:inGraph g1)` directly
- **THEN** it fails with `ReservedNamespace` and writes nothing

### Requirement: Memberships follow their statement

Retracting a member statement SHALL retract its memberships through the cascade with kind `cascade`, reported as retracted memberships. Supersede and cardinality-one replacement of a member statement SHALL retract its memberships and SHALL NOT copy them to the replacement.

#### Scenario: Cascade retracts memberships
- **WHEN** `e1` is in `g1` and `e1` is retracted
- **THEN** the membership is retracted in the same transaction with kind `cascade`

#### Scenario: Supersede drops memberships
- **WHEN** `e1` is in `g1` and is superseded into `e10`
- **THEN** the old membership is retracted with kind `supersede` and `e10` is in no graph

### Requirement: Membership reads on a view

A view SHALL list the members of `g` as the statements visible in the view that have a membership in `g` visible in the same view, in ascending eid order, and SHALL list the graphs as those with a visible membership or a visible declaration, in ascending id order. Both reads SHALL respect transaction time and valid time.

#### Scenario: Time travel
- **WHEN** `e1` was added to `g1` in transaction 5 and removed in transaction 9
- **THEN** the members of `g1` as of 7 are `[e1]` and as of 9 are empty

#### Scenario: Bounded membership under valid-at
- **WHEN** `e1` was added to `g1` valid `[2025-01-01, 2025-07-01)`
- **THEN** the members of `g1` at valid-at `2025-03-01` are `[e1]` and at `2025-08-01` are empty
