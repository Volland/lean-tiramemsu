## Purpose

Moves a belief with its layers and evidence from one database file to another (one file per agent) as a portable value, with export from any view and idempotent import, proven to round-trip.

## ADDED Requirements

### Requirement: Bundle members
Exporting the bundle of a root statement from a view SHALL collect the root's dependents in that view (its layers, the statements that cite it, its memberships) plus every statement visible in the view that a collected statement references in subject or object position, transitively. It SHALL NOT add the dependents of a statement collected only because it is referenced. A root not visible in the view SHALL fail with `NotLive(root)`.

#### Scenario: Layers, nested layers and a supporting belief
- **WHEN** `e1 = (alice worksAt acme)` has `e2 = (e1 confidence 0.8)`, `e3 = (e2 source chat)` and `e4 = (belief9 supportedBy e1)`, and the bundle of `e1` is exported
- **THEN** it holds `e1`, `e2`, `e3` and `e4`

#### Scenario: Evidence is carried downward
- **WHEN** `e4 = (belief9 supportedBy e1)` is the root and `e1` has a layer `e2`
- **THEN** the bundle holds `e4` and `e1` but not `e2`

### Requirement: Bundle exclusions
A candidate statement SHALL be excluded when its subject or object is a transaction, when its predicate is reserved so that a user write of it would be rejected (`sys:inGraph` excepted), or when it references a statement that is not visible or is excluded. Exclusion SHALL propagate to every statement referencing an excluded one, and the downward closure SHALL be computed from the statements that remain. An excluded root SHALL fail with `Unsupported` naming the reason.

#### Scenario: Confirmation is left out
- **WHEN** `e1` was confirmed (an engine statement referencing a transaction)
- **THEN** the bundle of `e1` holds no confirmation statement

#### Scenario: Supersede link is left out
- **WHEN** `e5` superseded `e1` and the bundle of `e5` is exported
- **THEN** it holds no `sys:supersedes` statement

### Requirement: Bundle value
A bundle SHALL hold an ordered list of statements, each with a bundle-local id equal to its position, a subject, a predicate IRI, an object and a valid-time interval, plus the root's local id. A subject or object SHALL be a value (IRI or literal), a local statement id, or a local anonymous-node label. Statements SHALL come after the statements they reference when references are acyclic, ties broken by source eid, reference-cycle members last in eid order. The same view of the same data SHALL always produce an equal bundle.

#### Scenario: References come first
- **WHEN** the bundle of `e2 = (e1 confidence 0.8)` is exported
- **THEN** `e1` has a smaller local id than `e2`

#### Scenario: Stable output
- **WHEN** the same bundle is exported twice from the same view
- **THEN** the two bundles are equal

### Requirement: Anonymous nodes
`NODE` and `BNODE` ids SHALL be exported as local labels numbered from 0 in order of first appearance, never as skolem IRIs. Import SHALL mint one fresh node per label, so distinct anonymous nodes stay distinct and a shared one stays shared. Import SHALL reject a skolem IRI of a statement, node, blank node or transaction with `InvalidTerm`.

#### Scenario: Two anonymous nodes stay distinct and consistent
- **WHEN** a bundle mentions anonymous node `n1` in two statements and `n2` in one, and is imported
- **THEN** the target holds two fresh nodes, the first used by two statements

### Requirement: Import is idempotent assert
Importing a bundle SHALL, within the caller's transaction, check the bundle's structure and cycles, then write every statement in bundle order: a `sys:inGraph` statement as a graph membership, every other statement as an assert with its valid time. Schema and reserved-namespace checks SHALL apply as for any user write, and any failure SHALL roll back the whole transaction. It SHALL return the root's eid and, in bundle order, each local id with its eid and whether it is new. A root whose content is already live with an overlapping valid time SHALL map to that eid and take the layers. Two statements of equal content and overlapping valid time SHALL map to one eid.

#### Scenario: Round trip between two databases
- **WHEN** the bundle of `e1` with one layer is exported from database A and imported into an empty database B
- **THEN** B holds two new live statements, the layer's subject being the new eid of the root

#### Scenario: Schema violation fails atomically
- **WHEN** an import violates a `sys:unique` constraint of the target
- **THEN** the transaction fails and the target is unchanged

#### Scenario: Machine-checked round trip
- **WHEN** the proofs library builds
- **THEN** "importing an exported bundle into a fresh store and exporting the imported root yields a bundle equal to the original up to renaming of ids, after collapsing equal-content statements" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Re-import changes nothing
Importing a bundle without anonymous-node labels a second time SHALL change no live statement and report every statement as not new. A bundle with anonymous-node labels SHALL mint fresh nodes on every import, like RDF blank nodes.

#### Scenario: Second import changes nothing
- **WHEN** a bundle without anonymous nodes is imported twice into the same database
- **THEN** the second import adds no statement and reports every entry with `new = false`

#### Scenario: Machine-checked re-import
- **WHEN** the proofs library builds
- **THEN** "a second import of a bundle without anonymous labels leaves the live statements unchanged and reports nothing new" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Cycles and malformed bundles
Import SHALL fail with `Unsupported("bundle with a reference cycle")` before writing when the bundle's statements reference each other in a cycle. A duplicate or unknown local id, a reference to a missing statement, a non-IRI predicate or an unknown root SHALL fail with `InvalidTerm` before writing.

#### Scenario: Cycle
- **WHEN** a bundle holds `e7 about e8` and `e8 about e7`
- **THEN** export succeeds and import fails with `Unsupported("bundle with a reference cycle")` without writing

### Requirement: Bundle of the past
Export SHALL read every statement through the given view, so an as-of view SHALL produce the bundle of a structure as it was, including statements retracted since.

#### Scenario: Since-retracted structure
- **WHEN** a layer of `e1` was retracted at 160 and the bundle of `e1` is exported as of 150
- **THEN** the bundle holds the layer

### Requirement: Bundle JSON
A bundle SHALL have the JSON form `{"format": "tiramemsu-bundle/1", "root", "statements"}`, each statement `{"id", "s", "p", "o"}` plus `validFrom` and `validTo` in epoch milliseconds when bounded, `p` the predicate IRI text, and a term one of `{"iri"}`, `{"ref": id}`, `{"blank": label}`, `{"lex", "datatype"}` or `{"lex", "lang"}`. Writing SHALL be byte-identical to the Rust build for the same bundle. Reading SHALL accept exactly that form, reject another format string or a malformed statement with `InvalidTerm`, and reading a written bundle SHALL give the same bundle.

#### Scenario: JSON round trip
- **WHEN** a bundle is written as JSON and read back
- **THEN** the result equals the original bundle

#### Scenario: Same bytes as Rust
- **WHEN** the same bundle is exported to JSON by the Lean build and the Rust oracle from the same file
- **THEN** the two texts are byte-identical

#### Scenario: Unknown version
- **WHEN** JSON with `"format": "tiramemsu-bundle/2"` is read
- **THEN** reading fails with `InvalidTerm`
