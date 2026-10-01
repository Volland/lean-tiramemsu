## Purpose

Lets an agent cite the stored statements behind each answer row, and later find answers that relied on a retracted statement, with proven guarantees that the citations are real and enough to re-derive the row.

## ADDED Requirements

### Requirement: Provenance on request
Query execution SHALL accept a provenance option, off by default. With it, every result row SHALL carry the ascending, duplicate-free list of eids of the stored statements that support it. Without it, plans, rows and output SHALL be unchanged. With it, the rows themselves (without their eid lists) SHALL be exactly the rows of the same query without provenance.

#### Scenario: Basic graph pattern
- **WHEN** `Join[(alice worksAt ?c), (?c locatedIn ?city)]` is executed with provenance over `e1 = (alice worksAt acme)` and `e2 = (acme locatedIn paris)`
- **THEN** the one row carries `[e1, e2]`

#### Scenario: Machine-checked rows unchanged
- **WHEN** the proofs library builds
- **THEN** "erasing the eid lists of the provenance evaluation yields exactly the reference bag" holds as a theorem whose axioms satisfy the proof policy

### Requirement: What a row cites
A row SHALL cite:
- for a triple-pattern match, its statement's eid under `BagOfEids` or with an eid variable, and under `SetOfTriples` without an eid variable every visible eid with the matched `(s, p, o)`;
- for a pattern with graph selector `Var(?g)` or a one-graph `Set`, also the membership statement; with a set of two or more graphs, no membership;
- for `Join`, the union of its inputs' citations; for `LeftJoin`, the left row's plus the matched right row's; for `Union`, the branch taken; `Filter` and `Extend` SHALL add nothing, so statements tested by `EXISTS` or `NOT EXISTS` are not cited;
- for a path pattern in `TRAIL` or a shortest mode, the eid of every hop's statement and, when graph-scoped, the membership used; in `REACH` mode, nothing;
- for a virtual-predicate pattern and for inline values, nothing.

#### Scenario: Optional present and absent
- **WHEN** an optional part matches for one row and not for another
- **THEN** the first row cites the optional statement and the second does not

#### Scenario: Two episodes, one row, both eids
- **WHEN** under `SetOfTriples` two visible statements have content `(alice worksAt acme)` and `(alice worksAt ?c)` is executed with provenance
- **THEN** one row is returned citing both eids

#### Scenario: Existence test is not cited
- **WHEN** `Filter(EXISTS (?x confidence ?k), (?x worksAt ?c))` is executed with provenance
- **THEN** rows cite only the `worksAt` statements

### Requirement: Modifiers and aggregates
A distinct projection SHALL merge rows equal on the projected variables into one row citing the union of their eids, before skip and limit apply. An aggregate row SHALL cite the union of its group's input rows' citations. Ordering SHALL keep each row's citation.

#### Scenario: Distinct merges provenance
- **WHEN** `Project([?c], distinct, (?x worksAt ?c))` meets two employees of `acme`
- **THEN** one row `?c = acme` cites both statements

#### Scenario: Group provenance
- **WHEN** `Aggregate([?c], [COUNT(*) as ?n], (?x worksAt ?c))` groups three statements under `acme`
- **THEN** the `acme` row cites the three eids

### Requirement: Provenance soundness
Every eid a row cites SHALL be the eid of a statement visible in the view of a citing leaf of the query (a triple pattern, a membership or a path hop) that matches that leaf under the row's derivation.

#### Scenario: Retracted statement cited from the past
- **WHEN** a pattern under `AsOf(150)` matches statement `e1`, which was retracted at transaction 160, and the query is executed with provenance
- **THEN** the row cites `e1`, which is visible in that pattern's view

#### Scenario: Machine-checked soundness
- **WHEN** the proofs library builds
- **THEN** "every cited eid is visible in the view of a citing leaf and supports the row" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Provenance sufficiency
A row's cited eids SHALL suffice to re-derive it: evaluating the query with every citing leaf restricted to the cited statements, while non-citing leaves, negative tests (an optional's absence, `EXISTS`, `NOT EXISTS`, multi-graph membership tests, `REACH` paths, virtual predicates) and the inputs of aggregates and orderings read the full view, SHALL produce the row.

#### Scenario: Re-derive from citations
- **WHEN** a store is reduced to the cited statements of a join row plus all statements read only by negative tests
- **THEN** the same query still produces that row

#### Scenario: Machine-checked sufficiency
- **WHEN** the proofs library builds
- **THEN** "every row of the provenance evaluation belongs to the witness evaluation restricted to its cited eids" holds as a theorem whose axioms satisfy the proof policy

### Requirement: Stale answers can be detected
Because citations are statement eids, a caller SHALL be able to check every cited eid against a later view and find answers that relied on a statement retracted since.

#### Scenario: Detect a stale answer
- **WHEN** a row cited `e1`, and `e1` is retracted later
- **THEN** `e1` is no longer visible under `Now`, and its row under `History` shows the retracting transaction
