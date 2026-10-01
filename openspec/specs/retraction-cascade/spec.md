# retraction-cascade Specification

## Purpose
Defines how retracting a statement retracts every live statement standing on it through subject or object references, proven equal to the reflexive-transitive dependents closure, and how the same walk is read on any view without the writer.

## Requirements

### Requirement: Cascade equals the dependents closure

When a live statement `e` is retracted by any operation, the set of statements retracted for it SHALL be exactly the cascade set of `e`: the statements `x` for which a chain `x = x0, x1, …, xn = e` (n ≥ 0) exists where every `xi` is live at that point of the transaction and has `x(i+1)` as its subject or object. All of them SHALL receive the same `t_ret`, the current transaction. Only statement eids SHALL propagate; `IRI`, `NODE`, `BNODE`, `TX` and literal values SHALL never do. Already-retracted statements SHALL NOT be walked or changed.

#### Scenario: Annotation, reference and deep layer
- **WHEN** `e1 = (alice worksAt acme)`, `e2 = (e1 :confidence 0.8)`, `e7 = (:belief9 :supportedBy e1)` and `e8 = (e7 :method "llm")` are live and `e1` is retracted in transaction 12
- **THEN** `e1`, `e2`, `e7` and `e8` have `t_ret = 12`

#### Scenario: Plain nodes and transaction metadata do not cascade
- **WHEN** `(alice :name "Alice")` and `(tx5 sys:author :agent7)` are live, `(e1 sys:confirmedBy tx5)` is live, and `e1 = (alice worksAt acme)` is retracted
- **THEN** the confirmation is retracted and both other statements stay live

#### Scenario: Already retracted statements are not walked
- **WHEN** `e2 = (e1 :note "a")` was retracted earlier, `e3 = (e2 :note "b")` is live, and `e1` is retracted
- **THEN** `e2` keeps its retraction and `e3` stays live

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the property holds as a theorem whose axioms satisfy the proof policy

### Requirement: Cascade order, kinds and cycles

The cascade set SHALL be produced root first, then breadth-first, each expansion appending unseen statements in ascending eid order, with a visited set so that every statement in a reference cycle is retracted and reported exactly once. The root SHALL get the kind of the causing operation; the other members SHALL get `cascade` when that kind is `explicit` and the same kind otherwise (`supersede`, `cardinality`). The report SHALL list them in this order with these kinds.

#### Scenario: Diamond
- **WHEN** `e2 = (e1 :p x)`, `e3 = (e1 :q y)` and `e4 = (e2 :r e3)` are live and `e1` is retracted
- **THEN** the report lists `(e1, explicit), (e2, cascade), (e3, cascade), (e4, cascade)`, each once

#### Scenario: Cardinality replacement with annotations
- **WHEN** `:age` is `sys:one`, `e1 = (alice :age 30)` has `e2 = (e1 :source :form)`, and `(alice :age 31)` is asserted
- **THEN** `e1` and `e2` both have kind `cardinality`

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** termination, the absence of duplicates and the root-first order hold as theorems whose axioms satisfy the proof policy

### Requirement: Cascade size limit

The size of one cascade set, root included, SHALL NOT exceed the transaction's `max_cascade`; a larger set SHALL fail the whole transaction with `CascadeLimitExceeded { root, limit }` and leave no trace. The limit SHALL apply separately to each root (each retract, each match of retract-matching, each supersede, each cardinality replacement).

#### Scenario: Exactly at the limit
- **WHEN** a statement with 4 annotations is retracted with `max_cascade = 5`
- **THEN** the transaction commits and 5 statements are retracted

#### Scenario: Limit exceeded
- **WHEN** a statement with 5 annotations is retracted with `max_cascade = 5`
- **THEN** the transaction fails with `CascadeLimitExceeded` naming that statement and 5

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** the limit error occurring exactly when the closure is larger than the limit holds as a theorem whose axioms satisfy the proof policy

### Requirement: Dependents on any view

Reading the dependents of `e` on a view SHALL return `e` followed by the same breadth-first walk as the cascade, with "live" replaced by "visible in the view" for the root and every expansion; it SHALL be empty when `e` is not visible. Under the now view the result SHALL equal the cascade set of `e`, in the same order. The read SHALL never write, never take the writer, never burn an id, never be truncated and never fail because of its size.

#### Scenario: What depended on it back then
- **WHEN** `e1` with layers `e2` and `e7` exists as of transaction 3 and `e1` is retracted with its cascade in transaction 4
- **THEN** dependents of `e1` on the now view are empty and on the as-of view at 3 are `[e1, e2, e7]`

#### Scenario: Everything that ever depended
- **WHEN** layer `e2` on `e1` was retracted in transaction 3 and layer `e3` on `e1` asserted in transaction 4
- **THEN** dependents on the history view contain `e2` and `e3`, and on the now view only `e3`

#### Scenario: Larger than the cascade limit
- **WHEN** a statement has 20 layers
- **THEN** dependents return all 21 statements, while a retraction with `max_cascade = 10` fails

#### Scenario: Machine-checked
- **WHEN** the proofs library builds
- **THEN** dependents equal the closure over visible statements, and equal the cascade set under the now view, as theorems whose axioms satisfy the proof policy

### Requirement: Retracted structures stay visible in the past

A cascade SHALL only set `t_ret` and `ret_kind`, so the as-of view at `t_ret − 1` SHALL show every statement of the retracted structure with its original content.

#### Scenario: What a belief relied on
- **WHEN** `e1`, its annotation `e2` and its reference `e7` are retracted in transaction 20
- **THEN** the as-of view at transaction 19 contains `e1`, `e2` and `e7` unchanged
