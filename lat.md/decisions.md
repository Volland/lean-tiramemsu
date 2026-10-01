# Decisions

The fifteen decisions taken in the design interview on 2026-10-01, each with the alternative it rejected. Later changes cite them by number.

## D1 Native Through Lean

Lean is the source language; the native binary comes from Lean's own C backend with the Lean runtime linked statically. Rejected: standalone C, or readable C verified by a separate tool.

## D2 Proof Scope

Tiers 0–2 are proven (codec, store state machine, query semantics, plus provenance soundness and bundle round-trip). Tiers 3–4 (front-end lowering, physical execution) are differential-tested. See [[verification#Proof Tiers]].

## D3 SQLite As Sorted Index Backend

SQLite keeps the Rust schema, triggers and file format but only serves appends, retraction updates and ordered index range scans.

All query evaluation runs in Lean, so the proven evaluator is the one that executes. Rejected: SQL codegen (unverifiable), a pure-Lean storage engine (loses SQLite durability and file compatibility).

## D4 Scope And Stages

v1 is M0–M3: a verified core with a Lean API and CLI. M4 (SPARQL), M5 (Cypher) and M6 (bindings) follow. Every stage is an OpenSpec change. See [[roadmap]].

## D5 Fresh Specs

The OpenSpec specs are written fresh around the Lean design, stage by stage; the Rust specs are not imported. They are read as reference material only.

## D6 Compatible By Contract

The fresh specs commit to the Rust file format (schema, triggers, ObjectId encoding, `format_version`) and Rust query results, with every deviation listed.

The pinned Rust build is the differential oracle; the W3C SPARQL suite and the openCypher TCK are a second oracle.

## D7 Proof Policy

Runtime library imports only Lean core and Std; proofs live in a separate library that may import Mathlib. Verified code is total; `implemented_by` only with `@[csimp]`; no axioms about SQLite. See [[verification#Proof Policy]].

## D8 SQLite Through leansqlite

SQLite is reached through `leanprover/leansqlite`, pinned, which bundles the amalgamation. No hand-written C for storage. The `tm_path` SQL table function is dropped as a listed deviation.

## D9 C ABI Shim

One hand-written C file (about 150 lines, no logic) exports a `const char*` JSON-bridge ABI. Node.js binds through koffi and Python through ctypes. See [[architecture#C ABI]].

## D10 Writer Plus Reader Pool

One mutex-guarded writer connection and a pool of reader connections, each View pinned to a WAL snapshot, queries on Lean tasks. See [[architecture#Concurrency]].

## D11 Doubles As Bits

The core represents `xsd:double` as its IEEE bit pattern, with an exact-arithmetic, correctly rounded parser and a shortest round-trip printer proven inverse.

Output is byte-identical to Rust's `{:e}` form, checked by fuzzing. Hardware `Float` is used only for query arithmetic.

## D12 Scoped bv_decide

`bv_decide`, and with it its compiler-checked certificate axioms, is allowed only in codec proofs, through an explicit CI allowlist. See [[verification#Proof Policy]].

## D13 Hybrid Joins Proven Order-Independent

Index nested-loop joins for acyclic patterns (M3a) and Leapfrog Triejoin for cyclic ones (M3b). Both are proven equal to the natural-join semantics for every order, so the planner needs no proof.

## D14 Performance Gate At Bindings

Benchmarks are report-only through M5. Switching the Node.js and Python packages to the Lean backend (M6) is gated on ratios against Rust. See [[roadmap#Performance Gate]].

## D15 Origin Bits Reserved

The `STMT`, `NODE`, `BNODE` and `TX` payloads split into a 12-bit origin and a 48-bit counter from M1, and the Rust `reserve-replica-id` change lands too. The 2P-set merge laws are proven on the model.
