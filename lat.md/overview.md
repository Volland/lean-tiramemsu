# Overview

lean-tiramemsu is a port of tiramemsu (layered, bitemporal, never-forget graph memory on SQLite) from Rust to Lean 4, compiled to native code, with its core semantics proven.

The Rust implementation lives in the sibling repository `../tiramemsu` (linked into this repo as `tiramemsu/`). It stays the behavioral reference: the Lean build reads and writes the same files and returns the same query results, and the Rust binary is the oracle for everything that is tested rather than proven. See [[verification#Differential Oracle]].

## Goals

The port exists to make tiramemsu's novel claims (layers, never forget, supersede replay, bitemporal views, paths) machine-checked, while staying a drop-in replacement for the Rust core.

- Proven: the value codec, the store state machine, and the query semantics, including joins and paths. See [[verification#Proof Tiers]].
- Native: `lake build` produces native libraries and executables through Lean's C backend. The generated C is an intermediate artifact, never edited or reviewed.
- Compatible: same file format, same query results, same JSON bridge, same Node.js and Python package APIs.

## Non-Goals

These are deliberately out of scope, so that proof effort goes where the project's claims are.

- Standalone C without the Lean runtime, or hand-written C beyond the one ABI shim. See [[architecture#C ABI]].
- Formal semantics of SPARQL 1.1 or openCypher. Front ends are differential-tested. See [[verification#Proof Tiers]].
- The `tm_path` SQL table function and SQL UDFs; paths stay available through every other surface.
- Erasure (tag 15 `SEALED`, crypto-shredding). Format 1 rejects it, as in Rust.
- Memory merging. Only its algebraic laws are proven on the model. See [[decisions#D15 Origin Bits Reserved]].
