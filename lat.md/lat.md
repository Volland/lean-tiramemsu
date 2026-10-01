This directory defines the high-level concepts, business logic, and architecture of this project using markdown. It is managed by [lat.md](https://www.npmjs.com/package/lat.md) — a tool that anchors source code to these definitions. Install the `lat` command with `npm i -g lat.md` and run `lat --help`.

- [[overview]] — What lean-tiramemsu is, its goals and non-goals
- [[decisions]] — The fifteen design decisions D1–D15 and the alternatives each rejected
- [[architecture]] — The two Lean libraries, the Store abstraction, the SQLite boundary, concurrency, and the C ABI
- [[codec]] — Tier 0: ObjectIds with origin bits, literal canonicalization, doubles, the term dictionary, storage format 1 and the M1 deviations from Rust
- [[verification]] — Proof tiers, the proof policy, the trusted base, and how unproven parts are tested
- [[roadmap]] — Milestones M0–M6 mapped to OpenSpec changes, and the performance gate
