This directory defines the high-level concepts, business logic, and architecture of this project using markdown. It is managed by [lat.md](https://www.npmjs.com/package/lat.md) — a tool that anchors source code to these definitions. Install the `lat` command with `npm i -g lat.md` and run `lat --help`.

- [[overview]] — What lean-tiramemsu is, its goals and non-goals
- [[decisions]] — The fifteen design decisions D1–D15 and the alternatives each rejected
- [[architecture]] — The two Lean libraries, the Store abstraction, the SQLite boundary, concurrency, and the C ABI
- [[verification]] — Proof tiers, the proof policy, the trusted base, and how unproven parts are tested
- [[roadmap]] — Milestones M0–M6 mapped to OpenSpec changes, and the performance gate
