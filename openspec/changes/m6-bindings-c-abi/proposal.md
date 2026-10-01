## Why

M0–M5 give a verified Lean core with SPARQL and Cypher, but the Node.js and Python users of tiramemsu still run the Rust engine. M6 puts the existing `@tiramemsu/node` and `tiramemsu` packages on the Lean backend without changing their public API, and only when the Lean build is fast enough (D14).

## What Changes

- Add a C ABI: one hand-written C file (about 150 lines, no logic) and a public header `tiramemsu.h` exporting `tm_open`, `tm_call`, `tm_free`, `tm_close` and `tm_version`, all JSON text in and out (D1, D9). The Lean runtime is initialized once and thread-safely, foreign threads are registered before they call in, handles are opaque integers, and no Lean object crosses the ABI.
- Build one shared library per platform (macOS arm64 and x86_64, Linux x86_64 and aarch64, Windows x86_64) with the Lean runtime and SQLite (via leansqlite, D8) linked statically and only the `tm_*` symbols exported.
- Port the Rust JSON bridge to Lean: the same operation names, argument, result and error JSON, view objects and term forms (D5, D6). Conformance is tested by running the cases of the pinned Rust `bindings/json` tests against both builds.
- Re-implement the native layer of the Node.js package with koffi over the shared library (no compile at install) and of the Python package with ctypes. The TypeScript and Python wrappers and their public types stay as they are; the existing test suites pass unchanged.
- Add the performance gate (D14): the Lean-backed packages are released only if the ratios to pinned Rust at 10⁶ statements are met; results are published with every release.
- **BREAKING (packaging only)**: the npm package gains a runtime dependency on `koffi`; the Python wheels become `py3-none-<platform>` instead of `cp39-abi3`; no musllinux wheel is built. Public APIs are unchanged.

## Capabilities

### New Capabilities

- `c-abi`: the five exported functions, their memory and threading contract, error JSON and status codes, the handle table, runtime initialization, static linking and symbol hiding per platform, and the ABI test regime (ASan, valgrind, multi-threaded callers).
- `json-bridge`: the Lean port of the JSON call surface: open options, operations, views, terms, transactions with named references, speculation, query results, paths and graphs, error codes, and conformance against the Rust bridge.
- `node-binding`: `@tiramemsu/node` over the shared library through koffi: unchanged TypeScript API and types, prebuilt libraries per platform, loader behaviour, and the unchanged Rust test suite.
- `python-binding`: the `tiramemsu` package over the shared library through ctypes: unchanged public API and typing, parallel calls from threads, platform wheels, and the unchanged Rust test suite.
- `performance-gate`: the release gate against pinned Rust on the shared benchmark harness, its thresholds, measurement method and published results.

### Modified Capabilities

None; there are no existing specs.

## Impact

- New code: `abi/tiramemsu.c`, `abi/tiramemsu.h`, `Tiramemsu/Bridge/*` (JSON, views, terms, reads, transactions, errors, handle table, exports), `bindings/node`, `bindings/python`, `conformance/bridge/` (case corpus and runners), `bench/gate/`.
- Depends on M3a (reads, transactions, paths, bundles, Lean API), M4 (`sparql`), M5 (`cypher`, `cypherWrite`, the `cypher` op) and the M0 benchmark harness and Rust oracle pin.
- Verification: everything in this change is shell, trusted and Tier 4 tested (D2); no new theorems. The trusted base gains the C shim, koffi and ctypes.
- Dependencies: `koffi` (npm, runtime); no new Lean dependencies (the bridge carries its own JSON codec so that the `Lean` compiler library is not linked, D7).
- CI: per-platform library builds, ABI sanitizer jobs, conformance against the Rust bridge, both package suites, release workflows gated on the performance gate.
- Docs: `lat.md/architecture.md` (C ABI: handle table location), `lat.md/roadmap.md` (gate method), new `lat.md/bindings.md`.
