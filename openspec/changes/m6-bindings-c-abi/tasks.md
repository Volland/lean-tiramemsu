## 1. JSON codec

- [ ] 1.1 Add `Tiramemsu/Bridge/Json.lean`: `Json` and `JNum` types, a `ByteArray` parser with UTF-8 validation and a depth limit of 128, and a printer (integers bare; doubles shortest round-trip with `.` or exponent via the M1 printer; non-finite doubles as `null`)
- [ ] 1.2 Property tests: print then parse is the identity; integer/double classification matches serde_json on a table of edge literals (2^53, 2^63, 2^64, `1e2`, `-0`, `1.0`); depth 128 accepted, 129 rejected; invalid UTF-8 rejected
- [ ] 1.3 Microbenchmark parse and print of a 1 MB result against serde_json and record it in the bench report

## 2. Bridge core

- [ ] 2.1 Add `Bridge/Error.lean`: `BridgeError`, code names for every core error variant (same names as the Rust bridge), `InvalidArgument`, `InvalidHandle`, `Internal`, and the `{"code","message"}` form
- [ ] 2.2 Add `Bridge/Term.lean`: term from and to JSON, `$int`, `lex`/`datatype`/`lang`, times (epoch ms, RFC 3339 date or date-time), eids (`n`, `{"stmt"}`, `{"ref"}`), Cypher parameters; unit tests for every row of the json-bridge term requirement
- [ ] 2.3 Add `Bridge/View.lean`: view object to `View`, `asOf` selector checks, `validAt`; tests for the four view scenarios
- [ ] 2.4 Add `Bridge/Database.lean`: open with the six options (unknown key rejected before any file is created), `info`, `optimize`, `call` dispatch, `callText` (empty text is `null`)
- [ ] 2.5 Add `Bridge/Read.lean`: `sparql` (with `provenance`), `cypher`, `triples` (unstored term gives `[]`), `events`, `graphs`, `graphMembers`, `values`, `dependents`, `bundle`, and their result JSON
- [ ] 2.6 Extend `Bridge/Read.lean` with `path`: modes, `maxHops`, `graphs`, `timeRespecting`, row JSON with `arrival` and `path`
- [ ] 2.7 Add `Bridge/Tx.lean`: `transact` with options, all sixteen ops, `as`/`ref` resolution, report JSON with `results` and `refs`, rollback on any failure
- [ ] 2.8 Extend `Bridge/Tx.lean` with `cypherWrite` and `with` (speculation keeps nothing, failures keep nothing)
- [ ] 2.9 Concurrency test on the Lean API: eight reader threads and one writer, every observed count a multiple of the transaction size

## 3. Bridge conformance

- [ ] 3.1 Define the case format (steps of `open`/`call`, `args`, `expect` subset pattern, `expectError` code) and the canonicalizer (structural equality, numbers by value, `instant` and `info.path` masked, errors by `code`)
- [ ] 3.2 Transcribe every `#[test]` of the pinned `bindings/json/tests/bridge.rs` into `conformance/bridge/cases/`, one file per test, read from the pinned commit without modifying the Rust repository
- [ ] 3.3 Add the coverage check: list the `#[test]` names at the pinned commit and fail on any without a case file
- [ ] 3.4 Add the Rust runner crate depending on `tiramemsu-json` at the pinned revision; it writes a transcript per case
- [ ] 3.5 Add the Lean runner (`lake exe bridge-conformance`) and the transcript comparison; all cases pass and match Rust
- [ ] 3.6 Add the differential fuzzer (random op lists, refs, views, terms, malformed arguments) comparing both bridges; run 10⁴ cases in CI and more nightly

## 4. Handle table and exports

- [ ] 4.1 Add `Bridge/Handles.lean`: global table under a mutex, monotonic handles from 1, `close` removes the entry while in-flight calls keep their reference
- [ ] 4.2 Add `Bridge/Export.lean`: `@[export]` entry points for open, call, close and version taking `ByteArray` input and returning status-and-text pairs, catching every exception as `Internal`
- [ ] 4.3 Lean tests: stale handle gives `InvalidHandle`, double close fails, handles never repeat, version object fields

## 5. C shim and shared library

- [ ] 5.1 Write `abi/tiramemsu.h` (standard headers only, `tm_handle`, `TM_OK`, `TM_ERROR`, five prototypes, ownership rules in comments) and compile it alone as C99 and C++17 in CI
- [ ] 5.2 Write `abi/tiramemsu.c`: once-only initialization (`pthread_once` / `InitOnceExecuteOnce`), init-failure flag, per-thread registration with exit-time release, text copy in and out, `tm_free`; keep it free of operation logic (about 150 lines)
- [ ] 5.3 Add the Lake target that links the shim, `Tiramemsu`, leansqlite with SQLite, `Init`, `Std` and `leanrt` into one shared library per platform, with the export lists (`exports.map`, `exports.txt`, `exports.def`) and hidden visibility
- [ ] 5.4 Add the export check (`nm`/`dumpbin`: exactly the five `tm_*` functions) and the dependency check (`ldd`/`otool -L`/`dumpbin /dependents`: system libraries only)
- [ ] 5.5 Licence audit of every statically linked component; if the runtime contains GMP, rebuild `leanrt` from the pinned toolchain sources without GMP; ship `THIRD_PARTY_NOTICES` beside the library
- [ ] 5.6 CI matrix builds the library on macOS arm64, macOS x86_64, Linux x86_64, Linux aarch64 and Windows x86_64 and uploads them as artifacts

## 6. ABI tests

- [ ] 6.1 Write the C test program: every function, NULL and empty arguments, NULL out pointers, invalid UTF-8, stale and unknown handles, version object, error passthrough
- [ ] 6.2 Add the multi-threaded tests: racing first calls (32 threads), 16 threads of mixed reads and writes on one handle and on several, close during a call, 10⁴ short-lived threads, 512 KiB-stack threads running the corpus
- [ ] 6.3 Add the ABI conformance runner (corpus through the shared library) and compare its transcripts with Rust
- [ ] 6.4 Run the test program under ASan and UBSan on Linux and macOS and under valgrind memcheck on Linux x86_64, with `LEAN_ABORT_ON_PANIC=1`; add the negative control that a skipped `tm_free` fails the memcheck job
- [ ] 6.5 Add the 10⁵-call RSS stability test for Lean reference leaks
- [ ] 6.6 Load the library in a Python process that already uses `sqlite3` and in Node.js, and check both SQLite versions and libuv coexist

## 7. Node.js package

- [ ] 7.1 Copy the pinned Rust `bindings/node` wrapper, tests and configuration into `bindings/node`; record the hash list of every file that must stay identical and add the CI hash check
- [ ] 7.2 Add `lib/native.ts`: koffi bindings for the five functions, `Native` class with the `tiramemsu:` error prefix, string copy then `tm_free`, `FinalizationRegistry` closing handles, ABI version check, platform selection with the unsupported-platform message
- [ ] 7.3 Replace the `loadNative()` block of `lib/index.ts` with the import of `lib/native.ts`; add `koffi` as a dependency; remove the napi build script and `.node` artifacts
- [ ] 7.4 Check the `.d.ts` declaration diff against the pinned Rust build is empty and `tsc --strict` passes
- [ ] 7.5 Run the pinned vitest suite unchanged on all five platforms in CI
- [ ] 7.6 Add the garbage-collection test (a thousand dropped databases leave no open files) as a package-local test outside the pinned suite
- [ ] 7.7 Pack test: tarball holds `dist/` and five libraries under `prebuilds/<platform>-<arch>/`; install with `--ignore-scripts` and smoke-test on each platform; record unpacked size

## 8. Python package

- [ ] 8.1 Copy the pinned Rust `bindings/python` wrapper, stub, `py.typed` and tests into `bindings/python`; record the hash list and add the CI hash check
- [ ] 8.2 Add `tiramemsu/_native.py`: ctypes bindings (`CDLL`, so the interpreter lock is released), `Native` class with `RuntimeError("tiramemsu:…")`, string copy then `tm_free`, `weakref.finalize` closing handles, ABI version check, platform message when the library is missing
- [ ] 8.3 Replace the maturin build with a hatchling build that copies the platform library into `tiramemsu/_lib/` and tags the wheel `py3-none-<platform>`
- [ ] 8.4 Check the public-name and signature listing against the pinned Rust package and run `mypy --strict`
- [ ] 8.5 Run the pinned pytest suite unchanged on all five platforms in CI, with `faulthandler` enabled
- [ ] 8.6 Wheel checks: `auditwheel` on manylinux x86_64 and aarch64, `delocate` on macOS, smoke install in a fresh virtual environment per platform

## 9. Performance gate and release

- [ ] 9.1 Add `bench/gate/thresholds.json` with the D14 thresholds and the binding-overhead threshold
- [ ] 9.2 Add the gate workloads to the M0 harness where missing: batched and single writes, supersede, point and 2-hop lookups per view, acyclic BGPs, hub-and-spoke and layered triangles, the four path shapes, churn as-of versus no-history, footprint after checkpoint, package-level point lookup
- [ ] 9.3 Add the gate evaluator (medians of ≥10 runs after 2 warm-ups, ratios, result equality, missing-workload failure) with unit tests on synthetic results for pass, each failing threshold and a missing workload
- [ ] 9.4 Add the report renderer (`gate.json`, `gate.md` with medians, IQR, ratio, threshold, verdict, machine, revisions, dataset hash)
- [ ] 9.5 Add the release workflow: library matrix, ABI and conformance jobs, package suites, gate job on the dedicated Linux x86_64 runner, report-only macOS arm64 run, npm publish with provenance and PyPI trusted publishing, both depending on the gate; manual runs publish only when requested
- [ ] 9.6 Rehearse the release by hand without publishing and check every artifact and the gate report are uploaded
- [ ] 9.7 Commit the gate results under `bench/results/<version>/` and attach them to the release notes with the list of json-bridge deviations

## 10. Documentation and checks

- [ ] 10.1 Update `lat.md/architecture.md#C ABI`: handle table held in Lean, status-plus-out-pointer signatures, symbol hiding, runtime and thread registration
- [ ] 10.2 Add `lat.md/bindings.md`: JSON bridge, C ABI, Node.js and Python packages, conformance corpus, listed deviations; link it from `lat.md/lat.md`
- [ ] 10.3 Update `lat.md/roadmap.md#Performance Gate` with the measurement method, gating machine and binding-overhead threshold, and `lat.md/verification.md#Trusted Base` with koffi and ctypes
- [ ] 10.4 Add `// @lat:` references from the bridge, shim and package native layers to their `lat.md` sections
- [ ] 10.5 Run `lat check` and fix every failure
- [ ] 10.6 Run `openspec validate m6-bindings-c-abi --strict` and fix every failure
