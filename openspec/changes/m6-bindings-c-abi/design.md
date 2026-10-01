## Context

See proposal.md (Why). By M5 the `Tiramemsu` library offers `Db`, `View` and `Tx` with SPARQL, Cypher, paths, bundles and speculation, and the M0 harness benchmarks it against the pinned Rust build. The Rust packages talk to Rust through one JSON bridge (`tiramemsu-json`) behind napi-rs and PyO3 classes named `Native` with `call(op, args) -> text`. Their wrappers (`lib/index.ts`, `python/tiramemsu/_db.py`) depend only on that class and on the `tiramemsu:{"code","message"}` error prefix.

Constraints: D1 (native through Lean's C backend, runtime linked statically), D7 (runtime library imports only Lean core and Std), D8 (SQLite only through leansqlite), D9 (one C file, no logic, koffi and ctypes), D10 (writer plus reader pool), D14 (gate before switching packages). Everything here is shell: Tier 4, trusted, tested (D2, verification.md).

## Goals / Non-Goals

**Goals:**
- The Rust wrappers and test suites run unchanged on the Lean backend; only the `Native` class underneath is replaced.
- The C surface is small enough to audit in one sitting and cannot leak or double-free when used as documented.
- Bridge conformance is checked mechanically against the Rust bridge, not by reading code.

**Non-Goals:**
- No proofs. No requirement in this change is proven, so there are no theorem statements; the JSON codec and the bridge are property- and differential-tested.
- No async API, no new bridge operations, no WASM or MCP binding, no SQL table functions (D8, overview Non-Goals).
- No `musllinux` wheel, no Python sdist, no 32-bit or FreeBSD targets.
- No Lean runtime shutdown: the runtime lives until process exit.

## Decisions

### 1. Module layout

```
abi/tiramemsu.h            public header: stdint.h + stddef.h only
abi/tiramemsu.c            ~150 lines: init once, thread registration, marshalling
abi/exports.{map,txt,def}  symbol lists: GNU ld version script, macOS list, Windows .def
Tiramemsu/Bridge/Json.lean       JSON value, parser (depth limit), printer
Tiramemsu/Bridge/Term.lean       term <-> JSON, time and eid arguments, Cypher params
Tiramemsu/Bridge/View.lean       view object -> View
Tiramemsu/Bridge/Read.lean       read operations and result JSON
Tiramemsu/Bridge/Tx.lean         transact, cypherWrite, with, op application, refs
Tiramemsu/Bridge/Error.lean      BridgeError, code names, error JSON
Tiramemsu/Bridge/Database.lean   open (options), call, callText
Tiramemsu/Bridge/Handles.lean    handle table
Tiramemsu/Bridge/Export.lean     @[export] entry points used by the shim
bindings/node/                   wrapper from pinned Rust + lib/native.ts (koffi)
bindings/python/                 wrapper from pinned Rust + tiramemsu/_native.py (ctypes)
conformance/bridge/              case corpus, Rust runner, Lean runner, ABI runner
bench/gate/                      thresholds.json, gate evaluator, report renderer
```

The `Bridge` modules are unverified shell modules, so `@[export]`, `partial` and IO are allowed there (verification.md Proof Policy restricts verified modules only).

### 2. Key types

```lean
inductive JNum | int (i : Int)      -- literal without fraction/exponent, -2^63 ≤ i < 2^64
              | dbl (bits : UInt64) -- every other finite number, correctly rounded (D11 parser)
inductive Json | null | bool (b : Bool) | num (n : JNum) | str (s : String)
               | arr (xs : Array Json) | obj (kvs : Array (String × Json))
inductive BridgeError | db (e : Tiramemsu.Error) | arg (msg : String)
                      | handle (h : UInt64) | internal (msg : String)
def BridgeError.code : BridgeError → String   -- variant name | "InvalidArgument" | "InvalidHandle" | "Internal"
structure Database where db : Db               -- one open store with writer + reader pool (D10)
def Database.open (path : String) (opts : Json) : IO (Except BridgeError Database)
def Database.call (d : Database) (op : String) (args : Json) : IO (Except BridgeError Json)
def Database.callText (d : Database) (op : String) (args : ByteArray) : IO (Except String String)
```

`JNum` mirrors serde_json without `arbitrary_precision`: an integer literal that fits `i64` or `u64` stays an integer; anything else becomes `f64`. This reproduces Rust's classification exactly (an integer literal above `u64::MAX` is a double; above `i64::MAX` it is not a valid `xsd:integer` term and becomes a double too, as in Rust).

Alternative rejected: `Lean.Data.Json`. It lives in the `Lean` package, which would link the compiler library into the shared library (tens of MB) and stretch D7's "Lean core and Std"; its number type also loses the integer/double distinction the term rules need.

### 3. ABI shape

```c
typedef uint64_t tm_handle;                       /* 0 is never a valid handle */
int   tm_open (const char *path, const char *options_json, tm_handle *handle, char **out);
int   tm_call (tm_handle h, const char *op, const char *args_json, char **out);
int   tm_close(tm_handle h);
void  tm_free (char *p);
char *tm_version(void);
#define TM_OK 0
#define TM_ERROR 1
```

Status plus out-parameter rather than an envelope `{"ok"|"err"}`: the wrappers already expect "result text or error text", so an envelope would cost a second parse and re-serialization of every result. koffi (`_Out_ char **`) and ctypes (`POINTER(c_void_p)`) both handle out-pointers. Strings returned are `malloc`ed copies of the Lean string bytes; `tm_free` is `free`. Inputs are copied into a Lean `ByteArray`, and UTF-8 validation happens in Lean (`String.fromUTF8?`), so the C file never interprets text.

Lean exports return `UInt32 × String` (call) and `UInt64 × String` (open); the shim reads the two fields, copies the string, and drops the Lean reference before returning. No `lean_object*` is ever stored in C or returned to the caller.

### 4. Handle table in Lean, not in C

architecture.md says the shim "keeps a handle table". The table is put in Lean instead: a global `IO.Ref (Std.HashMap UInt64 Database)` guarded by a `Std.Mutex`, with a monotonic counter starting at 1, so handles are never reused. A C table would have to hold `lean_object*` across calls and manage reference counts and multi-threaded marking in C, which is exactly the logic D9 keeps out of the shim. `tm_close` removes the entry; a call already in flight keeps its own reference and finishes, and the connections close when the last reference drops. **Not covered by D1–D15**; `lat.md/architecture.md#C ABI` is updated in task 10.

Alternative rejected: pointer handles (`tm_db*`). They make use-after-close undefined behaviour instead of an `InvalidHandle` error.

### 5. Runtime initialization and threads

`init_once` runs under `pthread_once` (POSIX) or `InitOnceExecuteOnce` (Windows): `lean_initialize_runtime_module()`, the `Tiramemsu.Bridge.Export` module initializer, `lean_io_mark_end_initialization()`, `lean_init_task_manager()` (D10 queries use Lean tasks). If the module initializer fails, a flag makes every later call return an `Internal` error.

Every entry point first checks a thread-local flag; an unregistered thread calls `lean_initialize_thread()` and arms a pthread key destructor (POSIX) or an FLS callback (Windows) that calls `lean_finalize_thread()` at thread exit. The initializing thread is marked registered by `init_once`. Calls run on the caller's thread and block; a `Database` is shared by all threads, reads run in parallel on the reader pool, writes serialize on the writer mutex (D10).

Alternative rejected: run every call on a Lean task and wait. It isolates foreign stack sizes, but costs a thread hand-off per call, which the point-lookup gate (≤2×) cannot afford. Small stacks are handled by test (risk below).

### 6. Shared library build

Lake builds `Tiramemsu` as a static library; a Lake target links `abi/tiramemsu.c`, `libTiramemsu.a`, leansqlite's static archive (with the SQLite amalgamation), `libInit`, `libStd` and `libleanrt` (with libuv and the allocator) into `libtiramemsu.dylib` / `libtiramemsu.so` / `tiramemsu.dll`, using the toolchain's bundled clang and lld. Only `tm_*` are exported: `-fvisibility=hidden`, a version script and `--exclude-libs,ALL` plus `-Bsymbolic` on Linux, `-exported_symbols_list` on macOS, a `.def` file on Windows. Hiding matters: Node.js embeds its own libuv and Python's `sqlite3` module its own SQLite, and a flat-namespace clash would bind one to the other. Linux targets the glibc baseline of the pinned Lean toolchain, recorded as the wheel's manylinux tag; macOS targets 11.0.

Before the first release a license audit lists every statically linked component. If the pinned toolchain's runtime contains GMP (LGPL), `leanrt` is rebuilt from the pinned toolchain sources with GMP disabled, so the shipped binary is MIT/Apache/BSD/public-domain only. **Not covered by D1–D15.**

### 7. Node.js package

`bindings/node` is the pinned Rust package with two changes: `lib/native.ts` (new) implements `Native` with koffi, and the `loadNative()` block of `lib/index.ts` imports it instead of `require`-ing a `.node` addon. Everything else in `lib/` and all of `test/` must stay byte-identical to the pinned Rust commit; CI checks this with a hash list. `Native` throws `Error("tiramemsu:" + errorJson)` like napi did, registers each instance with a `FinalizationRegistry` that calls `tm_close`, and checks `tm_version().abi === 1` at load. Prebuilt libraries ship in one package under `prebuilds/<platform>-<arch>/`, the same one-package layout as the Rust release; koffi brings its own prebuilt binaries, so install runs no compiler and no install script. The Lean-backed release keeps the name `@tiramemsu/node` and takes the next minor version after the last Rust-backed release. **Version policy not covered by D1–D15.**

Alternative rejected: per-platform optional-dependency packages (esbuild style). Smaller installs, but five more npm packages to publish and a different release layout; revisit only if the package size measured in task 7 exceeds 100 MB unpacked.

### 8. Python package

`bindings/python` is the pinned Rust package with `tiramemsu/_native.py` (ctypes) replacing the PyO3 extension module; `_db.py`, `_types.py`, `__init__.py` and `tests/` stay byte-identical (hash-checked). `ctypes.CDLL` releases the GIL during foreign calls, which keeps the threads test passing. `Native.__init__` raises `RuntimeError("tiramemsu:" + errorJson)` and a `weakref.finalize` closes the handle; `Database.close()` stays a no-op, as in Rust. The `.pyi` stub is kept identical so `mypy --strict` sees the same types. Wheels are `py3-none-<platform>` (the library does not link libpython) built with a plain build backend (hatchling) that copies the prebuilt library into `tiramemsu/_lib/`. No sdist is published, because building from source needs the Lean toolchain. **Wheel tag and sdist policy not covered by D1–D15.**

### 9. Bridge conformance

`conformance/bridge/cases/<rust_test_name>.json` holds one case per `#[test]` in the pinned `bindings/json/tests/bridge.rs`: a list of steps `{open | call, args, expect?, expectError?}`, where `expect` is a JSON subset pattern transcribing the Rust assertions. Three runners execute the corpus: a Rust runner (Cargo crate under `conformance/bridge/rust-runner`, depending on `tiramemsu-json` at the pinned git revision), a Lean runner (`lake exe bridge-conformance`), and an ABI runner (the same corpus through `libtiramemsu` with ctypes). Each runner checks the `expect` patterns; then the Lean and ABI transcripts are compared with the Rust transcript after canonicalization: JSON compared structurally (member order ignored, numbers by exact value), report `instant` and `info.path` masked, errors compared by `code` only. A coverage script fails if a `#[test]` name at the pinned commit has no case file. A differential fuzzer generates random op lists and reads (terms, views, refs, bad arguments) and compares the two bridges the same way.

### 10. Performance gate

`bench/gate/thresholds.json` holds the D14 thresholds. The gate job runs the M0 harness with both builds on a dedicated Linux x86_64 runner, same machine and same run: read workloads use one 10⁶-statement file generated with a fixed seed and opened by both builds (the shared format makes this possible, D6); write workloads start from an empty file on each build. Each workload is 2 warm-up runs and at least 10 measured runs; the ratio is median(Lean) / median(Rust). The evaluator writes `gate.json` and `gate.md`; the release workflow's publish jobs depend on it, and there is no override flag. macOS arm64 results are produced and published as report-only. A binding-overhead check (a `triples` point lookup through each package, Lean-backed vs Rust-backed, ≤2×) is added to the D14 list so a slow JSON path cannot hide behind fast engine numbers. **Gating machine and binding-overhead threshold not covered by D1–D15.**

### 11. Test strategy (all requirements are tested, none proven)

| Capability | Tests |
|---|---|
| c-abi | C test program (`abi/test/`): every function, NULL and bad-UTF-8 inputs, stale handles, 16 threads × mixed reads/writes on one handle and on several, threads with 512 KiB stacks, open/close churn; run under ASan+UBSan (Linux, macOS) and valgrind memcheck (Linux x86_64, zero "definitely lost"); a 10⁵-call loop with bounded RSS growth (catches Lean reference leaks that valgrind cannot see through the Lean allocator); `nm`/`dumpbin` export check; header compiled alone as C99 and C++17; `LEAN_ABORT_ON_PANIC=1` everywhere so a panic fails the test |
| json-bridge | corpus on Lean, Rust and ABI runners; differential fuzzer; JSON codec property tests (parse ∘ print = id, number classification, depth limit) |
| node-binding | pinned Rust vitest suite, `tsc --strict`, `.d.ts` API diff against pinned Rust is empty, pack test (five libraries present), install with `--ignore-scripts` on each platform |
| python-binding | pinned Rust pytest suite, `mypy --strict`, public-name diff against pinned Rust, `auditwheel`/`delocate` checks, smoke install of each wheel |
| performance-gate | evaluator unit tests on synthetic results (pass, each threshold failing, missing workload) |

## Risks / Trade-offs

- [Foreign threads with small stacks (macOS secondary threads default to 512 KiB) overflow in deep Lean recursion] → JSON depth limit 128; ABI test on 512 KiB threads; if it fails, move the work of `tm_call` onto a Lean dedicated task, accepting the latency.
- [The Lean runtime installs signal handlers that interfere with Node.js or Python `faulthandler`] → package suites run with `faulthandler` enabled and under Node's default handlers on all five platforms; any conflict blocks the release.
- [Lean objects shared across threads not marked multi-threaded, causing refcount races] → databases enter the handle table through an `IO.Ref` (which marks stored values MT); the 16-thread ASan test and the RSS loop target this.
- [Symbol clash with host libuv or SQLite] → only `tm_*` exported; CI export check; package suites load the library next to Node's libuv and Python's `sqlite3`.
- [Package size: five static Lean-runtime libraries in one npm package] → measured in the pack test; above 100 MB unpacked, switch to per-platform optional dependencies (no API change).
- [GMP licence in the static runtime] → licence audit task and GMP-free `leanrt` rebuild if needed.
- [Gate noise near a threshold] → medians of ≥10 runs on a dedicated runner; IQR published; a failing gate is fixed by optimization or by an OpenSpec change to the thresholds, never by a waiver.
- [JSON parsing in Lean is slower than serde_json and dominates small calls] → binding-overhead check in the gate; the parser works on `ByteArray` without intermediate `String` copies.

## Migration Plan

1. Release the Lean-backed packages as the next minor version under the same names once the gate passes; release notes link the gate report and list the deviations from json-bridge.
2. Database files need no migration: both builds read and write format 1 (D6).
3. Rollback: users pin the previous Rust-backed version; files written by the Lean build stay readable by it.
