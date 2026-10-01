## Purpose

Defines the C ABI through which foreign languages reach the Lean build: a public header and one shared library per platform exporting five functions that take and return JSON text, with an exact memory, error and threading contract.

## ADDED Requirements

### Requirement: Five exported functions behind a self-contained header

The library SHALL export exactly the functions `tm_open`, `tm_call`, `tm_close`, `tm_free` and `tm_version`, declared in a public header `tiramemsu.h` that includes only standard C headers and compiles on its own as C99 and as C++17. Handles SHALL be the unsigned 64-bit integer type `tm_handle`, and `0` SHALL never be a valid handle. `tm_open(path, options_json, &handle, &out)` and `tm_call(handle, op, args_json, &out)` SHALL return the status `TM_OK` (0) on success and `TM_ERROR` (1) on failure; `tm_close(handle)` SHALL return `TM_OK` when it closed an open handle and `TM_ERROR` otherwise; `tm_version()` SHALL return a JSON text.

#### Scenario: Exported symbol set
- **WHEN** the dynamic symbol table of the shared library is listed on any supported platform
- **THEN** the only exported functions are `tm_open`, `tm_call`, `tm_close`, `tm_free` and `tm_version`

#### Scenario: Header stands alone
- **WHEN** a C99 file and a C++17 file that include only `tiramemsu.h` are compiled with no Lean headers on the include path
- **THEN** both compile without errors or warnings

### Requirement: JSON text in and out, owned by the caller

Every text argument SHALL be a NUL-terminated UTF-8 string; a NULL or empty `options_json` or `args_json` SHALL mean no options or no arguments. On success `tm_call` SHALL set `*out` to the result JSON text and `tm_open` SHALL set `*handle` to a new handle and `*out` to NULL. On failure both SHALL set `*out` to an error JSON text and `tm_open` SHALL set `*handle` to 0. Every non-NULL `char*` returned by any `tm_*` function SHALL be released by exactly one `tm_free` call, `tm_free(NULL)` SHALL do nothing, and no other memory SHALL be handed to the caller. If `handle` or `out` is NULL, the function SHALL perform no operation and return `TM_ERROR`. Returned text SHALL never contain a raw NUL byte. No Lean object SHALL be passed to or returned to the caller, and the library SHALL keep no pointer into caller memory after a call returns.

#### Scenario: Result ownership
- **WHEN** a caller runs `tm_call(h, "info", NULL, &out)`, parses `out` and calls `tm_free(out)`, ten thousand times
- **THEN** a leak checker reports no definitely lost bytes and no invalid free

#### Scenario: Caller buffer reused immediately
- **WHEN** a caller overwrites and frees its `op` and `args_json` buffers right after `tm_call` returns
- **THEN** later calls behave correctly and an address sanitizer reports no error

#### Scenario: Missing out pointer
- **WHEN** `tm_call(h, "info", NULL, NULL)` is called
- **THEN** it returns `TM_ERROR` and changes nothing

#### Scenario: Invalid UTF-8 argument
- **WHEN** `args_json` holds the bytes `{"text":"\xff"}`
- **THEN** `tm_call` returns `TM_ERROR` with an error whose `code` is `InvalidArgument`

### Requirement: Errors are JSON with a code

Every error text SHALL be a JSON object `{"code", "message"}` with string members. `code` SHALL be a code of the json-bridge capability, or one of the ABI codes `InvalidHandle` (the handle is not open) and `Internal` (the runtime failed to initialize, or the Lean side raised an unexpected exception). An error SHALL never terminate or abort the host process.

#### Scenario: Bridge error passes through
- **WHEN** `tm_call(h, "sparql", "{\"text\":\"SELECT ?\"}", &out)` is called
- **THEN** it returns `TM_ERROR` and `out` parses to an object whose `code` is `Parse`

#### Scenario: Unknown handle
- **WHEN** `tm_call` is called with a handle that was never returned by `tm_open`
- **THEN** it returns `TM_ERROR` with `code` `InvalidHandle`

### Requirement: Handle table

`tm_open` SHALL return a fresh handle for every successful open, and handles SHALL never be reused within a process. Several handles SHALL be allowed on the same file at once. After `tm_close(h)` succeeds, every later `tm_call(h, …)` SHALL fail with `InvalidHandle` and a second `tm_close(h)` SHALL return `TM_ERROR`. A call that is already running on `h` when `tm_close(h)` is called SHALL complete normally, and the database's connections SHALL be closed once no call uses it.

#### Scenario: Use after close
- **WHEN** a handle is closed and then used in `tm_call`
- **THEN** the call fails with `InvalidHandle` and the process does not crash

#### Scenario: Close during a call
- **WHEN** one thread runs a long query on `h` while another thread closes `h`
- **THEN** the query returns its full result, and a following call on `h` fails with `InvalidHandle`

#### Scenario: Handles are not recycled
- **WHEN** a handle is closed and a new database is opened
- **THEN** the new handle differs from every handle returned before

### Requirement: Runtime initialized exactly once

The library SHALL initialize the Lean runtime and its own modules exactly once per process, on the first call to any `tm_*` function, safely when that first call happens on several threads at the same time. If initialization fails, every later `tm_open` and `tm_call` SHALL fail with `Internal`. The library SHALL NOT require the host to call any initialization function.

#### Scenario: Racing first calls
- **WHEN** 32 threads call `tm_version` at the same moment as the first calls in a fresh process
- **THEN** every call returns the same version text and the runtime is initialized once

### Requirement: Foreign threads are registered before calling in

Any host thread SHALL be able to call any `tm_*` function. A thread unknown to the Lean runtime SHALL be registered with it before the call enters Lean, and its registration SHALL be released when the thread exits. Calls SHALL run on the calling thread and block until done. Calls from several threads on one handle SHALL be allowed: reads SHALL run in parallel, writes SHALL serialize, and every result SHALL equal the result of some serial order of the calls.

#### Scenario: Many threads on one handle
- **WHEN** 16 threads run 1 000 mixed `triples`, `sparql` and `transact` calls each on one handle under an address sanitizer
- **THEN** every call returns a valid result, the final store holds every committed statement once, and the sanitizer reports no error

#### Scenario: Short-lived threads
- **WHEN** 10 000 threads are created one after another, each makes one `tm_call` and exits
- **THEN** every call succeeds and the resident memory of the process stays bounded

#### Scenario: Small thread stacks
- **WHEN** threads created with a 512 KiB stack run the bridge conformance corpus through the ABI
- **THEN** every case passes

### Requirement: Version information

`tm_version()` SHALL return a JSON object with `abi` (the integer ABI version, 1 for this contract), `version` (the package version), `formatVersion` (the database format version, 1), `lean` (the Lean toolchain version) and `sqlite` (the linked SQLite version). Any incompatible change to the functions or their contract SHALL increase `abi`.

#### Scenario: Version object
- **WHEN** `tm_version()` is called and its text parsed
- **THEN** `abi` is 1, `formatVersion` is 1, and `version`, `lean` and `sqlite` are non-empty strings

### Requirement: One self-contained shared library per platform

The build SHALL produce one shared library for each of macOS arm64, macOS x86_64, Linux x86_64 (glibc), Linux aarch64 (glibc) and Windows x86_64, each with the Lean runtime, the `Tiramemsu` library and SQLite linked statically, and depending only on the platform's C runtime and system libraries. Symbols of the Lean runtime, libuv and SQLite SHALL NOT be exported, so the library can be loaded into a process that already contains another libuv or SQLite. Every statically linked component SHALL be listed with its licence in a notice file shipped beside the library.

#### Scenario: No foreign runtime dependency
- **WHEN** the dynamic dependencies of the Linux library are listed
- **THEN** they are limited to the C runtime, `libm`, `libpthread`, `libdl` and `librt` (or their merged glibc equivalents)

#### Scenario: Loaded next to another SQLite
- **WHEN** a Python process imports the standard `sqlite3` module and then loads the library and runs a query
- **THEN** both work, and the library reports its own SQLite version

### Requirement: The shim holds no logic

The hand-written C code SHALL be limited to runtime initialization, thread registration, copying text between caller memory and the Lean side, and freeing; every operation, every argument check and the handle table SHALL be implemented in Lean. Adding or changing a bridge operation SHALL NOT require a change to the C code.

#### Scenario: New operation without C changes
- **WHEN** the set of bridge operations changes
- **THEN** the C source file and header are unchanged and the new operation is reachable through `tm_call`

### Requirement: ABI test regime

Continuous integration SHALL run the ABI test program on every supported platform, under address and undefined-behaviour sanitizers on Linux and macOS, under a memory checker on Linux x86_64, and with Lean panics made fatal, covering every function, NULL and malformed inputs, stale handles, multi-threaded callers and open/close churn. Any sanitizer report, definitely lost block or panic SHALL fail the build.

#### Scenario: Leaked result is caught
- **WHEN** the test program is changed to skip one `tm_free`
- **THEN** the memory-checker job fails
