# Codec

Tier 0 of the proof plan (M1, `m1-verified-codec`): ObjectIds, literal canonicalization, the term dictionary and storage format 1, byte-compatible with the pinned Rust build.

Runtime code is in `src/Tiramemsu/Codec/`, `src/Tiramemsu/Term/` and `src/Tiramemsu/Storage/`; proofs in `TiramemsuProofs/Codec/` and `TiramemsuProofs/Term/`. See [[verification#Proven Codec Properties]] and [[decisions#D11 Doubles As Bits]].

## Errors

`CodecError` is `unsupported feature`, `invalidTerm reason` or `idSpaceExhausted kind`, with `IdKind` NODE, BNODE, STMT, TX, TERM.

Feature strings: `SEALED (M6)` for tag 15 and `origin <n>` for a non-zero origin, as the spec states (Rust appends ` (memory merge)`; errors compare by code only).

## ObjectId Layout

An `ObjectId` wraps the `Int64` stored in SQLite: `(payload << 4) | tag` with a 60-bit payload, read with an arithmetic shift for `INT`, `DATE`, `DATETIME` and a logical one otherwise.

`Tag` has 15 constructors (0–14); `Tag.ofBits` maps the low 4 bits to a tag. Construction is `ObjectId.ofPayload` (unsigned) and `ObjectId.ofSigned` (signed). Proven: tag and payload read back for every tag and 60-bit payload.

### Reserved Tag

Tag 15 (`SEALED`) has no constructor, so no value encodes to it; reading it is `Unsupported "SEALED (M6)"` on tag extraction and on decode.

## Origins And Allocation

`NODE`, `BNODE`, `STMT` and `TX` payloads are a 12-bit origin above a 48-bit counter (D15); format 1 allocates origin 0 only and rejects others on decode, on input and in skolems.

`alloc k n` succeeds exactly when `n ≤ 2^48 − 1`, with the origin-0 id of counter `n` and next counter `n + 1`; otherwise `IdSpaceExhausted`. Origin-0 counter order is signed id order.

## Inline Values

`INT`, `BOOL`, `DATE`, `DATETIME`, `SHORT_STR` and the allocated tags are inline: no dictionary row. Decoding is strict, so it accepts only ids some canonical value encodes to.

### Short Strings

Up to 7 UTF-8 bytes, big-endian in the high 56 payload bits, zero padding, the length in the low 4 bits; unpacking rejects a length above 7, non-zero padding and non-UTF-8 bytes.

## Literals

`literal lex dt lang` classifies an RDF literal and `Value.canonical` canonicalizes API values, following Rust's `Value::literal` and `Value::canonical`; ill-typed forms stay `TYPED` verbatim.

### Numbers

Integers canonicalize to the decimal of their value (`INT` in `[−2^59, 2^59 − 1]`, else `TYPED xsd:integer`); decimals to the normal form of their rational value (`0.0` for zero).

### Dates And Times

Day numbers use Hinnant's era algorithm over `Int` (`daysFromCivil`, `civilFromDays`), proven inverse on all integers and valid dates; timezone codes are `minutes + 841` (0 for none).

`DATETIME` payloads are `(ms << 11) | code`; `id >> 15` is the instant. The text parser and printer follow Rust and are tested, not proven.

### Doubles

`Double64` is the IEEE bit pattern. `parseDouble` rounds the exact decimal value to nearest-even in `Nat`, clamping the exponent first; `printDouble` searches 1–17 digits for the shortest decimal in the rounding interval.

Among equally short candidates the nearest wins; an exact tie takes the upper candidate, as Rust's `{:e}` does (found by the oracle). Output is Rust's `{:e}` with `.0` inserted and `E`. Specials: `NaN` (every NaN canonicalizes to `0x7FF8000000000000`), `INF`, `-INF`, `0.0E0`, `-0.0E0`.

The reference `roundBinary64 : Bool → ℚ → Double64` lives in the proof library; the printer's `roundingInterval` is the same interval the characterization theorem `round_eq_iff` describes.

## Skolem IRIs

`urn:tiramemsu:node|bnode|stmt|tx:<n>` with a canonical decimal: `1 ≤ n < 2^48` is the origin-0 id, `2^48 ≤ n < 2^60` is `Unsupported "origin <n >> 48>"`, anything else stays an IRI.

## Encoding

`encode v` canonicalizes and then yields an inline id or a `TermSpec` (tag, lexical form, datatype IRI, language, `num` bits); `decodeInline` and `valueFromTerm` invert it.

Proven: decode after encode and encode after decode are identities, decoding is injective, two values encode alike exactly when their canonical forms are equal, and inline kinds never reach the dictionary.

## Order And Ranges

Signed id order is value order within `INT` and `DATE`, (instant, code) order within `DATETIME`, and counter order for origin-0 allocated ids.

A value range on a signed tag is one id range `[(lo << 4) | T, (hi << 4) | T]` filtered by `id & 15 = T`; an instant range is `[(a << 15) | 7, (b << 15) | 0x7FF7]`. Both equivalences are proven.

## Term Dictionary

The pure model `Dict` (rows, `next`) keys terms by `(tag, lex, dt, lang)` coalesced as the `term_key` index compares; `intern` is lookup-or-append with `id = next`, bounded at `2^60 − 1`.

`internValue` interns the datatype IRI first, as Rust does; `lookupValue` never inserts; `decode` rebuilds the value from the row (a `DOUBLE` from its lexical form). Proven on the model: lookup after intern, idempotence, append-only rows, fresh ids, the bound, key and id uniqueness on reachable dictionaries, and the decode round trip.

The round-trip theorem `Dict.decode_internValue` takes the codec facts as the hypothesis `CodecLaws`, discharged by `Codec.codecLaws`, so the dictionary proofs use only standard axioms while the bit-level facts stay in the codec (D12).

### Caches And SQLite

`TermBackend` gives the model store and `SqliteStore` the same dictionary algorithms (`Term.intern`, `lookupValue`, `decode`), with Rust's lookup, insert and by-id SQL on SQLite.

The writer cache keeps a committed key/id map and a per-transaction overlay (merged on commit, dropped on rollback; capacity unbounded, `n` or off). Snapshot readers use an id → row LRU of committed rows. Caches never change results: `tiramemsu-tests terms` checks this against the proven model.

## Storage Format 1

The format-1 file is Rust's: same DDL text, never-forget triggers, `meta` counters and open rules, so either build opens the other's files.

### Schema

`Storage.ddlV1` is generated by `scripts/gen-ddl.py` from the pinned Rust `ddl_v1.sql`, split as Rust's `split_statements` splits it; CI fails on drift and diffs the schema rows against a Rust-created file.

### Meta And Open

`openFile` follows Rust: pragmas, `BEGIN IMMEDIATE`, create or check (`ForeignFile`, `FormatVersion`, missing counter), commit or roll back, then WAL. `meta` starts with the eight rows in Rust's order.

Format 1 has no migrations, so versions above and below 1 are both `FormatVersion`. A failed open leaves the file's bytes unchanged.

## Deviations

Every difference from the pinned Rust build is listed in the proposal and in `oracle/deviations.toml`.

- A `SHORT_STR` id with non-zero padding is rejected on decode; Rust ignores the padding.
- An allocated-tag id with a non-zero origin is rejected on decode as well as on input.
- `next_term` is bounded at `2^60 − 1`; Rust leaves it unbounded.
- No planner statistics: no `PRAGMA optimize` at open, no `sqlite_stat1`/`sqlite_stat4` written.
- The origin error's feature string is `origin <n>` (Rust: `origin <n> (memory merge)`).

## Differential Codec Oracle

`oracle codec` runs the Lean codec in process against `tm-core` behind the Rust driver (`codec*` operations); `oracle interchange` checks schema rows, term tables and decoded files in both directions.

Recorded full run (seed 42): 10,012,248 printed bit patterns, 1,150,987 parsed strings (1,000,000 random, up to 800 digits and 1,000-digit exponents), 200,000 each of literals, API values, dates, date-times and formatted values, 1,000,010 decoded ids (143,236 accepted strict-decoding deviations), 200,000 integers and decimals: zero mismatches. CI runs a smaller seed; nightly the full sizes. `oracle codec bench` reports parse and print throughput (report-only, D14).

## Tests

`tiramemsu-tests codec` checks every object-encoding and literal scenario value; `storage` the schema, triggers, open rules, reserved names and WAL; `terms` the dictionary refinement.

The refinement runs seeded intern/lookup/decode/commit/rollback sequences on the pure `Dict`, on `ModelStore` and on `SqliteStore` with the writer cache unbounded, at capacity 1 and off, and compares every result and the final `term` tables; NUL and non-BMP strings included.
