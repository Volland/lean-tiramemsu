## Why

Every later milestone compares ObjectIds as integers, scans index ranges by id, and reads or writes the Rust file format. M2's store proofs and M3's query proofs are only as strong as the claim that one value has exactly one id and that id order is value order. M1 makes the codec Tier 0 of the proof plan (D2, verification.md#Proof Tiers). It is also where Lean first meets a real `.db` file, so it fixes byte-level compatibility with Rust format 1 (D6) before any write path exists.

## What Changes

- ObjectId as a signed 64-bit value `(payload << 4) | tag`, with all 16 tags as in Rust and tag 15 `SEALED` rejected. The `STMT`, `NODE`, `BNODE` and `TX` payloads split into a 12-bit origin and a 48-bit counter (D15). Format 1 writes origin 0, rejects non-zero origins on input, and bounds counters at 2⁴⁸ − 1 with a typed error.
- Proven inline codec: encode/decode round trip per tag, decode injective, signed order kept within a tag, range-scan bounds, `DATETIME` packing and instant extraction (`id >> 15`), `SHORT_STR` packing, origin/counter split, skolem IRI round trip. `bv_decide` is allowed here under the CI allowlist (D12).
- Literal canonicalization behaving like Rust: integers, booleans, dates and date-times (proven civil-calendar inverse), `xsd:decimal` canonical form, and `xsd:double` held as IEEE bits (D11). Doubles get a correctly rounded exact parser and a shortest round-trip printer, both proven, whose output is fuzz-tested to be byte-identical to Rust's canonical form.
- The term dictionary: `(tag, lex, dt, lang)` keys, `num` for doubles and decimals, intern on write, lookup-only reads, ids never reused, immutable rows, an append-only cache. Its laws are proven on a pure dictionary model, and `SqliteStore` is refinement-tested against that model.
- Storage format 1 on SQLite through leansqlite (D8). The schema DDL and never-forget triggers are byte-identical to Rust. This change also covers `meta` counters, the `format_version` open rules, and cross-implementation file compatibility tested against the pinned Rust oracle.
- **Deviations from Rust (D6)**, each specified and tested:
  - A `SHORT_STR` id with non-zero bytes beyond its length is rejected on decode. Rust ignores the padding, so two raw ids decode to one string. Rust never writes such ids.
  - An inline `NODE`/`BNODE`/`STMT`/`TX` id read from a file with a non-zero origin is rejected on decode, as well as on input.
  - `next_term` is bounded at 2⁶⁰ − 1 with `IdSpaceExhausted { kind: TERM }`. Rust leaves it unbounded.
  - The Lean build writes no SQLite planner statistics (`sqlite_stat1`/`sqlite_stat4`). These are outside the format, and Lean evaluates no SQL (D3).

## Capabilities

### New Capabilities
- `object-encoding`: the ObjectId layout, tags, origin/counter split, inline encode/decode, canonical uniqueness, order within a tag, range-scan bounds, `DATETIME` and `SHORT_STR` packing, skolem IRIs.
- `literal-canonicalization`: how RDF literals and API values map to one canonical value: integers, booleans, `xsd:date`/`xsd:dateTime` (with timezone codes, truncation and range rules), `xsd:decimal`, and `xsd:double` as IEEE bits with a correctly rounded parser and shortest printer.
- `term-dictionary`: the term table contract: keys, `dt`/`lang`/`num` columns, intern and lookup semantics, id allocation, immutability, decoding dictionary ids, and caching.
- `storage-format`: format-1 schema and trigger text, connection pragmas, `meta` keys and counters, open rules (create, foreign, newer, older), reserved names, and file interchange with Rust.

### Modified Capabilities
<!-- none: there are no existing specs -->

## Impact

- **Code:** new `Tiramemsu.Codec.*` (ObjectId, values, literals, doubles, decimals, calendar, short strings, skolems), `Tiramemsu.Term.*` (dictionary model and keys), and `Tiramemsu.Storage.*` (format-1 DDL, meta, open). Also new `TiramemsuProofs.Codec.*` and `TiramemsuProofs.Term.*`, and the format-1 open path of `SqliteStore`.
- **Proof policy:** first entries in the theorem index and in the `bv_decide` allowlist (D7, D12).
- **Oracle:** codec and file-interchange modes in the differential harness from M0, run against the pinned Rust build (D6). Needs the Rust `reserve-replica-id` change landed before the pin (D15).
- **Dependencies:** M0 (Lake libraries, CI proof gates, `Store` interface, leansqlite pin). Unblocks M2, which needs canonical ids, counters and the open path.
- **Not in scope:** statement writes, transactions and retraction (M2), query evaluation and `term.num` range filters (M3), JSON bridge error names (M6).
