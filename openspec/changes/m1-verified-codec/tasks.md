## 1. Groundwork

- [ ] 1.1 Create the module files of design D-M1-1 under `Tiramemsu/` and `TiramemsuProofs/`, import them from both library roots, and check that `lake build` passes with empty stubs.
- [ ] 1.2 Define `CodecError` (`unsupported`, `invalidTerm`, `idSpaceExhausted`) and `IdKind` (`NODE`, `BNODE`, `STMT`, `TX`, `TERM`), with Rust's feature strings `SEALED (M6)` and `origin <n>`.
- [ ] 1.3 Add a codec mode to the M0 oracle harness that calls the pinned Rust `tm-core` functions: classify a literal, encode a value (inline id or term spec with `num` bits), `canonical_double`, `parse_double`, decode a raw id, and dump a file canonically. Smoke-test it on the Rust unit-test values.

## 2. ObjectId, tags and origins

- [ ] 2.1 Implement `Tag` (15 constructors, names, `ofBits` rejecting 15) and `ObjectId` over `Int64` (`mk`, `tagBits`, signed and unsigned payload).
- [ ] 2.2 Prove the layout and SEALED-rejection theorems. Register them in the theorem index and in the `bv_decide` allowlist.
- [ ] 2.3 Implement the origin/counter split and `alloc` with the 2⁴⁸ − 1 bound. Prove the split, origin-0 identity, non-zero-origin rejection and `alloc_ok_iff`, and register them.
- [ ] 2.4 Add unit tests for the object-encoding scenarios: `85`, `(42 << 4) | 3`, `(7 << 4) | 4`, negative `SHORT_STR` id, `origin 1` and `origin 3` errors, `STMT` at 2⁴⁸ − 1 and at 2⁴⁸.

## 3. Inline packings, order and ranges

- [ ] 3.1 Implement strict `SHORT_STR` pack/unpack (length ≤ 7, UTF-8, zero padding). Prove both round-trip directions and register them.
- [ ] 3.2 Implement timezone codes and `DATETIME` pack/unpack/instant. Prove the code bijection, both packing directions and `instant_encDT`, and register them.
- [ ] 3.3 Prove the order theorems for `INT`, `DATE`, `DATETIME` (instant, code) and origin-0 counters, and register them.
- [ ] 3.4 Implement the range bounds of design D-M1-5 (including `DATETIME` `| 7` / `| 0x7FF7`). Prove the bound equivalences and register them.
- [ ] 3.5 Add unit tests for the scenarios on malformed inline ids, NUL strings, offsets, and integer and instant ranges.

## 4. Calendar and date/time text

- [ ] 4.1 Implement `daysFromCivil`, `civilFromDays` and `validYMD` over `Int`. Prove both inverse directions and validity of `civilFromDays`, and register them.
- [ ] 4.2 Implement `parseDate`, `parseDateTime` (year rules, 24:00, fraction truncation, timezone validation), `formatDate` and `formatDateTime`.
- [ ] 4.3 Property-test the parse/format round trip on random in-range instants and offsets, and differential-test random date and date-time lexicals (±10⁶ years, invalid days, offsets ±14:01) against the oracle.

## 5. Integers, booleans and decimals

- [ ] 5.1 Implement `canonInteger` and the `INT` range rule. Prove idempotence, value preservation and the equality characterisation, and register them.
- [ ] 5.2 Implement `canonDecimal`. Prove its three laws against `decVal : String → ℚ`, and register them.
- [ ] 5.3 Differential-test random integer, boolean and decimal lexicals against the oracle.

## 6. Doubles

- [ ] 6.1 Implement `Double64` (bits, classification, canonical NaN `0x7FF8000000000000`). In `TiramemsuProofs`, define `toRat?` and the IEEE reference `roundBinary64`.
- [ ] 6.2 Implement the parser: Rust's syntax gate, the exponent clamp, and exact round-to-nearest-even in `Nat`/`Int`, with a Clinger fast path in `Nat`. Prove the clamp lemma and parser correctness against `roundBinary64`, and register them.
- [ ] 6.3 Prove the rounding-interval characterisation: a decimal parses to `x` iff it lies in `x`'s interval, with inclusive ends for even significands and the asymmetric gap at powers of two.
- [ ] 6.4 Implement the printer: the interval search for `k = 1 … 17` with a fuel-sufficiency lemma, `{:e}` digit/exponent formatting, the xsd rewrite, and the specials and signed zeros.
- [ ] 6.5 Prove `parse ∘ print` round trip (finite, and canonical for specials) and shortness, and register them.
- [ ] 6.6 Fuzz against the oracle: 10⁷ random bit patterns for printing; 10⁶ random decimal strings (up to 800 digits, huge exponents) for parsing; and the edge list (subnormal boundaries, powers of ten 1e-324 … 1e308, `MAX`, `MIN_POSITIVE`, smallest subnormal, ±0.0, ±∞, NaN, halfway cases). Zero mismatches are required.
- [ ] 6.7 Add a report-only benchmark of parse and print throughput against Rust (D14).

## 7. Values, skolems and encoding

- [ ] 7.1 Implement `Value`, literal classification, API canonicalization, `lexical` and `datatype`, following the literal-canonicalization spec.
- [ ] 7.2 Implement skolem render/parse, including the origin range. Prove both round-trip directions and register them.
- [ ] 7.3 Implement `encode` (inline or term spec with `num`), `decodeInline` and `valueFromTerm`. Prove `decode_encode`, `encode_decode`, `encode_eq_iff`, `decode_injective` and `inline_never_term`, and register them.
- [ ] 7.4 Differential-test classification and encoding of every spec edge literal and of random corpora of every kind against the oracle. Property-test lexical stability and canonicalization idempotence.

## 8. Term dictionary

- [ ] 8.1 Implement `TermKey` (coalesced comparison), `TermRow`, and the pure `Dict` with `lookup`, `intern` (bound 2⁶⁰ − 1), `internValue` (datatype IRI first) and `decode`.
- [ ] 8.2 Prove `lookup_intern`, `intern_idem`, `intern_append_only`, `fresh_id`, `ids_unique` (through the `WF` invariant) and `decode_internValue`, and register them.
- [ ] 8.3 Implement the dictionary operations on `SqliteStore` with Rust's lookup, insert and by-id SQL. Test interning NUL-containing and non-BMP strings, and fix the leansqlite pin if binding truncates.
- [ ] 8.4 Implement the writer cache (committed map plus per-transaction overlay, dropped on rollback) and the reader id→term LRU (committed rows only).
- [ ] 8.5 Add refinement tests: random intern/lookup/decode/commit/rollback sequences on `ModelStore` and `SqliteStore`, with cache capacity unbounded, 1 and 0. Include the rolled-back-term scenario and the term-row equality scenario against Rust.

## 9. Storage format

- [ ] 9.1 Add a script that generates `Storage/Ddl.lean` from the pinned Rust `ddl_v1.sql`, split as Rust's `split_statements` splits it. Check in the output, and add a CI step that fails on drift.
- [ ] 9.2 Implement `meta` counters, `INITIAL` in Rust order, and the missing-counter check.
- [ ] 9.3 Implement open as in design D-M1-9: pragmas, immediate transaction, init / foreign / version checks, rollback on error, then WAL.
- [ ] 9.4 Test the schema dump diff against a Rust-created file, each of the nine triggers with raw SQLite, the open rules (absent, zero-length, empty-schema, foreign, newer, older, missing counter, failed init), reserved names and the WAL pragma.
- [ ] 9.5 Test interchange in both directions with the oracle: Rust fixtures opened and dumped by Lean, Lean-created term files opened by Rust, with and without `sqlite_stat1`. Also check that a reopen leaves table dumps unchanged.

## 10. Close-out

- [ ] 10.1 Run the axiom audit. Every proven requirement of the four specs must have its theorem in the index, and only allowlisted codec theorems may use `Lean.ofReduceBool`.
- [ ] 10.2 Update `lat.md/`: add a codec and storage section covering the ObjectId layout with origin bits, literal canonicalization, the term dictionary, storage format 1 and this change's Rust deviations, and link it from `lat.md/lat.md`, `architecture.md` and `verification.md#Proof Tiers`.
- [ ] 10.3 Run `lat check` and fix every reported link or section error.
- [ ] 10.4 Run `openspec validate m1-verified-codec --strict` and fix until it passes.
