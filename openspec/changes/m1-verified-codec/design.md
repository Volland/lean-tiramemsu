## Context

M0 delivers the Lake project with the `Tiramemsu` (core + Std only) and `TiramemsuProofs` (may import Mathlib) libraries, the CI proof gates (no `sorry`, axiom audit, theorem index, `bv_decide` allowlist), the `Store` interface with `ModelStore`/`SqliteStore` stubs, the leansqlite pin and the Rust oracle harness. M1 fills in the lowest layer, the one every later proof stands on.

The Rust reference behaviour is in `tm-core` (`id.rs`, `codec.rs`, `value.rs`, `term.rs`, `storage/ddl_v1.sql`, `storage/mod.rs`, `storage/meta.rs`, `storage/migrate.rs`), plus the pending `reserve-replica-id` change (D15). The specs of this change restate that behaviour fresh (D5) and list every deviation (D6).

## Goals / Non-Goals

**Goals:**
- One total, pure Lean definition per codec function, with the proof about that exact definition. No `partial`, and no `implemented_by` without `@[csimp]` (D7).
- Rust-identical observable output: ObjectIds, term rows (`tag`, `lex`, `dt`, `lang`, `num` bits), canonical lexical forms, `sqlite_schema` text.
- A pure dictionary model whose laws M2 reuses when it proves never-forget for terms.

**Non-Goals:**
- Fast-path float algorithms (Ryu, Eisel–Lemire). They can arrive later behind `@[csimp]` with an equality proof, if benchmarks ask for it (D14).
- Proofs of the textual date/time parser and formatter. They are tested; only the arithmetic underneath is proven.
- Proof that printed doubles are the *closest* of the shortest candidates, and tie-breaking. Byte identity with Rust covers these by test.
- Statement allocation in transactions, savepoints, burned ids (M2). M1 provides the pure allocation step and the bound.

## Decisions

### D-M1-1 Module layout

```
Tiramemsu/Codec/Tag.lean          Tag (15 ctors), names, ofBits? (SEALED → error)
Tiramemsu/Codec/ObjectId.lean     ObjectId := ⟨raw : Int64⟩, mk, tagBits, payload (signed/unsigned)
Tiramemsu/Codec/Origin.lean       AllocTag, origin/counter split, alloc, IdSpaceExhausted
Tiramemsu/Codec/ShortStr.lean     pack / unpack (strict)
Tiramemsu/Codec/Civil.lean        daysFromCivil / civilFromDays / validYMD
Tiramemsu/Codec/DateTime.lean     TzCode, pack / unpack, parseDate, parseDateTime, format*
Tiramemsu/Codec/Integer.lean      canonInteger, INT range
Tiramemsu/Codec/Decimal.lean      canonDecimal
Tiramemsu/Codec/Double/Bits.lean  Double64 := ⟨bits : UInt64⟩, classify, canonical NaN
Tiramemsu/Codec/Double/Parse.lean exact correctly-rounded parser
Tiramemsu/Codec/Double/Print.lean shortest printer + Rust `{:e}` → xsd form
Tiramemsu/Codec/Value.lean        Value, literal, canonical, lexical, datatype
Tiramemsu/Codec/Skolem.lean       render / parse
Tiramemsu/Codec/Encode.lean       Encoded := inline ObjectId | term TermSpec; encode, decodeInline, valueFromTerm
Tiramemsu/Codec/Range.lean        lowerBound / upperBound per signed tag, DATETIME instant bounds
Tiramemsu/Term/Key.lean           TermKey (coalesced dt/lang), TermRow
Tiramemsu/Term/Dict.lean          pure Dict model: lookup, intern, byId
Tiramemsu/Term/Cache.lean         append-only committed cache + tx overlay (shell, unverified)
Tiramemsu/Storage/Ddl.lean        format-1 statement list (generated, see D-M1-8)
Tiramemsu/Storage/Meta.lean       Counters, INITIAL
Tiramemsu/Storage/Open.lean       open/init/format check on SqliteStore
TiramemsuProofs/Codec/*.lean, TiramemsuProofs/Term/Dict.lean   (one file per runtime module)
```

The modules under `Codec/` and `Term/Key|Dict` are verified modules (totality and attribute rules from the proof policy apply). `Term/Cache` and `Storage/*` are shell code, tested only.

### D-M1-2 Key types

- `ObjectId` wraps `Int64`, so SQLite's signed `INTEGER` and Lean agree with no conversion. Proofs work on `raw.toBitVec : BitVec 64` (for `bv_decide`) or on `raw.toInt` (for `omega`/order).
- `Tag` is an inductive with 15 constructors. Tag 15 has no constructor: `Tag.ofBits : BitVec 4 → Except CodecError Tag` returns `unsupported "SEALED (M6)"` for 15. So no well-typed `Value` can ever carry `SEALED`.
- Payloads: `BitVec 60`. Signed tags read it with `BitVec.toInt`, unsigned ones with `toNat`. `AllocTag := node | bnode | stmt | tx`. `payload = origin ++ counter` with `origin : BitVec 12` and `counter : BitVec 48`.
- `Double64 := ⟨bits : UInt64⟩` (D11). Its numeric meaning lives only in proofs: `Double64.toRat? : Double64 → Option ℚ`, in `TiramemsuProofs`, using Mathlib's `ℚ`. Runtime code never uses `Float`, except where `SqliteStore` binds `num` as REAL through `Float.ofBits` (shell).
- `Value` mirrors the Rust enum. Differences: `int : Int` is unbounded, so Lean-API values beyond `i64` canonicalize to `TYPED xsd:integer` like Rust's big-integer path. `double : Double64`. `dateTime (ms : Int) (tz : Option Int)`.
- Errors: `CodecError := unsupported (feature : String) | invalidTerm (reason : String) | idSpaceExhausted (kind : IdKind)`. The `feature` strings are Rust's: `"SEALED (M6)"` and `"origin <n>"`.

### D-M1-3 Strict decoding, so decode is injective

`decodeInline` rejects every raw id that no canonical value encodes to: tag 15, `BOOL` payload > 1, `DATETIME` timezone code > 1681, `SHORT_STR` length > 7, non-UTF-8 or non-zero padding, and a non-zero origin on an allocated tag. With that, `encode ∘ decode = id` on the accepted ids, so decode is injective, and value equality is integer equality without side conditions.
*Alternative:* decode leniently like Rust (ignore `SHORT_STR` padding). Rejected, because then injectivity holds only on a "well-formed" predicate that every downstream theorem would carry. The two strictness points Rust lacks are listed deviations (proposal); Rust never writes such ids, and the oracle confirms it on Rust-written fixtures.

### D-M1-4 Doubles: exact arithmetic, proven, no float hardware

- **Parser.** A syntax check identical to Rust's `parse_double` gate. The decimal `m · 10^q` is held as `Nat × Int` and rounded to binary64 with round-to-nearest, ties-to-even. That covers subnormals, overflow to ±∞ at or beyond `MAX + ½ ulp`, and underflow to ±0. The exponent is clamped before any power is formed. With `n` significant digits, `n + q > 310` gives ±∞ and `n + q < -324` gives ±0, with a lemma that the clamp does not change the rounded result. So `1e999999999999` costs no memory.
- **Printer.** For finite nonzero `x`, compute the rounding interval of `x` under *our parser*: midpoints to the neighbours, with endpoints included iff the significand is even, and the asymmetric lower gap at powers of two. Then for `k = 1 … 17` (fuel 17, with a theorem that 17 suffices), take the `k`-digit decimal in the interval closest to `x`; the first `k` that has one wins. Format it as Rust's `{:e}` does (`d[.ddd]e[-]n`), then rewrite to the xsd form (`.0` inserted when there is no fraction, `e` → `E`). Zero prints `0.0E0` or `-0.0E0`. Specials print `INF`, `-INF` and `NaN`.
- *Alternatives:* Ryu or Grisu with 128-bit tables (fast, but a large proof over tables), or hardware `Float` plus libc `strtod`/`printf` (unverifiable, and not byte-identical across platforms). Rejected for M1. A faster implementation can replace either function later through `@[csimp]` with an equality theorem.

### D-M1-5 Range-scan bounds

A signed-tag value `v` gives bounds `lower T v = (v << 4) | T` and `upper T v = (v << 4) | T`, inclusive. Together with a filter on `raw & 15 = T`, these select exactly the ids of tag `T` with value in range. For `DATETIME` instants the bounds are Rust's: `lo ms = (ms << 15) | 7` and `hi ms = (ms << 15) | 0x7FF7`. Proving these once lets M3 range scans use them with no side conditions.

### D-M1-6 Term dictionary as a pure model plus a shell cache

`Dict := { rows : Array TermRow, next : Nat }`. `lookup` searches by coalesced key `(tag, lex, dt.getD 0, lang.getD "")`, exactly as `term_key` compares. `intern` is lookup-or-append with `id = next`, and fails with `idSpaceExhausted TERM` past 2⁶⁰ − 1. `internValue` interns the datatype IRI first, then the term, so id order matches Rust. `SqliteStore` implements the same operations with the SQL of the Rust `term.rs` (`LOOKUP_SQL`, `INSERT_SQL`, `BY_ID_SQL`). The writer cache is a committed map plus a per-transaction overlay, dropped on rollback; readers use an id→term LRU. Since terms are immutable, no cache entry is ever invalidated, only evicted. The cache sits in the shell and is covered by refinement tests: the same results with the cache on, off, and size 1.
*Alternative:* prove the cache. Rejected: it is performance-only and lives outside the pure core (architecture.md#Concurrency).

### D-M1-7 Origin bits and allocation

`alloc (k : AllocTag) (next : Nat) : Except CodecError (ObjectId × Nat)` returns `(mk k (0 ++ next), next + 1)` when `next ≤ 2⁴⁸ − 1`, else `idSpaceExhausted k`. M2 calls it inside transactions and owns "leaves no trace". Skolem parsing distinguishes three cases for the decimal `n`:
- `1 ≤ n < 2⁴⁸`: the id.
- `2⁴⁸ ≤ n < 2⁶⁰`: `unsupported "origin <n >> 48>"`.
- Otherwise (0, leading zeros, ≥ 2⁶⁰, non-digits): an ordinary IRI.

### D-M1-8 DDL text is generated from Rust, not retyped

`Storage/Ddl.lean` holds the format-1 statements as the list Rust's `split_statements(DDL_V1)` produces. That list is what SQLite stores in `sqlite_schema.sql`: comments stripped, trigger bodies whole. A small task script regenerates the Lean file from the pinned Rust source, and a CI test diffs `SELECT type, name, tbl_name, sql FROM sqlite_schema ORDER BY rowid` between a Rust-created and a Lean-created fresh file.
*Alternative:* port `split_statements` to Lean and embed `ddl_v1.sql`. Rejected: that duplicates a parser whose only job is to reproduce one constant.

### D-M1-9 Open path

Open follows Rust's order:
1. Writer connection with `synchronous = NORMAL` and `recursive_triggers = ON`.
2. `BEGIN IMMEDIATE`.
3. Count objects in `sqlite_schema` other than `sqlite_*`. Zero means run the DDL and insert `meta` INITIAL in order. Otherwise a missing `meta` table or `format_version` row is `ForeignFile`; a newer version is `FormatVersion`; an older one runs migrations, of which format 1 has none.
4. `COMMIT`, or `ROLLBACK` on error.
5. `journal_mode = WAL`.

There is no `PRAGMA optimize` (proposal deviation): Lean issues only index range scans with forced indexes, so SQLite's planner statistics never matter to it. A Lean-written file opened by Rust is analysed by Rust's own open.

### Theorem statements (proven requirements)

Informal statement, then a Lean-ish signature. Every theorem is registered in the theorem index under its spec requirement. `[bv]` marks those on the `bv_decide` allowlist (D12).

**object-encoding**
- Tag/payload layout `[bv]`: `∀ t p, (mk t p).tagBits = t.toBits ∧ (mk t p).payload = p`, and `(x.raw &&& 15 = 15) → Tag.ofBits x.tagBits = .error (.unsupported "SEALED (M6)")`.
- Round trip `[bv]`: `decode_encode : v.Canonical → v.Inline → decodeInline (encodeInline v) = .ok v`; `encode_decode : decodeInline x = .ok v → encodeInline v = x`.
- Canonical uniqueness: `encode_eq_iff : encode v = encode w ↔ v.canonical = w.canonical`; `decode_injective : decodeInline x = .ok v → decodeInline y = .ok v → x = y`; `inline_never_term : v.canonical.Inline → ∃ x, encode v = .inline x`.
- Order `[bv]`: `int_lt_iff : inIntRange a → inIntRange b → (a < b ↔ (encInt a).raw < (encInt b).raw)`; the same for `DATE`; `datetime_lt_iff : (ms₁, c₁) <ₗₑₓ (ms₂, c₂) ↔ (encDT ms₁ c₁).raw < (encDT ms₂ c₂).raw`; `counter_lt_iff : c₁ c₂ < 2⁴⁸ → (c₁ < c₂ ↔ (alloc k c₁).id.raw < (alloc k c₂).id.raw)`.
- Instant `[bv]`: `instant_encDT : (encDT ms c).raw >>> 15 = ms` (arithmetic shift).
- Range bounds `[bv]`: `x.tagBits = T → (lower T a ≤ x.raw ∧ x.raw ≤ upper T b ↔ a ≤ val x ∧ val x ≤ b)`; for `DATETIME`, `lo a ≤ x.raw ∧ x.raw ≤ hi b ↔ a ≤ instant x ∧ instant x ≤ b`.
- DateTime packing `[bv]`: `unpackDT (packDT ms tz) = .ok (ms, tz)` for `-2⁴⁸ ≤ ms < 2⁴⁸` and a valid tz; `unpackDT p = .ok (ms, tz) → packDT ms tz = p`; `tzCode_inj`.
- Short strings `[bv]`: `s.utf8ByteSize ≤ 7 → unpackShort (packShort s) = .ok s`; `unpackShort p = .ok s → packShort s = p`.
- Origin `[bv]`: `origin (mkAlloc k o c) = o ∧ counter (mkAlloc k o c) = c`; `mkAlloc k 0 c = mk k (c.zeroExtend 60)`; `origin x ≠ 0 → decodeInline x = .error (.unsupported _)`; `alloc_ok_iff : (alloc k n).isOk ↔ n ≤ 2⁴⁸ - 1`.
- Skolem: `1 ≤ c < 2⁴⁸ → parseSkolem (renderSkolem (mkAlloc k 0 c)) = .ok (some (mkAlloc k 0 c))`; `parseSkolem s = .ok (some x) → renderSkolem x = s`.

**literal-canonicalization**
- Integer: `canonInteger s = some c → canonInteger c = some c ∧ intVal c = intVal s`; `canonInteger s = some c → canonInteger t = some d → (c = d ↔ intVal s = intVal t)`.
- Decimal: the same three laws for `canonDecimal` with `decVal : String → ℚ`.
- Civil calendar: `daysFromCivil (civilFromDays z) = z` for all `z : Int`; `validYMD y m d → civilFromDays (daysFromCivil y m d) = (y, m, d)`; `validYMD (civilFromDays z)`.
- Double parser correctness: `parseDouble s = some x → s.isNumeric → x = roundBinary64 (decVal s)`, where `roundBinary64 : ℚ → Double64` is the IEEE 754 round-to-nearest-even reference (with ±∞ and signed zero), defined in the proofs library.
- Double round trip: `x.isFinite → parseDouble (printDouble x) = some x`; for specials, `parseDouble (printDouble x) = some x.canonNaN`.
- Double shortest: `x.isFinite → roundBinary64 (d.val) = x → sigDigits (printDouble x) ≤ d.sigDigits` for every decimal `d`.

**term-dictionary** (on the pure model)
- `lookup_intern : (d.intern k n).ok = (i, d') → d'.lookup k = some i`.
- `intern_idem : d.lookup k = some i → d.intern k n = .ok (i, d)`.
- `intern_append_only : d.intern k n = .ok (i, d') → d.rows <+: d'.rows ∧ d.next ≤ d'.next`.
- `fresh_id : d.lookup k = none → d.intern k n = .ok (d.next, d') ∧ d'.next = d.next + 1`.
- `ids_unique : d.lookup k₁ = some i → d.lookup k₂ = some i → k₁ ≈ k₂` (coalesced equality), from the invariant `d.WF`, which `intern` preserves.
- `decode_internValue : d.internValue v = .ok (x, d') → d'.decode x = .ok v.canonical` (round trip through the dictionary, using the codec theorems above).

### Test strategy for what is not proven

- **Differential codec oracle** (M0 harness, pinned Rust). Inputs:
  - every edge literal listed in the specs;
  - 10⁷ random `u64` bit patterns for `canonical_double`;
  - 10⁶ random decimal strings, including long mantissas, huge exponents, subnormals, powers of ten, `MAX`, `MIN_POSITIVE`, −0.0, halfway cases, and rejected syntax;
  - random date/date-time lexicals across ±10⁶ years, ±14:00, 24:00, fractions, invalid days;
  - random integer and decimal strings.

  The harness compares the `Encoded` result field by field (inline raw id, or tag/lex/datatype/lang/num bits).
- **Property tests** in Lean (Plausible or a seeded generator): `parseDateTime ∘ formatDateTime` round trip; `literal ∘ lexical` stability on canonical values.
- **Refinement**: random intern/lookup/byId sequences on `ModelStore` vs `SqliteStore`, with the cache on, off and size 1, comparing every result and the final `term` table.
- **File interchange**:
  - Rust writes fixtures (all tags, every edge literal), and Lean opens them and decodes every id in `triple` and `term` to the same canonical dump Rust produces.
  - Lean creates a file and interns the same values, and Rust opens it and dumps the same terms.
  - Both `sqlite_schema` dumps match.
- **Trigger tests**: raw-SQLite attempts against Lean-created files, one per never-forget trigger.

## Risks / Trade-offs

- [The shortest-printer proof is the largest Tier 0 proof] → The interval characterisation is proven once against the parser, and the printer search is a bounded loop over `k ≤ 17`. If the proof slips, the printer ships as tested-only with its requirement marked pending in the theorem index. CI then fails, as the policy demands, so slipping is visible rather than silent.
- [Exact bignum arithmetic is slow on decode-heavy workloads with many doubles] → Clinger's fast path (exact for ≤ 15 digits and |q| ≤ 22) is done in `Nat`, so it stays proven. Benchmarks are report-only until M6 (D14), and Ryu/Eisel–Lemire can arrive later under `@[csimp]`.
- [Tie-breaking among equally close shortest candidates may differ from Rust] → Covered by the 10⁷ bit-pattern fuzz plus targeted halfway cases. Any mismatch is a bug against the byte-identity requirement.
- [leansqlite may bind TEXT through C strings and truncate at NUL] → Strings with NUL are legal values (`"a\0b"`). An M0 gap check covers it, and an M1 refinement test interns NUL-containing `STR` and `LANG_STR` terms. If binding is broken, the fix goes in the leansqlite pin, not in a format change.
- [SQLite may store `num = -0.0` as `0`] → Decoding uses `lex`, never `num`, so no value is lost. Rust has the same behaviour, so the files still match.
- [The `reserve-replica-id` change lands in Rust with different edge behaviour] → The oracle pin is taken after it lands (verification.md#Differential Oracle). Any difference in the origin scenarios is resolved before the pin, not by changing these specs silently.
