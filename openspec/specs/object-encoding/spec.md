# object-encoding Specification

## Purpose
Defines the ObjectId: the single signed 64-bit integer that represents every value in a statement position. It covers the tag layout, the origin/counter split of allocated ids, inline encoding and decoding, canonical uniqueness, order within a tag, range-scan bounds and skolem IRIs, all compatible with the Rust format 1.

## Requirements

### Requirement: ObjectId layout and tags
An ObjectId SHALL be a signed 64-bit integer equal to `(payload << 4) | tag`, with the tag in the low 4 bits and a 60-bit payload above it. The tags SHALL be:

| Tag | Name | Kind | Payload |
|---|---|---|---|
| 0 | `IRI` | dictionary | term id |
| 1 | `NODE` | inline | allocated counter |
| 2 | `BNODE` | inline | allocated counter |
| 3 | `STMT` | inline | allocated counter |
| 4 | `TX` | inline | allocated counter |
| 5 | `INT` | inline | signed integer |
| 6 | `BOOL` | inline | 0 or 1 |
| 7 | `DATETIME` | inline | signed packed date-time |
| 8 | `DATE` | inline | signed days since 1970-01-01 |
| 9 | `SHORT_STR` | inline | packed short string |
| 10 | `STR` | dictionary | term id |
| 11 | `LANG_STR` | dictionary | term id |
| 12 | `TYPED` | dictionary | term id |
| 13 | `DOUBLE` | dictionary | term id |
| 14 | `DECIMAL` | dictionary | term id |
| 15 | `SEALED` | reserved | none in format 1 |

The payload of `INT`, `DATE` and `DATETIME` SHALL be read as a signed 60-bit value (arithmetic shift). Every other payload SHALL be read as an unsigned 60-bit value (logical shift). Each tag SHALL have the upper-case name shown, used wherever a tag is named (for example in tag IRIs).

#### Scenario: Integer five
- **WHEN** the integer 5 is encoded
- **THEN** its ObjectId is `(5 << 4) | 5 = 85`, and `85 & 15 = 5` identifies `INT`

#### Scenario: Statement and transaction ids are inline
- **WHEN** statement counter 42 and transaction number 7 are encoded
- **THEN** their ObjectIds are `(42 << 4) | 3` and `(7 << 4) | 4`, and no dictionary row is involved

#### Scenario: Large unsigned payload makes a negative id
- **WHEN** a `SHORT_STR` payload of `2^60 − 1` is encoded
- **THEN** the ObjectId is negative as a signed 64-bit integer, and its tag and payload still read back as `SHORT_STR` and `2^60 − 1`

#### Scenario: Machine-checked layout
- **WHEN** the proofs library builds
- **THEN** reading the tag and payload of an id built from any tag 0–14 and any 60-bit payload gives back that tag and payload, as a theorem whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Reserved SEALED tag is rejected
Format 1 SHALL reject tag 15 (`SEALED`, reserved for crypto-shredding) wherever an ObjectId is decoded, inspected for its tag, or accepted as input. The rejection SHALL be the error `Unsupported` with feature `SEALED (M6)`. No value SHALL ever encode to tag 15.

#### Scenario: Decoding tag 15
- **WHEN** the raw id `(3 << 4) | 15` is decoded
- **THEN** decoding fails with `Unsupported { feature: "SEALED (M6)" }`

#### Scenario: Machine-checked rejection
- **WHEN** the proofs library builds
- **THEN** every raw id whose low 4 bits equal 15 fails tag extraction with that error, and no value encodes to tag 15, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Origin and counter of allocated ids
For the allocated tags `NODE`, `BNODE`, `STMT` and `TX`, the high 12 bits of the 60-bit payload SHALL be the origin and the low 48 bits SHALL be the counter. Format 1 SHALL allocate only origin 0, so an allocated id SHALL equal the id the plain layout gives for the counter. An allocated-tag id with a non-zero origin SHALL be rejected with `Unsupported` and feature `origin <n>`, where `<n>` is the origin in decimal. This applies when the id is decoded, when it is given as a value or raw id on input, and when it arrives as a skolem IRI.

#### Scenario: Local ids have origin 0
- **WHEN** statement counter 42 is allocated
- **THEN** its payload is 42, its origin (`payload >> 48`) is 0, its counter is 42, and its ObjectId is `(42 << 4) | 3`

#### Scenario: Foreign origin rejected on decode
- **WHEN** the raw id with tag `STMT` and payload `(1 << 48) | 5` is decoded
- **THEN** decoding fails with `Unsupported { feature: "origin 1" }`

#### Scenario: Foreign origin rejected on input
- **WHEN** a `NODE` value with payload `(3 << 48) | 1` is encoded on the write path
- **THEN** encoding fails with `Unsupported { feature: "origin 3" }`

#### Scenario: Machine-checked origin split
- **WHEN** the proofs library builds
- **THEN** splitting the id built from any origin and counter gives back that origin and counter, origin-0 ids equal the plain layout, and every non-zero-origin id is rejected on decode, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Allocation counters are bounded
Allocating an id of kind `NODE`, `BNODE`, `STMT` or `TX` from a counter value `n` SHALL succeed with the origin-0 id of counter `n` and the next counter `n + 1` exactly when `n ≤ 2^48 − 1`. Otherwise it SHALL fail with `IdSpaceExhausted { kind }` naming the tag, and SHALL NOT produce an id that spills into the origin bits.

#### Scenario: Last counter value
- **WHEN** a `STMT` id is allocated from counter `2^48 − 1`
- **THEN** allocation succeeds with counter `2^48 − 1` and origin 0, and the next counter is `2^48`

#### Scenario: Past the bound
- **WHEN** a `STMT` id is allocated from counter `2^48`
- **THEN** allocation fails with `IdSpaceExhausted { kind: STMT }`

#### Scenario: Machine-checked bound
- **WHEN** the proofs library builds
- **THEN** allocation succeeds if and only if the counter is at most `2^48 − 1`, and a successful allocation has origin 0, as a theorem whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Inline encode and decode round trip
Every canonical value of an inline tag SHALL encode to exactly one ObjectId of that tag, and decoding that id SHALL return the value. Decoding SHALL be strict: it SHALL accept only ids that some canonical value encodes to. Every other id of an inline tag SHALL fail with `InvalidTerm`:
- a `BOOL` payload other than 0 or 1;
- a `DATETIME` timezone code above 1681;
- a `SHORT_STR` length above 7;
- `SHORT_STR` bytes that are not UTF-8;
- `SHORT_STR` bytes beyond the length that are not zero.

So for every accepted id, encoding the decoded value SHALL return the same id. Dictionary tags decode through the term dictionary.

#### Scenario: One value per inline tag
- **WHEN** `NODE` 1, `BNODE` 2, `STMT` 3, `TX` 4, `INT` −7, `BOOL` true, a `DATETIME` with offset +02:00, `DATE` −1 and `SHORT_STR` `"héllo"` are encoded and decoded
- **THEN** each decodes to the original value, and re-encoding gives the same id

#### Scenario: Malformed inline ids are rejected
- **WHEN** the ids `BOOL` payload 2, `DATETIME` timezone code 1682, `SHORT_STR` length 8, and `SHORT_STR` `"a"` with a non-zero byte after its length are decoded
- **THEN** each fails with `InvalidTerm`

#### Scenario: Machine-checked round trip
- **WHEN** the proofs library builds
- **THEN** decode after encode is the identity on canonical inline values, and encode after decode is the identity on accepted ids, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: One ObjectId per value
Two values SHALL encode to the same ObjectId, or to the same dictionary key, if and only if their canonical forms are equal. A value whose canonical form has an inline tag SHALL never be given a dictionary entry. Decoding SHALL be injective: two different accepted ids SHALL never decode to the same value.

#### Scenario: Lexical variants share an id
- **WHEN** the literals `"01"^^xsd:integer`, `"+1"^^xsd:integer` and `"1"^^xsd:integer` are encoded
- **THEN** all three give the same `INT` id

#### Scenario: Inlineable values never reach the dictionary
- **WHEN** an integer within 60 bits, a boolean, an in-range date, an in-range date-time and a string of at most 7 UTF-8 bytes are encoded
- **THEN** each encoding is inline and requests no dictionary key

#### Scenario: Machine-checked uniqueness
- **WHEN** the proofs library builds
- **THEN** equal encodings imply equal canonical values and vice versa, and decoding is injective, as theorems whose axioms satisfy the proof policy

### Requirement: Signed order within a tag
For `INT` and `DATE`, signed 64-bit order of ObjectIds SHALL equal the order of the encoded values, negatives included. For `DATETIME`, signed id order SHALL equal the lexicographic order of (instant, timezone code). For `NODE`, `BNODE`, `STMT` and `TX` with origin 0, signed id order SHALL equal counter order.

#### Scenario: Integers across zero
- **WHEN** −1000, −1, 0, 1 and `2^59 − 1` are encoded as `INT`
- **THEN** their ids are strictly increasing as signed 64-bit integers

#### Scenario: Earlier instant sorts first whatever the offset
- **WHEN** a date-time at instant `t` with offset +14:00 and one at instant `t + 1` ms without a timezone are encoded
- **THEN** the first id is smaller than the second

#### Scenario: Machine-checked order
- **WHEN** the proofs library builds
- **THEN** each of the four order statements holds for all in-range values, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Date-time packing and instant extraction
A `DATETIME` payload SHALL be `(epoch_ms << 11) | tz_code`, with `epoch_ms` in `[−2^48, 2^48)` and `tz_code` as defined by literal canonicalization (0 for no timezone, else offset minutes + 841). The instant of a `DATETIME` id SHALL be `id >> 15` with an arithmetic shift. Value comparison of date-times SHALL use the instant only, so a date-time without a timezone compares as UTC. Term identity SHALL use the whole id, so equal instants with different offsets are different terms.

#### Scenario: Offsets make two terms with one instant
- **WHEN** `2026-03-01T12:00:00+02:00` and `2026-03-01T10:00:00Z` are encoded
- **THEN** their ids differ, and `id >> 15` is the same epoch millisecond for both

#### Scenario: Instant before the epoch
- **WHEN** `1969-12-31T23:59:59.999Z` is encoded
- **THEN** `id >> 15` is −1

#### Scenario: Machine-checked packing
- **WHEN** the proofs library builds
- **THEN** unpacking a packed (instant, timezone) gives it back for every in-range instant and valid timezone, packing an accepted payload's unpacking gives the payload back, and `id >> 15` equals the instant, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Short-string packing
A `SHORT_STR` payload SHALL hold the string's UTF-8 bytes (at most 7) big-endian in its high 56 bits, the first byte highest, with zero bytes after the string. The byte length SHALL be in the low 4 bits. The empty string and strings containing NUL bytes SHALL be representable, and SHALL be distinguished by the length.

#### Scenario: Strings with NUL bytes
- **WHEN** `""`, `"a\0b"` and `"a"` are encoded
- **THEN** they give three different `SHORT_STR` ids, each decoding to exactly its string

#### Scenario: Machine-checked packing
- **WHEN** the proofs library builds
- **THEN** unpacking a packed string of at most 7 bytes gives back the string, and packing an accepted payload's string gives back the payload, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Range-scan bounds
A value range on one signed tag `T` (`INT`, `DATE`) SHALL be answerable as one contiguous id range filtered by `id & 15 = T`. The bounds SHALL be `(lo << 4) | T` and `(hi << 4) | T` inclusive. An instant range `[a, b]` on `DATETIME` SHALL use the bounds `(a << 15) | 7` and `(b << 15) | 0x7FF7` inclusive. For every id of tag `T`, lying within the bounds SHALL be equivalent to its value (or instant) lying within the range.

#### Scenario: Integer range
- **WHEN** the `INT` range `[−5, 10]` is turned into bounds
- **THEN** the bounds are `(−5 << 4) | 5` and `(10 << 4) | 5`, and the `INT` ids between them are exactly those of −5 … 10

#### Scenario: Date-time instant range covers every offset
- **WHEN** the instant range `[t, t]` is turned into bounds
- **THEN** every `DATETIME` id with instant `t`, whatever its timezone code, lies within the bounds, and no id with another instant does

#### Scenario: Machine-checked bounds
- **WHEN** the proofs library builds
- **THEN** the equivalence between "id within bounds" and "value within range" holds for every id of the tag, as a theorem whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Skolem IRIs
An origin-0 `NODE`, `BNODE`, `STMT` or `TX` id with counter `n` SHALL render as `urn:tiramemsu:node:<n>`, `urn:tiramemsu:bnode:<n>`, `urn:tiramemsu:stmt:<n>` or `urn:tiramemsu:tx:<n>`, with `<n>` in canonical decimal. An IRI of one of these forms SHALL be parsed according to `<n>`, and in no case SHALL parsing create an `IRI` term:
- a canonical decimal (no sign, no leading zero) with `1 ≤ n ≤ 2^48 − 1` gives the corresponding id;
- `2^48 ≤ n < 2^60` is rejected with `Unsupported { feature: "origin <n >> 48>" }`;
- anything else (0, leading zeros, a sign, non-digits, `n ≥ 2^60`) leaves the IRI an ordinary IRI.

#### Scenario: Node round trip
- **WHEN** the `NODE` id with counter 12 is rendered and the IRI is encoded again
- **THEN** the IRI is `urn:tiramemsu:node:12`, and encoding it gives the same `NODE` id with no dictionary key

#### Scenario: Non-canonical forms stay IRIs
- **WHEN** `urn:tiramemsu:node:007`, `urn:tiramemsu:node:0` and `urn:tiramemsu:node:-1` are encoded
- **THEN** each is an ordinary `IRI` value

#### Scenario: Foreign-origin skolem is rejected
- **WHEN** `urn:tiramemsu:stmt:281474976710661` (`(1 << 48) + 5`) is encoded
- **THEN** encoding fails with `Unsupported { feature: "origin 1" }`

#### Scenario: Machine-checked skolem round trip
- **WHEN** the proofs library builds
- **THEN** parsing the rendering of every origin-0 allocated id with counter `1 … 2^48 − 1` gives back that id, and rendering a parsed id gives back the IRI, as theorems whose axioms satisfy the proof policy
