## Purpose

Defines the term dictionary that holds every value too large for an inline ObjectId (IRIs, long strings, language strings, typed literals, doubles, decimals). It covers the row contents, the identity key, intern and lookup semantics, id allocation, immutability, decoding, and caching, compatible with the Rust `term` table.

## ADDED Requirements

### Requirement: Term rows
A dictionary value SHALL be stored as one `term` row `(id, tag, lex, dt, lang, num)`, and its ObjectId SHALL be `(id << 4) | tag`. The tag SHALL be one of `IRI`, `STR`, `LANG_STR`, `TYPED`, `DOUBLE` or `DECIMAL`, and the columns SHALL hold:

| Column | Contents |
|---|---|
| `lex` | Canonical lexical form: the IRI text, the string, the language string's text, the `TYPED` lexical form, the canonical double form, or the canonical decimal form |
| `dt` | For `TYPED`, `DOUBLE` and `DECIMAL`, the raw `IRI` ObjectId of the datatype IRI (`xsd:double` for `DOUBLE`, `xsd:decimal` for `DECIMAL`); NULL for the other tags |
| `lang` | The lower-cased language tag for `LANG_STR`; NULL for the other tags |
| `num` | For `DOUBLE`, the double's value, NULL for NaN. For `DECIMAL`, the correctly rounded binary64 value of the decimal. NULL for the other tags |

#### Scenario: Typed literal row
- **WHEN** `"POINT(1 2)"^^geo:wktLiteral` is interned
- **THEN** its row has tag `TYPED`, lex `POINT(1 2)`, `dt` equal to the raw ObjectId of the `IRI` term `geo:wktLiteral`, NULL `lang`, and NULL `num`

#### Scenario: Double and decimal rows
- **WHEN** `"1E0"^^xsd:double`, `"NaN"^^xsd:double` and `"0.10"^^xsd:decimal` are interned
- **THEN** their rows have lex `1.0E0`, `NaN` and `0.1`, and `num` equal to 1.0, NULL, and the binary64 nearest to 0.1

#### Scenario: Rows match Rust
- **WHEN** the same values are interned in the same order by the Lean build and by the pinned Rust build into fresh files
- **THEN** the `term` tables are equal row by row, `num` bits included

### Requirement: One row per term key
A term SHALL be identified by `(tag, lex, dt, lang)`, where an absent `dt` SHALL compare equal to 0 and an absent `lang` SHALL compare equal to the empty string, exactly as the `term_key` index compares. The dictionary SHALL hold at most one row per key, and two different keys SHALL never share an id.

#### Scenario: Same IRI in two transactions
- **WHEN** the IRI `https://example.org/alice` is interned in two different transactions
- **THEN** both return the same `IRI` ObjectId, and the `term` table holds one row for it

#### Scenario: Same text, different kinds
- **WHEN** the IRI `urn:x:abcdefghij` and the plain string `"urn:x:abcdefghij"` are interned
- **THEN** they get different ids with tags `IRI` and `STR`

#### Scenario: Machine-checked key uniqueness
- **WHEN** the proofs library builds
- **THEN** on the dictionary model, every reachable dictionary maps each id to at most one key and each key to at most one id, as a theorem whose axioms satisfy the proof policy

### Requirement: Interning on the write path
Interning a value SHALL first canonicalize and encode it. An inline encoding SHALL be returned with no dictionary access. Otherwise interning SHALL:
1. intern the datatype IRI first, when there is one;
2. look the key up;
3. return the existing id if the key is present;
4. otherwise insert a row with `id = next_term`, then increase `next_term` by one.

Interning the same value again SHALL return the same ObjectId and change nothing.

#### Scenario: Datatype interned before the term
- **WHEN** a fresh dictionary interns `"POINT(1 2)"^^geo:wktLiteral`
- **THEN** `geo:wktLiteral` receives id 1 and the literal receives id 2, the same ids Rust allocates

#### Scenario: Idempotent intern
- **WHEN** a 20-byte plain string is interned twice
- **THEN** the second intern returns the first id, and no row or counter changes

#### Scenario: Machine-checked intern laws
- **WHEN** the proofs library builds
- **THEN** on the dictionary model, a value is found by lookup right after it is interned, interning a present key changes nothing, and interning an absent key returns the previous `next_term` and advances it by one, as theorems whose axioms satisfy the proof policy

### Requirement: Ids are never reused and terms never change
The dictionary SHALL only grow. Once inserted, a row's id and every column SHALL never change, no row SHALL ever be deleted, and `next_term` SHALL only increase. `next_term` SHALL NOT exceed `2^60 − 1`. Interning a new key when no id is left SHALL fail with `IdSpaceExhausted { kind: TERM }`, and SHALL NOT change the dictionary.

#### Scenario: Existing rows are a prefix
- **WHEN** any sequence of interns runs on a dictionary
- **THEN** every row present before the sequence is present afterwards, unchanged

#### Scenario: Dictionary full
- **WHEN** `next_term` is `2^60` and a new key is interned
- **THEN** interning fails with `IdSpaceExhausted { kind: TERM }`, and an already present key still interns to its id

#### Scenario: Machine-checked append-only
- **WHEN** the proofs library builds
- **THEN** on the dictionary model, interning keeps the previous rows as a prefix and never decreases `next_term`, as a theorem whose axioms satisfy the proof policy

### Requirement: Lookup without insertion on the read path
Encoding a value for a read SHALL only look it up and SHALL NOT insert anything. A missing dictionary value SHALL be reported as absent, and so SHALL a value whose datatype IRI is missing. The `term` table and `next_term` SHALL be unchanged by any number of lookups.

#### Scenario: Unknown IRI
- **WHEN** a read encodes an IRI that was never interned
- **THEN** the result is absent, and the `term` table and `next_term` are unchanged

#### Scenario: Unknown datatype
- **WHEN** a read encodes `"x"^^<urn:never-seen>`
- **THEN** the result is absent, and no `IRI` row is created for `urn:never-seen`

### Requirement: Decoding dictionary ids
Decoding an ObjectId of a dictionary tag SHALL read the row with that id and SHALL rebuild the value from `lex`, from the datatype IRI that `dt` names, and from `lang`. A `DOUBLE` value SHALL be rebuilt by parsing its `lex`, never from `num`. A missing row, or a row whose tag differs from the id's tag, SHALL fail with `InvalidTerm`. Decoding an interned value SHALL give its canonical form.

#### Scenario: Tag mismatch
- **WHEN** the id `(id << 4) | STR` is decoded and row `id` holds an `IRI`
- **THEN** decoding fails with `InvalidTerm`

#### Scenario: Round trip through the dictionary
- **WHEN** random IRIs, long strings, language strings, typed literals, doubles (signed zeros, subnormals and NaN included) and decimals are interned and decoded
- **THEN** each decodes to its canonical value

#### Scenario: Machine-checked dictionary round trip
- **WHEN** the proofs library builds
- **THEN** on the dictionary model, decoding the id returned by interning any value gives the value's canonical form, as a theorem whose axioms satisfy the proof policy

### Requirement: Caching never changes results
Term caches SHALL be append-only. Because terms are immutable, a cached entry SHALL never be invalidated, only evicted. Entries created inside a transaction SHALL become shared only after it commits, and SHALL be dropped when it rolls back. A read SHALL never cache a term it saw uncommitted. Every intern, lookup and decode result SHALL be the same with caching enabled, disabled, or limited to one entry.

#### Scenario: Rolled-back term is not served from cache
- **WHEN** a transaction interns a new IRI and rolls back, and a later read encodes that IRI
- **THEN** the read reports it absent

#### Scenario: Cache size does not matter
- **WHEN** the same random sequence of interns, lookups, decodes, commits and rollbacks runs with cache capacity unbounded, 1 and 0
- **THEN** all three runs return identical results and leave identical `term` tables

### Requirement: SQLite dictionary refines the model
The dictionary as stored in SQLite SHALL return the same result as the dictionary model for every intern, lookup and decode, and SHALL leave a `term` table equal to the model's rows. Strings containing NUL bytes and any Unicode text are included.

#### Scenario: Random operation sequences
- **WHEN** random sequences of interns, lookups and decodes, including strings with NUL bytes and non-BMP characters, run on the model and on SQLite
- **THEN** every result is equal, and the final rows are equal
