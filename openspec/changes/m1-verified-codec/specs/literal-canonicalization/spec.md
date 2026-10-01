## Purpose

Maps every RDF literal and API value to exactly one canonical value, so that it gets exactly one ObjectId. Covers integers, booleans, strings, dates, date-times with timezones, decimals, and `xsd:double` held as IEEE bits with a correctly rounded parser and a shortest round-trip printer, all behaving like the Rust format 1.

## ADDED Requirements

### Requirement: Literal classification by datatype
A literal `(lex, datatype, lang)` SHALL be classified as follows, with `xsd:` meaning `http://www.w3.org/2001/XMLSchema#`:
- With a language tag, it SHALL be a language string with `lex` unchanged and the tag's ASCII letters lower-cased. Any datatype is then ignored.
- With no datatype or `xsd:string`, it SHALL be a plain string.
- `xsd:integer`, `xsd:boolean`, `xsd:date`, `xsd:dateTime`, `xsd:double` and `xsd:decimal` SHALL follow their own requirements below. A lexical form that is ill-typed or out of range for one of them SHALL become `TYPED` with that datatype and `lex` kept verbatim.
- Any other datatype, including derived types such as `xsd:int`, SHALL become `TYPED` with `lex` kept verbatim.

Lexical forms SHALL NOT be whitespace-trimmed.

#### Scenario: Language tag lower-cased
- **WHEN** `"colour"@en-GB` and `"colour"@en-gb` are classified
- **THEN** both are the language string `colour` with tag `en-gb`

#### Scenario: Plain and xsd:string agree
- **WHEN** `"hello"` and `"hello"^^xsd:string` are classified
- **THEN** both are the plain string `hello`

#### Scenario: Derived and unknown datatypes stay typed
- **WHEN** `"5"^^xsd:int` and `"POINT(1 2)"^^geo:wktLiteral` are classified
- **THEN** both are `TYPED` with their datatype and lexical form unchanged

#### Scenario: Ill-typed and padded forms stay typed
- **WHEN** `"abc"^^xsd:integer` and `" 1"^^xsd:integer` are classified
- **THEN** both are `TYPED xsd:integer` with lexical forms `abc` and ` 1`

### Requirement: Integers
An `xsd:integer` lexical form SHALL be an optional `+` or `-` followed by one or more ASCII digits. Its canonical decimal SHALL have no `+`, no leading zeros, and SHALL be `0` for any zero. An integer in `[−2^59, 2^59 − 1]` SHALL be the `INT` value. Any other integer SHALL be `TYPED xsd:integer` with the canonical decimal as its lexical form. An API integer SHALL be canonicalized the same way.

#### Scenario: Lexical variants collapse
- **WHEN** `"+0001"`, `"01"` and `"1"` are read as `xsd:integer`
- **THEN** each is `INT` 1, and `"-000"` is `INT` 0

#### Scenario: Range boundaries
- **WHEN** `2^59 − 1`, `−2^59`, `2^59` and `−2^59 − 1` are canonicalized
- **THEN** the first two are `INT`, and the last two are `TYPED xsd:integer` with lexical forms `576460752303423488` and `-576460752303423489`

#### Scenario: Machine-checked integer canonical form
- **WHEN** the proofs library builds
- **THEN** canonicalizing an integer is idempotent, keeps its numeric value, and two lexical forms canonicalize to the same text exactly when they denote the same integer, as theorems whose axioms satisfy the proof policy

### Requirement: Booleans
`xsd:boolean` SHALL accept exactly `true` and `1` as true, and `false` and `0` as false. Every other lexical form SHALL be ill-typed. The canonical lexical forms SHALL be `true` and `false`.

#### Scenario: Numeric and word forms agree
- **WHEN** `"1"^^xsd:boolean` and `"true"^^xsd:boolean` are classified
- **THEN** both are the boolean true, and `"TRUE"^^xsd:boolean` is `TYPED`

### Requirement: Strings
A plain string whose UTF-8 encoding is at most 7 bytes SHALL be a `SHORT_STR` value, and a longer one SHALL be a `STR` value. Length SHALL be counted in UTF-8 bytes, not characters. A language string SHALL always be `LANG_STR`, whatever its length.

#### Scenario: Seven-byte boundary
- **WHEN** `"abcdefg"`, `"abcdefgh"`, `"héllo"` and `"€€€"` are classified
- **THEN** `"abcdefg"` and `"héllo"` (6 bytes) are `SHORT_STR`, and `"abcdefgh"` and `"€€€"` (9 bytes) are `STR`

#### Scenario: Short language string
- **WHEN** `"hi"@en` is classified
- **THEN** it is `LANG_STR`

### Requirement: Date and date-time syntax
An `xsd:date` SHALL be `[-]YYYY-MM-DD` followed by an optional timezone. An `xsd:dateTime` SHALL be `[-]YYYY-MM-DDThh:mm:ss`, then an optional `.` with one or more digits, then an optional timezone. The year SHALL have 4 to 30 digits, with no leading zero when longer than 4. A leading `-` negates it as an astronomical year, so `0000` is 1 BCE. Month and day SHALL form a valid proleptic Gregorian date. Minutes and seconds SHALL be at most 59. The hour SHALL be at most 24, and hour 24 SHALL be allowed only as `24:00:00` with an all-zero fraction, meaning midnight of the next day. A timezone SHALL be `Z` or `±hh:mm` with `mm ≤ 59` and an absolute offset of at most 14:00. Any other form SHALL be ill-typed.

#### Scenario: Invalid calendar dates
- **WHEN** `"2026-02-30"^^xsd:date`, `"1900-02-29"^^xsd:date` and `"2026-03-01T10:00:00+14:01"^^xsd:dateTime` are classified
- **THEN** each is `TYPED` with its lexical form verbatim, while `"2000-02-29"^^xsd:date` is a `DATE`

#### Scenario: End-of-day hour
- **WHEN** `"2026-03-01T24:00:00Z"^^xsd:dateTime` is classified
- **THEN** it equals `2026-03-02T00:00:00.000Z`, and `"2026-03-01T24:00:01Z"` is `TYPED`

### Requirement: Timezone codes
A date-time's timezone SHALL be stored as a code: 0 for no timezone, else the offset in minutes plus 841, so that −14:00 … +14:00 maps to 1 … 1681. `Z`, `+00:00` and `-00:00` SHALL all be offset 0, code 841. The code SHALL be a bijection between `{no timezone} ∪ [−840, 840]` minutes and `0 … 1681`.

#### Scenario: Zero offsets are one code
- **WHEN** `2026-03-01T10:00:00Z` and `2026-03-01T10:00:00+00:00` are classified
- **THEN** both have timezone code 841 and are the same value

#### Scenario: Extreme offsets
- **WHEN** offsets −14:00 and +14:00 are encoded
- **THEN** their codes are 1 and 1681

#### Scenario: Machine-checked timezone code
- **WHEN** the proofs library builds
- **THEN** encoding then decoding a timezone code is the identity on its domain, and decoding rejects every code above 1681, as theorems whose axioms satisfy the proof policy, including the codec `bv_decide` allowlist

### Requirement: Date-time instants and canonical form
The instant of a date-time SHALL be its local time minus its offset (no timezone counting as offset 0), in epoch milliseconds. Fraction digits beyond the third SHALL be truncated, not rounded. An instant in `[−2^48, 2^48)` SHALL give a `DATETIME` value; otherwise the literal SHALL be `TYPED xsd:dateTime` with its lexical form verbatim. The canonical lexical form SHALL be `YYYY-MM-DDThh:mm:ss.mmm` in the value's own offset, followed by nothing, `Z`, or `±hh:mm`. The year SHALL be zero-padded to at least 4 digits, with `-` for negative years. An API date-time whose instant or offset is out of range SHALL become `TYPED xsd:dateTime` with that canonical lexical form.

#### Scenario: Sub-millisecond truncation
- **WHEN** `"2026-03-01T10:00:00.123999Z"^^xsd:dateTime` is classified
- **THEN** its instant is that of `10:00:00Z` plus 123 ms, and its canonical form is `2026-03-01T10:00:00.123Z`

#### Scenario: Offset kept in the canonical form
- **WHEN** `"2026-03-01T12:00:00+02:00"^^xsd:dateTime` is classified and printed
- **THEN** the canonical form is `2026-03-01T12:00:00.000+02:00`

#### Scenario: Out-of-range instant
- **WHEN** `"12000-01-01T00:00:00Z"^^xsd:dateTime` is classified
- **THEN** it is `TYPED xsd:dateTime` with lexical form `12000-01-01T00:00:00Z`

#### Scenario: Text round trip
- **WHEN** random in-range (instant, timezone) pairs are printed in canonical form and parsed back
- **THEN** each parse gives back the same instant and timezone

### Requirement: Dates
An `xsd:date` SHALL be the signed number of days from 1970-01-01 to its date. A timezone suffix SHALL be validated and then ignored. A day count in `[−2^59, 2^59 − 1]` SHALL give a `DATE` value; otherwise the literal SHALL be `TYPED xsd:date` with its lexical form verbatim. The canonical lexical form SHALL be `YYYY-MM-DD`, with the year padded as for date-times.

#### Scenario: Dates around the epoch
- **WHEN** `"1970-01-01"`, `"1969-12-31"` and `"1969-12-31Z"` are read as `xsd:date`
- **THEN** they are `DATE` 0, `DATE` −1 and `DATE` −1

### Requirement: Civil calendar conversion
The conversion between proleptic Gregorian dates `(year, month, day)` and day numbers relative to 1970-01-01 SHALL be a bijection between all valid dates and all integers. It SHALL use astronomical year numbering, with the Gregorian leap rule applied to every year, negative years included.

#### Scenario: Known day numbers
- **WHEN** 1970-01-01, 1969-12-31, 2000-03-01 and 0000-03-01 are converted to day numbers and back
- **THEN** they give 0, −1, 11017 and −719468 and convert back to the same dates

#### Scenario: Machine-checked calendar
- **WHEN** the proofs library builds
- **THEN** converting any integer day number to a date gives a valid date that converts back to that day number, and converting any valid date to a day number converts back to that date, as theorems whose axioms satisfy the proof policy

### Requirement: Decimals
An `xsd:decimal` lexical form SHALL be an optional sign, then integer digits, then optionally `.` and fraction digits, with at least one digit overall and no exponent. Its canonical form SHALL:
- have no `+`;
- have no leading zeros in the integer part, with `0` when it is empty;
- have no trailing zeros in the fraction, with `0` when it is empty;
- always contain a `.`;
- be `0.0` for any zero, without a sign.

A valid form SHALL be the `DECIMAL` value with its canonical form; an invalid one SHALL be `TYPED xsd:decimal` verbatim.

#### Scenario: Decimal variants collapse
- **WHEN** `"01.50"`, `"1.5"`, `"+1.5000"` are read as `xsd:decimal`
- **THEN** all are `DECIMAL` `1.5`, while `"3"` is `3.0`, `".5"` is `0.5`, `"-0.0"` is `0.0`, and `"."` and `"1e3"` are `TYPED`

#### Scenario: Machine-checked decimal canonical form
- **WHEN** the proofs library builds
- **THEN** canonicalizing a decimal is idempotent, keeps its rational value, and two valid forms canonicalize to the same text exactly when they denote the same rational, as theorems whose axioms satisfy the proof policy

### Requirement: Doubles are parsed with correct rounding
`xsd:double` SHALL be held as its IEEE 754 binary64 bit pattern. The forms `INF`, `+INF`, `-INF` and `NaN` SHALL be accepted exactly as written. Any other accepted form SHALL be an optional sign, then integer digits, then optionally `.` and fraction digits (at least one digit overall), then optionally `e` or `E` with an optional sign and one or more digits. Such a form SHALL be converted to the binary64 value nearest to its exact decimal value, ties to even. Values at or beyond the overflow threshold SHALL become ±∞, values too small SHALL become ±0 or a subnormal by the same rule, and the sign of zero SHALL be kept. Any other form (for example `inf`, `-NaN`, `1e`, `0x1p3`) SHALL be ill-typed. The parse SHALL use exact arithmetic and SHALL NOT depend on hardware floating point. Its memory use SHALL NOT grow with the numeric value of the exponent, only with the length of the input.

#### Scenario: Equivalent spellings
- **WHEN** `"1.0"`, `"1E0"` and `"+1e+0"` are read as `xsd:double`
- **THEN** all give the bits of 1.0

#### Scenario: Ties to even
- **WHEN** `"9007199254740993"` (`2^53 + 1`) is read as `xsd:double`
- **THEN** it gives the bits of `2^53`

#### Scenario: Overflow and underflow
- **WHEN** `"1e400"`, `"-1e400"`, `"1e-400"` and `"-1e-400"` are read, along with a form with a 1000-digit exponent
- **THEN** they give +∞, −∞, +0.0 and −0.0, and the long exponent completes and saturates in the same way

#### Scenario: Machine-checked correct rounding
- **WHEN** the proofs library builds
- **THEN** every accepted numeric form parses to the round-to-nearest-even binary64 value of its exact decimal value, as a theorem whose axioms satisfy the proof policy

### Requirement: Doubles print in shortest round-trip form
The canonical lexical form of a double SHALL be:
- `NaN` for every NaN bit pattern, and `INF` / `-INF` for infinities;
- for finite values, the decimal with the fewest significant digits that parses back to the same bits, choosing among those the one nearest the exact value, written as `[-]d.dddE[-]n`:
  - one leading digit, then `.`;
  - then the remaining digits, or `0` when there are none;
  - then `E` and the decimal exponent with no `+` and no leading zeros.

Zero SHALL be `0.0E0` and negative zero `-0.0E0`, two different values. Every NaN SHALL canonicalize to the quiet NaN with bits `0x7FF8000000000000`. Parsing the canonical form SHALL return the canonical value.

#### Scenario: Canonical forms
- **WHEN** 1.0, 150.0, −0.00003, 0.1, −0.0, 5e-324, `2.2250738585072014e-308` and `1.7976931348623157e308` are printed
- **THEN** the forms are `1.0E0`, `1.5E2`, `-3.0E-5`, `1.0E-1`, `-0.0E0`, `5.0E-324`, `2.2250738585072014E-308` and `1.7976931348623157E308`

#### Scenario: NaN payloads collapse
- **WHEN** two NaNs with different payload bits are canonicalized
- **THEN** both print `NaN` and both canonicalize to the bits `0x7FF8000000000000`

#### Scenario: Machine-checked round trip and shortness
- **WHEN** the proofs library builds
- **THEN** for every finite double, parsing its printed form gives back the same bits, and no decimal with fewer significant digits parses to those bits, as theorems whose axioms satisfy the proof policy

### Requirement: Double text is byte-identical to Rust
For every bit pattern, the printed canonical form SHALL be byte-identical to Rust's `canonical_double`, which is `{:e}` with `.0` inserted when there is no fraction and `e` replaced by `E`. For every string, the parse result SHALL be bit-identical to Rust's `parse_double`, including whether the form is accepted. This SHALL be checked against the pinned Rust oracle.

#### Scenario: Random bit patterns
- **WHEN** at least 10⁷ uniformly random 64-bit patterns are printed by both builds
- **THEN** every output is byte-identical

#### Scenario: Edge cases
- **WHEN** every subnormal boundary, every power of ten from 1e-324 to 1e308, `MAX`, `MIN_POSITIVE`, the smallest subnormal, ±0.0, ±∞, NaN, exact halfway decimals and 10⁶ random decimal strings with up to 800 digits are printed and parsed by both builds
- **THEN** printed text is byte-identical and parsed bits are identical, rejections included

### Requirement: Canonical form of API values
Values given directly through the API SHALL be canonicalized before encoding:
- an IRI of a skolem form SHALL become its allocated id;
- an integer outside the `INT` range SHALL become `TYPED xsd:integer` with its canonical decimal;
- a date outside the `DATE` range SHALL become `TYPED xsd:date` with its canonical form;
- a date-time whose instant or offset is out of range SHALL become `TYPED xsd:dateTime` with its canonical form;
- a language tag SHALL be lower-cased;
- a `TYPED` value SHALL be re-classified by the literal rules, so `TYPED("1", xsd:integer)` becomes `INT` 1;
- a decimal SHALL take its canonical form, or become `TYPED` if invalid;
- a double NaN SHALL become the canonical NaN.

Canonicalization SHALL be idempotent, and re-classifying a canonical value's lexical form and datatype SHALL return the same value.

#### Scenario: Typed literal of a special datatype
- **WHEN** the API value `TYPED("01", xsd:integer)` is canonicalized
- **THEN** it is `INT` 1

#### Scenario: Lexical stability
- **WHEN** random canonical values of every literal kind are printed to (lexical form, datatype, language) and classified again
- **THEN** each gives back the same canonical value
