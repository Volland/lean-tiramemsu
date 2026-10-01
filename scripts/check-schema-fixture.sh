#!/usr/bin/env bash
# testdata/format1-schema.sql must equal the schema of an empty database created by the pinned
# Rust build (needs the oracle driver from scripts/oracle-build.sh).
set -euo pipefail
source "$(dirname "$0")/lib.sh"
cd "$ROOT"

dir=".oracle/work/schema"
rm -rf "$dir"; mkdir -p "$dir"
printf '%s\n' "{\"id\":1,\"op\":\"open\",\"args\":{\"path\":\"$dir/empty.db\"}}" '{"id":2,"op":"close"}' \
  | .oracle/target/release/tm-oracle-driver > /dev/null
.lake/build/bin/tiramemsu-tests schema-dump "$dir/empty.db" > "$dir/schema.sql"
if ! diff -u testdata/format1-schema.sql "$dir/schema.sql"; then
  die "testdata/format1-schema.sql differs from the pinned Rust build's schema"
fi
echo "schema fixture ok: matches the pinned Rust build"
