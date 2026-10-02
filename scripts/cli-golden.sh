#!/usr/bin/env bash
# Golden test of the `tiramemsu` command-line tool (lean-api "Command-line tool"): JSON-lines
# output, error JSON with exit status 1, usage errors with exit status 2, and the bundle pipe
# between two files. Usage: scripts/cli-golden.sh [--update]
set -uo pipefail
cd "$(dirname "$0")/.."
T=.lake/build/bin/tiramemsu
D=testdata/tmp/cli
rm -rf "$D"; mkdir -p "$D"
out="$D/actual.txt"
run() { echo "\$ tiramemsu $*" >>"$out"; "$T" "$@" >>"$out" 2>&1; echo "exit $?" >>"$out"; }
: >"$out"
run "$D/a.db" assert v:alice v:worksAt v:acme
run "$D/a.db" assert stmt:1 v:confidence 0.8 --valid-from 2024-01-01
run "$D/a.db" assert v:bob v:knows v:alice
run "$D/a.db" triples --s v:alice
run "$D/a.db" triples --p v:confidence
run "$D/a.db" values v:alice v:worksAt
run "$D/a.db" dependents stmt:1
run "$D/a.db" path v:bob "knows/worksAt" --mode TRAIL
run "$D/a.db" path v:bob "knows+" --max-hops 3
run "$D/a.db" path v:bob "knows/(" 
run "$D/a.db" path
run "$D/a.db" path v:bob knows --mode SIMPLE
run "$D/a.db" retract stmt:3
run "$D/a.db" triples --history
run "$D/a.db" triples --as-of 2
run "$D/a.db" bundle stmt:1
echo "\$ tiramemsu a.db bundle stmt:1 | tiramemsu b.db import-bundle -" >>"$out"
"$T" "$D/a.db" bundle stmt:1 | "$T" "$D/b.db" import-bundle - >>"$out" 2>&1; echo "exit $?" >>"$out"
run "$D/b.db" triples
run "$D/a.db" info
sed -i.bak "s#$D/##g" "$out" && rm -f "$out.bak"
if [ "${1:-}" = "--update" ]; then cp "$out" testdata/cli/expected.txt; echo "updated"; exit 0; fi
if diff -u testdata/cli/expected.txt "$out"; then echo "cli golden: ok"; else echo "cli golden: FAILED"; exit 1; fi
