#!/usr/bin/env bash
# The single CI entry point, also run by developers:
#   scripts/ci.sh            build, proof gates, tests, oracle (every commit)
#   scripts/ci.sh nightly    the same, plus the >2 GiB probe, 5 000 x 1 000 refinement runs and
#                            refinement runs from several Rust-written fixtures
# The Rust repository is read from $TIRAMEMSU_RUST_REPO (default: ./tiramemsu), never written.
set -euo pipefail
source "$(dirname "$0")/lib.sh"
cd "$ROOT"
mode="${1:-ci}"
step() { echo; echo "== $*"; }

step "pins: toolchain and dependencies"
scripts/check-pins.sh

step "build: Mathlib cache and default targets (runtime, proofs, executable)"
lake exe cache get
lake build
lake build policy-check tiramemsu-tests oracle PolicyFixtures

step "native binary"
scripts/check-binary.sh

step "proof policy"
lake exe policy-check --self-test
lake exe policy-check

step "leansqlite gap-check probes"
if [ "$mode" = nightly ]; then
  .lake/build/bin/tiramemsu-tests probe --large
else
  .lake/build/bin/tiramemsu-tests probe
fi

step "store contract (model and SQLite) and plan report"
.lake/build/bin/tiramemsu-tests contract
.lake/build/bin/tiramemsu-tests plan

step "refinement"
.lake/build/bin/tiramemsu-tests refine --self-test
if [ "$mode" = nightly ]; then
  .lake/build/bin/tiramemsu-tests refine --seeds 5000 --ops 1000
else
  .lake/build/bin/tiramemsu-tests refine --seeds 200 --ops 300
fi

step "oracle: pin, read-only build, schema fixture"
scripts/oracle-pin-check.sh
if scripts/oracle-pin-check.sh "$(git -C "$RUST_REPO" rev-parse "$(pin_field commit)^")" >/dev/null 2>&1; then
  die "the pin check accepted the commit before the prerequisite"
fi
scripts/oracle-build.sh
scripts/check-schema-fixture.sh

step "oracle: harness tests and scenarios"
.lake/build/bin/oracle test
.lake/build/bin/oracle scenario oracle/scenarios/*.json

step "Rust-written fixtures: compatibility, plans, refinement"
mkdir -p .oracle/fixtures
if [ "$mode" = nightly ]; then seeds="1 2 3 4 5"; runs=1000; else seeds="1"; runs=100; fi
for s in $seeds; do
  f=".oracle/fixtures/rust-$s.db"
  .lake/build/bin/oracle fixture "$f" --seed "$s" --txs 80
  .lake/build/bin/tiramemsu-tests compat "$f"
  .lake/build/bin/tiramemsu-tests plan "$f" | head -n 2
  .lake/build/bin/tiramemsu-tests refine --start "$f" --seeds "$runs" --ops 300
done

step "benchmark harness smoke run (report-only)"
.lake/build/bin/oracle bench --n 1000 --out .oracle/bench-smoke

echo
echo "ci ($mode): all gates passed"
