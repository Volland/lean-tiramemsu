#!/usr/bin/env bash
# Read-only check of the Rust oracle pin: the commit exists in the Rust repository, its tree
# contains the archived reserve-replica-id change and no active one.
# Usage: scripts/oracle-pin-check.sh [<commit>]   (default: the commit in oracle/RUST_PIN)
set -euo pipefail
source "$(dirname "$0")/lib.sh"

commit="${1:-$(pin_field commit)}"
change="$(pin_field change)"
[ -n "$commit" ] || die "no commit given and none recorded in oracle/RUST_PIN"
[ -n "$change" ] || die "oracle/RUST_PIN records no change name"
[ -d "$RUST_REPO" ] || die "Rust repository not found at $RUST_REPO (set TIRAMEMSU_RUST_REPO)"

git -C "$RUST_REPO" cat-file -e "$commit^{commit}" 2>/dev/null \
  || die "commit $commit does not exist in $RUST_REPO"
full="$(git -C "$RUST_REPO" rev-parse "$commit^{commit}")"

archived="$(git -C "$RUST_REPO" ls-tree -d --name-only "$full" openspec/changes/archive/ \
  | grep -E "/[0-9]{4}-[0-9]{2}-[0-9]{2}-$change\$" || true)"
[ -n "$archived" ] || die "commit $full has no archived $change change (pin predates the prerequisite)"

active="$(git -C "$RUST_REPO" ls-tree -d --name-only "$full" openspec/changes/ \
  | grep -E "^openspec/changes/$change\$" || true)"
[ -z "$active" ] || die "commit $full still has an active $change change"

if [ -z "${1:-}" ]; then
  evidence="$(pin_field evidence)"
  [ "$archived" = "$evidence" ] || die "recorded evidence $evidence differs from $archived"
fi
echo "pin ok: $full ($archived)"
