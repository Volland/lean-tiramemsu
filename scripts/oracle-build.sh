#!/usr/bin/env bash
# Builds the oracle from the pinned commit alone, reading the Rust repository only:
# `git archive <pin>` is unpacked into .oracle/rust-<pin>/ and oracle/rust-driver is built
# against it. Fails if the Rust repository's status, branches or worktree list change.
# Usage: scripts/oracle-build.sh [<commit>]
set -euo pipefail
source "$(dirname "$0")/lib.sh"

commit="${1:-$(pin_field commit)}"
[ -d "$RUST_REPO" ] || die "Rust repository not found at $RUST_REPO (set TIRAMEMSU_RUST_REPO)"
full="$(git -C "$RUST_REPO" rev-parse "$commit^{commit}")"

snapshot() {
  git -C "$RUST_REPO" status --porcelain=v1 --untracked-files=all
  git -C "$RUST_REPO" for-each-ref --format='%(refname) %(objectname)'
  git -C "$RUST_REPO" worktree list --porcelain
}
before="$(snapshot)"

src="$ROOT/.oracle/rust-$full"
if [ ! -f "$src/.complete" ]; then
  rm -rf "$src"
  mkdir -p "$src"
  git -C "$RUST_REPO" archive "$full" | tar -x -C "$src"
  touch "$src/.complete"
fi
ln -sfn "rust-$full" "$ROOT/.oracle/rust"

toolchain="$(sed -n 's/^channel[[:space:]]*=[[:space:]]*"\(.*\)"/\1/p' "$src/rust-toolchain.toml" | head -n1)"
[ -n "$toolchain" ] || die "no toolchain channel in $src/rust-toolchain.toml"
if command -v rustup >/dev/null && ! rustup run "$toolchain" rustc --version >/dev/null 2>&1; then
  rustup toolchain install "$toolchain" --profile minimal
fi
locked="--locked"
[ -f "$ROOT/oracle/rust-driver/Cargo.lock" ] || { cp "$src/Cargo.lock" "$ROOT/oracle/rust-driver/Cargo.lock"; locked=""; }
RUSTUP_TOOLCHAIN="$toolchain" CARGO_TARGET_DIR="$ROOT/.oracle/target" \
  cargo build --release $locked --manifest-path "$ROOT/oracle/rust-driver/Cargo.toml"

after="$(snapshot)"
[ "$before" = "$after" ] || die "the Rust repository changed during the oracle build"
echo "oracle driver: $ROOT/.oracle/target/release/tm-oracle-driver (pin $full)"
