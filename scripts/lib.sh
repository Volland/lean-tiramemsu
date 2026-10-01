# Shared helpers for the scripts in this directory. Sourced, not executed.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# The Rust repository (read-only). Defaults to the `tiramemsu` link next to the sources.
RUST_REPO="${TIRAMEMSU_RUST_REPO:-$ROOT/tiramemsu}"
# cargo from rustup (the toolchain is read from the pinned tree's rust-toolchain.toml).
export PATH="$HOME/.cargo/bin:$PATH"

pin_field() { # pin_field <name>: a field of oracle/RUST_PIN
  sed -n "s/^$1[[:space:]]*=[[:space:]]*//p" "$ROOT/oracle/RUST_PIN" | head -n1
}

die() { echo "error: $*" >&2; exit 1; }
