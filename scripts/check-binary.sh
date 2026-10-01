#!/usr/bin/env bash
# Native-binary checks of the `tiramemsu` executable: its dynamic dependencies are system
# libraries only (no Lean shared library), and its version command runs with no Lean
# toolchain on the search path.
set -euo pipefail
source "$(dirname "$0")/lib.sh"
cd "$ROOT"

exe="$ROOT/.lake/build/bin/tiramemsu"
[ -x "$exe" ] || die "build the executable first ($exe)"

case "$(uname -s)" in
  Darwin) deps="$(otool -L "$exe" | tail -n +2)" ;;
  Linux)  deps="$(ldd "$exe" || true)" ;;
  *) die "unsupported platform $(uname -s)" ;;
esac
echo "$deps"
if echo "$deps" | grep -Eiq 'lean|libInit|libStd|libLake'; then
  die "the executable links a Lean shared library"
fi

tmp="$(mktemp -d)"
cp "$exe" "$tmp/tiramemsu"
out="$(cd "$tmp" && env -i HOME="$tmp" PATH=/usr/bin:/bin ./tiramemsu version)"
rm -rf "$tmp"
echo "$out"
echo "$out" | grep -q '^format 1$' || die "version report lacks the format version"
echo "$out" | grep -q '^sqlite 3\.' || die "version report lacks the SQLite version"
echo "binary ok: system libraries only, runs without a toolchain"
