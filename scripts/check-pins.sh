#!/usr/bin/env bash
# Toolchain and dependency pins: lean-toolchain equals the lean-toolchain of the pinned Mathlib
# commit; every lakefile `require` and every manifest entry names an exact 40-hex commit.
set -euo pipefail
source "$(dirname "$0")/lib.sh"
cd "${1:-$ROOT}"   # optional argument: another checkout (used by the self-check)

python3 - <<'PY'
import json, re, subprocess, sys

errors = []
hexrev = re.compile(r"^[0-9a-f]{40}$")
manifest = json.load(open("lake-manifest.json"))
for p in manifest["packages"]:
    if not hexrev.match(p.get("rev") or ""):
        errors.append(f"manifest entry {p.get('name')} is not pinned to an exact commit (rev {p.get('rev')!r})")

lakefile = open("lakefile.lean").read()
for name, rev in re.findall(r'require\s+(\S+)\s+from\s+git\s+"[^"]+"\s*@\s*"([^"]*)"', lakefile):
    if not hexrev.match(rev):
        errors.append(f"lakefile requires {name} at {rev!r}, not an exact commit")
for name in re.findall(r'require\s+(\S+)\s+from', lakefile):
    if name not in {p["name"] for p in manifest["packages"]}:
        errors.append(f"lakefile requires {name}, which the manifest does not pin")

mathlib = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
project = open("lean-toolchain").read().strip()
if mathlib is None:
    errors.append("mathlib is not in the manifest")
else:
    try:
        theirs = subprocess.run(
            ["git", "-C", ".lake/packages/mathlib", "show", f"{mathlib['rev']}:lean-toolchain"],
            check=True, capture_output=True, text=True).stdout.strip()
    except subprocess.CalledProcessError as e:
        errors.append(f"cannot read lean-toolchain of mathlib {mathlib['rev']}: {e.stderr.strip()}")
        theirs = None
    if theirs is not None and theirs != project:
        errors.append(f"lean-toolchain {project} differs from the pinned Mathlib's {theirs}")

for e in errors:
    print("error:", e, file=sys.stderr)
if errors:
    sys.exit(1)
print(f"pins ok: {project}; {len(manifest['packages'])} manifest entries pinned to exact commits")
PY
