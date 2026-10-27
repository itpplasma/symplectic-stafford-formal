#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

expected_toolchain=leanprover/lean4:v4.35.0-rc3
actual_toolchain=$(tr -d '\r\n' < lean-toolchain)
if [ "$actual_toolchain" != "$expected_toolchain" ]; then
  echo "expected $expected_toolchain in lean-toolchain, found $actual_toolchain" >&2
  exit 1
fi
if ! command -v elan >/dev/null 2>&1; then
  echo "elan is required to select the pinned Lean toolchain" >&2
  exit 1
fi

if ! ELAN_TOOLCHAIN="$expected_toolchain" elan which lean >/dev/null 2>&1; then
  elan toolchain install "$expected_toolchain"
fi
lean_bin=$(ELAN_TOOLCHAIN="$expected_toolchain" elan which lean)
lean_version=$("$lean_bin" --version)
lean_commit=$(printf '%s\n' "$lean_version" | sed -n 's/.*commit \([0-9a-f]\{40\}\).*/\1/p')
if [ "$lean_commit" != "470d5ce1400764999581fd26d5d72b00d990b0f4" ]; then
  echo "Lean toolchain binary has unexpected commit: ${lean_commit:-unknown}" >&2
  exit 1
fi
bin_root=$(cd -- "$(dirname -- "$lean_bin")" && pwd)
for tool in lake lean leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -f "$bin_root/$tool" ] || [ ! -x "$bin_root/$tool" ]; then
    echo "pinned toolchain lacks executable $bin_root/$tool" >&2
    exit 1
  fi
done

bwrap_bin=$(command -v bwrap || true)
if [ -z "$bwrap_bin" ] || [ ! -x "$bwrap_bin" ]; then
  echo "bubblewrap (bwrap) is required; install it before Palomar verification" >&2
  exit 1
fi
bwrap_bin=$(cd -- "$(dirname -- "$bwrap_bin")" && pwd)/$(basename -- "$bwrap_bin")
bwrap_version=$("$bwrap_bin" --version)
if [ "$bwrap_version" != "bubblewrap 0.12.0" ]; then
  echo "expected official Palomar bubblewrap 0.12.0, found $bwrap_version" >&2
  exit 1
fi
if ! "$bwrap_bin" --ro-bind / / /bin/true; then
  echo "bwrap cannot create the required read-only sandbox" >&2
  exit 1
fi

record_dir=.lake/palomar-tools
mkdir -p "$record_dir"
{
  printf 'Lean toolchain %s\n' "$expected_toolchain"
  printf 'Lean commit %s\n' "$lean_commit"
  printf 'Mathlib commit %s\n' "$(python3 - <<'PY'
import json
from pathlib import Path
manifest = json.loads(Path('lake-manifest.json').read_text())
print(next((p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib'), 'not used'))
PY
)"
  for tool in lake lean leanexport leanchecker nanoda_bin con-ron; do
    printf '%s sha256 %s\n' "$tool" "$(sha256sum "$bin_root/$tool" | cut -d ' ' -f1)"
  done
  printf 'bwrap version %s\n' "$bwrap_version"
  printf 'bwrap %s\n' "$bwrap_bin"
  printf 'bwrap sha256 %s\n' "$(sha256sum "$bwrap_bin" | cut -d ' ' -f1)"
} >"$record_dir/revisions.txt"

printf 'Palomar uses bundled Lean 4.35.0-rc3 tools and bwrap; recorded at %s/revisions.txt\n' "$record_dir"
