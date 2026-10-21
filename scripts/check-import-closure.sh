#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
case "${1:-}" in
  Challenge|Solution|SymplecticStafford.Paper) module=$1 ;;
  *) echo "usage: $0 Challenge|Solution|SymplecticStafford.Paper" >&2; exit 2 ;;
esac

mkdir -p .lake/verification
audit=".lake/verification/${module}Imports.lean"
log=".lake/verification/${module}-imports.log"
{
  echo 'module'
  echo "import $module"
  echo "import Lean.Elab.Command"
  cat <<'LEAN'
run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    Lean.logInfo m!"IMPORT {name}"
LEAN
} > "$audit"
lake env bash -c '
  repo_root=$1
  shift
  export LEAN_PATH="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
  exec lean --trust=0 "$@"
' bash "$repo_root" "$audit" > "$log" 2>&1

python3 - "$module" "$log" <<'PY'
import json
import re
import sys
from pathlib import Path

target, log = sys.argv[1:]
names = re.findall(r'^IMPORT (\S+)$', Path(log).read_text(), re.M)
if target not in names:
    raise SystemExit('loaded-environment audit did not report its target')
# Only Mathlib and its own pinned transitive packages are allowed as external
# proof dependencies. In particular, the historical Stafford/AA dependencies
# cannot enter the current Challenge or Paper authority unnoticed.
mathlib_manifest = json.loads(Path('.lake/packages/mathlib/lake-manifest.json').read_text())
mathlib_packages = {'mathlib'} | {p['name'] for p in mathlib_manifest.get('packages', [])}
allowed = set()
for name in mathlib_packages:
    root = Path('.lake/packages') / name
    for source in root.rglob('*.lean'):
        rel = source.relative_to(root)
        if not any(part.startswith('.') for part in rel.parts):
            allowed.add('.'.join(rel.with_suffix('').parts))

def permitted(name):
    if name.split('.')[0] in {'Init', 'Lean', 'Std'} or name in allowed:
        return True
    if target == 'Challenge':
        return name == 'Challenge'
    return (name == 'Solution' and target == 'Solution') or name == 'SymplecticStafford.Paper' or name.startswith('SymplecticStafford.Paper.')

forbidden = [n for n in names if not permitted(n)]
if forbidden:
    raise SystemExit(f'{target} has forbidden transitive imports: {forbidden}')
print(f'{target}: audited {len(names)} loaded modules; Mathlib-only external closure')
PY
