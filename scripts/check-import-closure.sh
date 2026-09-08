#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
case "${1:-}" in
  Challenge|Solution) module=$1 ;;
  *) echo "usage: $0 Challenge|Solution" >&2; exit 2 ;;
esac

mkdir -p .lake/verification
audit=".lake/verification/${module}Imports.lean"
log=".lake/verification/${module}-imports.log"
{
  echo "import $module"
  echo "import Lean.Elab.Command"
  cat <<'LEAN'
run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    Lean.logInfo m!"IMPORT {name}"
LEAN
} > "$audit"
lake env lean --trust=0 "$audit" > "$log" 2>&1

python3 - "$module" "$log" <<'PY'
import json
import re
import sys
from pathlib import Path

target, log = sys.argv[1:]
names = re.findall(r'^IMPORT (\S+)$', Path(log).read_text(), re.M)
if target not in names:
    raise SystemExit('loaded-environment audit did not report its target')
if target == 'Solution':
    forbidden = [n for n in names if n == 'Challenge' or n.startswith('Challenge.')]
else:
    manifest = json.loads(Path('lake-manifest.json').read_text())
    allowed_roots = {'Init', 'Lean', 'Std', 'Mathlib'}
    allowed = set()
    for pkg in manifest.get('packages', []):
        root = Path('.lake/packages') / pkg['name']
        if not root.is_dir():
            continue
        for source in root.rglob('*.lean'):
            rel = source.relative_to(root)
            if not any(part.startswith('.') for part in rel.parts):
                allowed.add('.'.join(rel.with_suffix('').parts))
    forbidden = [n for n in names
                 if n != 'Challenge' and n.split('.')[0] not in allowed_roots
                 and n not in allowed]
if forbidden:
    raise SystemExit(f'{target} has forbidden transitive imports: {forbidden}')
print(f'{target}: audited {len(names)} loaded modules')
PY
