#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
./scripts/check-resources.sh
mkdir -p .lake/verification
python3 scripts/check-pins.py
python3 scripts/check-dependency-checkouts.py
python3 scripts/check-source-policy.py
map_args=(--formal-only)
if [[ -n "${PAPER_REPO:-}" ]]; then map_args=(); fi
python3 scripts/check-paper-lean-map.py "${map_args[@]}"
python3 - <<'PY'
import json
from pathlib import Path
expected = {
  'challenge_module': 'Challenge',
  'solution_module': 'Solution',
  'theorem_names': ['SymplecticStaffordChallenge.universalStatement'],
  'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
}
if json.loads(Path('comparator.json').read_text()) != expected:
    raise SystemExit('comparator.json mismatch')
print('Palomar configuration: exact semantic theorem and approved axioms')
PY

# This checks the official sandbox and bundled tools before doing proof work.
# A local pass is evidence only; the registry's Linux runner remains decisive.
bash scripts/bootstrap-palomar-tools.sh
lean_bin=$(elan which lean)
bin_root=$(cd -- "$(dirname -- "$lean_bin")" && pwd)
export PATH="$bin_root:$PATH"
lake build SymplecticStafford.Paper > .lake/verification/palomar-semantic-build.log 2>&1
lake build Challenge > .lake/verification/palomar-challenge-build.log 2>&1
lake env bash -c '
  repo_root=$1
  export LEAN_PATH="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
  exec lean --trust=0 -o .lake/build/lib/lean/Solution.olean Solution.lean
' bash "$repo_root" > .lake/verification/palomar-solution-build.log 2>&1
./scripts/check-import-closure.sh Challenge
./scripts/check-import-closure.sh Solution
./scripts/check-import-closure.sh SymplecticStafford.Paper

# Palomar supplies a protected config rather than trusting external-kernel
# commands in a submitted repository. Reproduce that boundary locally.
protected_config=$(mktemp .lake/verification/palomar-protected.XXXXXX)
trap 'rm -f "$protected_config"' EXIT
python3 - "$protected_config" "$bin_root" <<'PY'
import json
import sys
from pathlib import Path
config = json.loads(Path('comparator.json').read_text())
config['definition_names'] = []
config['external_kernels'] = {
    'nanoda': [str(Path(sys.argv[2]) / 'nanoda_bin')],
    'con-ron': [str(Path(sys.argv[2]) / 'con-ron')],
}
Path(sys.argv[1]).write_text(json.dumps(config, indent=2) + '\n')
PY
bwrap_bin=$(command -v bwrap)
lake_lean_path=$(lake env bash -c 'printf "%s" "$LEAN_PATH"')
LEAN_PATH="$repo_root/.lake/build/lib/lean:$lake_lean_path" \
  COMPARATOR_BWRAP="$bwrap_bin" \
  "$bin_root/lake" comparator --config "$protected_config" > .lake/verification/comparator.log 2>&1
for marker in \
  'con-ron kernel accepts the solution' \
  'nanoda kernel accepts the solution' \
  'Lean default kernel accepts the solution' \
  'Your solution is okay!'; do
  if ! grep -Fxq "$marker" .lake/verification/comparator.log; then
    echo "Comparator omitted required acceptance marker: $marker" >&2
    exit 1
  fi
done
echo 'Local Comparator, con-ron, NanoDa, and Lean kernel replay passed; registry receipt still required'
