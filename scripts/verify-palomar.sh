#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
./scripts/check-resources.sh
tool_root=.lake/palomar-tools
bin_root=$tool_root/bin
if [[ ! -x "$bin_root/comparator" || ! -x "$bin_root/lean4export" ||
      ! -x "$bin_root/nanoda" || ! -x "$bin_root/landrun" ]]; then
  echo "missing Palomar tools; run scripts/bootstrap-palomar-tools.sh" >&2
  exit 1
fi

expected='Comparator 575674928e239f5bc452aab72d1dd7b0f1326494
ComparatorLean leanprover/lean4:v4.34.0-rc1
lean4export 15f6055e299ad5b89345e533cc2192f4cc00f659
NanoDa 68d5ca9db226849b41a6fff59d796ff19d0a8840
Landrun 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
Lean leanprover/lean4:v4.33.0'
[[ "$(cat "$tool_root/revisions.txt")" == "$expected" ]] || {
  echo 'Palomar tool revision record mismatch' >&2; exit 1;
}

python3 - <<'PY'
import json
from pathlib import Path
expected = {
  'challenge_module': 'Challenge',
  'solution_module': 'Solution',
  'theorem_names': ['SymplecticStaffordChallenge.universalStatement'],
  'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
  'enable_nanoda': True,
}
if json.loads(Path('comparator.json').read_text()) != expected:
    raise SystemExit('comparator.json mismatch')
print('Palomar configuration: exact semantic theorem and approved axioms')
PY

lake build SymplecticStafford > .lake/verification/palomar-semantic-build.log 2>&1
lake build Challenge > .lake/verification/palomar-challenge-build.log 2>&1
lake env lean --trust=0 -o .lake/build/lib/lean/Solution.olean \
  Solution.lean > .lake/verification/palomar-solution-build.log 2>&1
./scripts/check-import-closure.sh Challenge
./scripts/check-import-closure.sh Solution

# The Stafford38 dependency also exports a module named `Challenge`.  Lake's
# normal dependency-first `LEAN_PATH` therefore resolves that module before our
# local semantic challenge.  Run the comparator directly with the project
# artifact directory prepended, while retaining Lake's dependency paths and
# executable search path.
lake_path=$(lake env bash -c 'printf "%s" "$PATH"')
lake_lean_path=$(lake env bash -c 'printf "%s" "$LEAN_PATH"')
PATH="$lake_path" LEAN_PATH="$repo_root/.lake/build/lib/lean:$lake_lean_path" \
  PALOMAR_LANDRUN_BIN="$(cd "$bin_root" && pwd)/landrun" \
  COMPARATOR_LANDRUN="$repo_root/scripts/landrun-wrapper.sh" \
  COMPARATOR_LEAN4EXPORT="$(cd "$bin_root" && pwd)/lean4export" \
  COMPARATOR_NANODA="$(cd "$bin_root" && pwd)/nanoda" \
  "$bin_root/comparator" comparator.json > .lake/verification/comparator.log 2>&1

grep -Fq 'nanoda kernel accepts the solution' .lake/verification/comparator.log
grep -Fq 'Lean default kernel accepts the solution' .lake/verification/comparator.log
grep -Fq 'Your solution is okay!' .lake/verification/comparator.log
echo 'Palomar Comparator, NanoDa, and Lean kernel verification passed'
