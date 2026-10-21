#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
mode=${1:-full}
case "$mode" in
  --phase-i|--phase-ii|full|--legacy) ;;
  *) echo "usage: $0 [--phase-i|--phase-ii|full|--legacy]" >&2; exit 2 ;;
esac

project_lean() {
  lake env bash -c '
    repo_root=$1
    shift
    export LEAN_PATH="$repo_root/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
    exec lean "$@"
  ' bash "$repo_root" "$@"
}

./scripts/check-resources.sh
mkdir -p .lake/verification
python3 scripts/check-pins.py
python3 scripts/check-dependency-checkouts.py
python3 scripts/check-source-policy.py
map_args=(--formal-only)
if [[ -n "${PAPER_REPO:-}" ]]; then map_args=(); fi
python3 scripts/check-paper-lean-map.py "${map_args[@]}" --lean-audit .lake/verification/PaperLeanMapAudit.lean

# The release authority is the Mathlib-only Paper development. Historical
# scaffolds and their fixtures can be replayed explicitly with --legacy.
build_target=SymplecticStafford.Paper
endpoint_file=docs/endpoints.txt
if [[ "$mode" == "--legacy" ]]; then
  build_target=SymplecticStafford
  endpoint_file=docs/legacy-endpoints.txt
fi
lake build "$build_target" > .lake/verification/build.log 2>&1
lake build Challenge > .lake/verification/challenge-build.log 2>&1
project_lean --trust=0 -o .lake/build/lib/lean/Solution.olean \
  Solution.lean > .lake/verification/solution-build.log 2>&1
./scripts/check-import-closure.sh Challenge
./scripts/check-import-closure.sh Solution
./scripts/check-import-closure.sh SymplecticStafford.Paper
project_lean --trust=0 .lake/verification/PaperLeanMapAudit.lean \
  > .lake/verification/paper-lean-map.log 2>&1
project_lean --trust=0 .lake/verification/PaperLeanMapAudit.challenge.lean \
  >> .lake/verification/paper-lean-map.log 2>&1
{
  echo 'module'
  echo 'import SymplecticStafford.Paper'
  [[ "$mode" == "--legacy" ]] && echo 'import SymplecticStafford'
  echo 'import Solution'
  sed 's/^/#print axioms /' "$endpoint_file"
} > .lake/verification/AxiomAudit.lean
project_lean --trust=0 .lake/verification/AxiomAudit.lean > .lake/verification/axioms.log 2>&1
python3 scripts/check-axiom-closure.py --endpoints "$endpoint_file" .lake/verification/axioms.log

consumers=(tests/PaperTargetAOracle.lean)
if [[ "$mode" == "--legacy" ]]; then consumers=(tests/*.lean); fi
: > .lake/verification/consumers.log
for source in "${consumers[@]}"; do
  project_lean --trust=0 "$source" >> .lake/verification/consumers.log 2>&1
done
python3 scripts/check-axiom-closure.py .lake/verification/consumers.log

echo "verify.sh ($mode) passed: Target A proof, mapped declarations, axioms, import closure, and consumers"
