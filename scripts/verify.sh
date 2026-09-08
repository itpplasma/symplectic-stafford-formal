#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
mode=${1:-full}
case "$mode" in
  --phase-i|--phase-ii|full) ;;
  *) echo "usage: $0 [--phase-i|--phase-ii|full]" >&2; exit 2 ;;
esac

./scripts/check-resources.sh
mkdir -p .lake/verification

python3 - <<'PY'
import json
import re
import tomllib
from pathlib import Path

expected_toolchain = 'leanprover/lean4:v4.33.0'
expected = {
    'mathlib': ('https://github.com/leanprover-community/mathlib4',
                'db584cd6d46c92f209a44c0f1c829460d327499d'),
    'algebraicAnalysis': ('https://github.com/itpplasma/algebraic-analysis.git',
                          '44921f5914c5dbd40d2d532c2867adce0f519cb9'),
    'stafford38Formal': ('https://github.com/itpplasma/stafford38-formal.git',
                         '784b59925beb9a480519142336bd6434f6eeef16'),
}
if Path('lean-toolchain').read_text().strip() != expected_toolchain:
    raise SystemExit('Lean toolchain pin mismatch')
lake = tomllib.loads(Path('lakefile.toml').read_text())
requires = {item['name']: item for item in lake.get('require', [])}
manifest = json.loads(Path('lake-manifest.json').read_text())
packages = {item['name']: item for item in manifest.get('packages', [])}
for name, (url, rev) in expected.items():
    req, pkg = requires.get(name), packages.get(name)
    if not req or req.get('git') != url or req.get('rev') != rev:
        raise SystemExit(f'{name}: lakefile pin mismatch')
    if not pkg or pkg.get('rev') != rev or pkg.get('inputRev') != rev:
        raise SystemExit(f'{name}: manifest pin mismatch')
    if not re.fullmatch(r'[0-9a-f]{40}', rev):
        raise SystemExit(f'{name}: revision is not a full commit')
print('pins: exact Lean, Mathlib, AlgebraicAnalysis, and Stafford38 revisions')
PY

python3 - <<'PY'
import re
from pathlib import Path

def code_without_comments_or_strings(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\': out.extend('  '); i += 2
            elif text[i] == '"': out.append(' '); string = False; i += 1
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            out.extend(' ' * (len(text) - i if end < 0 else end - i))
            i = len(text) if end < 0 else end
        elif text.startswith('/-', i): out.extend('  '); depth = 1; i += 2
        elif text[i] == '"': out.append(' '); string = True; i += 1
        else: out.append(text[i]); i += 1
    if depth or string: raise SystemExit('unterminated comment or string')
    return ''.join(out)

challenge = code_without_comments_or_strings(Path('Challenge.lean').read_text())
if re.findall(r'\b(?:sorry|admit)\b', challenge) != ['sorry']:
    raise SystemExit('Challenge.lean must contain exactly one deliberate sorry')
for source in Path('.').rglob('*.lean'):
    if any(part in {'.git', '.lake'} for part in source.parts): continue
    code = code_without_comments_or_strings(source.read_text())
    if source.name != 'Challenge.lean' and re.search(r'\b(?:sorry|admit)\b', code):
        raise SystemExit(f'proof hole outside Challenge.lean: {source}')
    if re.search(r'(?m)^\s*axiom\s+', code):
        raise SystemExit(f'project axiom declaration: {source}')
    if re.search(r'\bnative_decide\b|Lean\.ofReduceBool', code):
        raise SystemExit(f'forbidden proof mechanism: {source}')
print('source audit: one challenge hole, no project axioms or native shortcuts')
PY

lake build SymplecticStafford > .lake/verification/build.log 2>&1
# Build the Mathlib-only challenge as a Lake target, then replay Solution
# against the checked project library.  Asking Lake for both targets at once
# can unnecessarily schedule every inherited dependency target and collide
# with another checkout's cache; this still checks the exact Solution source
# and keeps the import-closure audit below independent.
lake build Challenge > .lake/verification/challenge-build.log 2>&1
lake env lean --trust=0 -o .lake/build/lib/lean/Solution.olean \
  Solution.lean > .lake/verification/solution-build.log 2>&1

endpoint_file=docs/phase-i-endpoints.txt
if [[ "$mode" == "full" || "$mode" == "--phase-ii" ]]; then
  endpoint_file=docs/endpoints.txt
fi
{
  echo 'import SymplecticStafford'
  [[ "$mode" == "full" || "$mode" == "--phase-ii" ]] && echo 'import Solution'
  sed 's/^/#print axioms /' "$endpoint_file"
} > .lake/verification/AxiomAudit.lean
lake env lean --trust=0 .lake/verification/AxiomAudit.lean > .lake/verification/axioms.log 2>&1
if grep -Eq 'sorryAx|admitAx|Lean\.ofReduceBool|(^|:) error:' .lake/verification/axioms.log; then
  echo 'axiom audit failed; see .lake/verification/axioms.log' >&2
  exit 1
fi

: > .lake/verification/consumers.log
for source in tests/*.lean; do
  lake env lean --trust=0 "$source" >> .lake/verification/consumers.log 2>&1
done
if grep -Eq 'sorryAx|admitAx|Lean\.ofReduceBool|(^|:) error:' .lake/verification/consumers.log; then
  echo 'consumer audit failed; see .lake/verification/consumers.log' >&2
  exit 1
fi

echo "verify.sh ($mode) passed for the implemented semantic/ordered checkpoint"
