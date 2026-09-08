#!/usr/bin/env bash
set -euo pipefail

manifest="${1:-release-gates.yaml}"
[[ -f "$manifest" ]] || { echo "release gate: missing $manifest" >&2; exit 2; }
python3 - "$manifest" <<'PY'
import pathlib, sys
try:
    import yaml
except ImportError:
    raise SystemExit("release gate: PyYAML is required")

manifest_path = pathlib.Path(sys.argv[1])
data = yaml.safe_load(manifest_path.read_text()) or {}
phases = data.get("phases", {})
required = data.get("publication", {}).get("required_phases", [])
if not required:
    raise SystemExit("release gate: no required phases declared")
errors = []
for name in required:
    phase = phases.get(name)
    if not isinstance(phase, dict) or phase.get("status") != "verified":
        errors.append(f"{name}: status is not verified")
        continue
    evidence_name = phase.get("evidence")
    evidence = pathlib.Path(evidence_name) if evidence_name else None
    if evidence is None or not evidence.is_file():
        errors.append(f"{name}: missing evidence file {evidence_name!r}")
        continue
    record = yaml.safe_load(evidence.read_text()) or {}
    if record.get("phase") != name or record.get("result") != "pass":
        errors.append(f"{name}: evidence must declare phase and result: pass")
if errors:
    print("release gate: publication is NOT ready")
    for error in errors: print(f" - {error}")
    raise SystemExit(1)
print("release gate: Phase I, Phase II, and Palomar evidence verified")
PY
