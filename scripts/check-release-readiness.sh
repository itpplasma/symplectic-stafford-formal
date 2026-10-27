#!/usr/bin/env bash
set -euo pipefail

manifest="${1:-release-gates.yaml}"
[[ -f "$manifest" ]] || { echo "release gate: missing $manifest" >&2; exit 2; }
python3 - "$manifest" <<'PY'
import hashlib, io, json, pathlib, re, subprocess, sys, tarfile
try:
    import yaml
except ImportError:
    raise SystemExit("release gate: PyYAML is required")

manifest_path = pathlib.Path(sys.argv[1]).resolve()
repo_root = manifest_path.parent
data = yaml.safe_load(manifest_path.read_text()) or {}
phases = data.get("phases", {})
required = data.get("publication", {}).get("required_phases", [])
if not required:
    raise SystemExit("release gate: no required phases declared")
errors = []
if set(required) != {"phase_i", "phase_ii", "palomar"}:
    errors.append("publication: all three verification phases are required")
inventory_path = repo_root / "evidence/source-inventory.json"
inventory = {}
try:
    inventory = json.loads(inventory_path.read_text())
except (OSError, ValueError):
    errors.append("source inventory: missing or invalid evidence/source-inventory.json")
source_commit = inventory.get("source_commit", "")
if inventory.get("schema") != "symplectic-stafford-source-inventory/v1":
    errors.append("source inventory: unsupported schema")
if not isinstance(source_commit, str) or not re.fullmatch("[0-9a-f]{40}", source_commit):
    errors.append("source inventory: source_commit must be a full commit")
if data.get("verification_source_commit") != source_commit or not source_commit:
    errors.append("source inventory: manifest verification_source_commit differs")
files = inventory.get("files")
if not isinstance(files, dict):
    errors.append("source inventory: files must map paths to SHA256 digests")
    files = {}
try:
    tracked = subprocess.check_output(
        ["git", "-C", str(repo_root), "ls-files", "-z"], text=True
    ).split("\0")
except subprocess.CalledProcessError:
    raise SystemExit("release gate: cannot enumerate tracked source files")
root_inputs = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "dependency-pins.json", "comparator.json", "LICENSE", "NOTICE"}
def selected(name):
    path = pathlib.PurePosixPath(name)
    return bool(name) and (path.suffix == ".lean" or path.parts[0] in {"scripts", "tests"}
        or name in root_inputs or (path.parent == pathlib.PurePosixPath(".github/workflows") and path.suffix == ".yml"))
expected_files = {name for name in tracked if selected(name)}
if not root_inputs <= expected_files:
    errors.append("source inventory: required root source files are not all tracked")
if set(files) != expected_files:
    errors.append(f"source inventory: coverage differs ({len(expected_files - set(files))} missing, {len(set(files) - expected_files)} extra files)")
committed_files = {}
if isinstance(source_commit, str) and re.fullmatch("[0-9a-f]{40}", source_commit):
    archive = subprocess.run(
        ["git", "-C", str(repo_root), "archive", "--format=tar", source_commit, "--", *sorted(expected_files)],
        capture_output=True,
    )
    if archive.returncode:
        errors.append("source inventory: cannot read inventoried sources at source_commit")
    else:
        with tarfile.open(fileobj=io.BytesIO(archive.stdout), mode="r:") as tree:
            committed_files = {entry.name: hashlib.sha256(tree.extractfile(entry).read()).hexdigest()
                               for entry in tree.getmembers() if entry.isfile()}
        if set(committed_files) != expected_files:
            errors.append("source inventory: source_commit file coverage differs")
for name in sorted(expected_files & files.keys()):
    digest = files.get(name)
    path = repo_root / name
    if not isinstance(digest, str) or not re.fullmatch("[0-9a-f]{64}", digest):
        errors.append(f"source inventory: missing/invalid SHA256 for {name}")
    elif committed_files.get(name) != digest:
        errors.append(f"source inventory: digest differs from source_commit for {name}")
    if isinstance(digest, str) and (path.is_symlink() or not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest):
        errors.append(f"source inventory: source drift in {name}")
publication = data.get("publication", {})
if publication.get("enabled") is not True:
    errors.append("publication: enabled is not true")
target = data.get("target")
if target != "SS-all-original-affine":
    errors.append(f"target: expected SS-all-original-affine, got {target!r}")
for name in required:
    phase = phases.get(name)
    if not isinstance(phase, dict) or phase.get("status") != "verified":
        errors.append(f"{name}: status is not verified")
        continue
    evidence_name = phase.get("evidence")
    evidence = (manifest_path.parent / evidence_name) if evidence_name else None
    if evidence is None or not evidence.is_file():
        errors.append(f"{name}: missing evidence file {evidence_name!r}")
        continue
    record = yaml.safe_load(evidence.read_text()) or {}
    if record.get("phase") != name or record.get("result") != "pass":
        errors.append(f"{name}: evidence must declare phase and result: pass")
    if record.get("source_commit") != source_commit or not source_commit:
        errors.append(f"{name}: evidence source_commit differs from source inventory")
    checks = record.get("checks")
    if not isinstance(checks, dict):
        errors.append(f"{name}: evidence must provide a checks mapping")
    else:
        for check in phase.get("required_checks", []):
            if checks.get(check) != "pass":
                errors.append(f"{name}: required check {check!r} is not pass")
if errors:
    print("release gate: publication is NOT ready")
    for error in errors[:20]: print(f" - {error}")
    if len(errors) > 20: print(f" - ... and {len(errors) - 20} further error(s)")
    raise SystemExit(1)
print("release gate: Target A closure, independent replay, and Palomar evidence verified")
PY
