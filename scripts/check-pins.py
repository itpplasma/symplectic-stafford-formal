#!/usr/bin/env python3
"""Check dependency declarations against the reviewed release pin record."""
import json
import re
import tomllib
from pathlib import Path

record = json.loads(Path('dependency-pins.json').read_text())
if Path('lean-toolchain').read_text().strip() != record['lean_toolchain']:
    raise SystemExit('Lean toolchain pin mismatch')
requires = {r['name']: r for r in tomllib.loads(Path('lakefile.toml').read_text()).get('require', [])}
packages = {p['name']: p for p in json.loads(Path('lake-manifest.json').read_text()).get('packages', [])}
if set(requires) != set(record['packages']):
    raise SystemExit('direct dependency names differ from reviewed pin record')
for name, expected in record['packages'].items():
    url, rev = expected['url'], expected['revision']
    if not re.fullmatch('[0-9a-f]{40}', rev):
        raise SystemExit(f'{name}: revision is not a full commit')
    req, pkg = requires[name], packages.get(name, {})
    if req.get('git') != url or req.get('rev') != rev:
        raise SystemExit(f'{name}: lakefile pin mismatch')
    if pkg.get('rev') != rev or pkg.get('inputRev') != rev or pkg.get('url') != url:
        raise SystemExit(f'{name}: manifest pin mismatch')
print(f'pins: exact Lean and {len(requires)} reviewed direct dependency revisions')
