#!/usr/bin/env python3
"""Check source identity and references, never infer semantic equivalence from hashes.

Run the generated Lean audit after building to check mapped declarations against
Lean's environment. Paper inputs are read at the recorded Git commit, so local
uncommitted manuscript edits cannot silently redefine the comparison baseline.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent


def fail(message: str) -> None:
    raise SystemExit('paper/Lean map: ' + message)


def safe_path(name: str) -> str:
    path = PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or not name or '\\' in name:
        fail(f'unsafe source path {name!r}')
    return name


def verify_hash(data: bytes, record: dict) -> None:
    expected = record.get('sha256', '')
    if not re.fullmatch('[0-9a-f]{64}', expected):
        fail(f'invalid source fingerprint: {record.get("path")}')
    if hashlib.sha256(data).hexdigest() != expected:
        fail(f'source drift: {record["path"]}; review correspondence and update the map explicitly')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--map', type=Path, default=ROOT / 'docs/paper-lean-map.json')
    parser.add_argument('--paper-root', type=Path, default=os.environ.get('PAPER_REPO'))
    parser.add_argument('--lean-audit', type=Path)
    parser.add_argument('--formal-only', action='store_true', help='public replay: skip private paper Git-object/hash/anchor checks explicitly')
    args = parser.parse_args()
    data = json.loads(args.map.read_text())
    if data.get('schema_version') != 1:
        fail('unsupported schema version')
    paper, formal = data['sources']['paper'], data['sources']['formal']
    if paper.get('repository') != 'itpplasma/symplectic-stafford' or formal.get('repository') != 'itpplasma/symplectic-stafford-formal':
        fail('unexpected source repository')
    commit = paper.get('commit', '')
    if not re.fullmatch('[0-9a-f]{40}', commit):
        fail('paper revision must be an immutable full Git commit')
    paper_root = args.paper_root
    if paper_root is None:
        paper_root = next((p for p in [ROOT.parent / 'symplectic-stafford', ROOT / '.lake/paper-source'] if (p / '.git').exists()), None)
    if paper_root is None and not args.formal_only:
        fail('paper checkout missing; use --paper-root or PAPER_REPO with the recorded commit available')
    paper_files = {}
    for record in paper['files']:
        name = safe_path(record['path'])
        if name in paper_files:
            fail(f'duplicate paper source: {name}')
        if args.formal_only:
            if not re.fullmatch('[0-9a-f]{64}', record.get('sha256', '')):
                fail(f'invalid paper source fingerprint: {name}')
            paper_files[name] = None
            continue
        result = subprocess.run(['git', '-C', str(paper_root), 'show', f'{commit}:{name}'], capture_output=True)
        if result.returncode:
            fail(f'cannot read {name} at paper revision {commit}')
        verify_hash(result.stdout, record)
        paper_files[name] = result.stdout.decode()
    formal_files = set()
    for record in formal['files']:
        name = safe_path(record['path'])
        if name in formal_files:
            fail(f'duplicate formal source: {name}')
        formal_files.add(name)
        path = ROOT / name
        if path.is_symlink() or not path.is_file():
            fail(f'missing/nonregular formal source: {name}')
        verify_hash(path.read_bytes(), record)
    required = {'Challenge.lean', 'Solution.lean', 'SymplecticStafford/Paper.lean', 'comparator.json', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'dependency-pins.json'}
    required.update(str(path.relative_to(ROOT)) for path in (ROOT / 'SymplecticStafford/Paper').rglob('*.lean'))
    if required - formal_files:
        fail(f'protected formal input(s) absent: {sorted(required - formal_files)}')
    ids = set()
    declarations = set()
    declaration_pattern = re.compile(r'[A-Za-z_\u0080-\uffff][A-Za-z0-9_\u0080-\uffff]*(?:\.[A-Za-z_\u0080-\uffff][A-Za-z0-9_\u0080-\uffff]*)*\Z')
    for item in data['items']:
        if item['id'] in ids:
            fail(f'duplicate item id: {item["id"]}')
        ids.add(item['id'])
        for ref in item['paper']:
            name = safe_path(ref['path'])
            if name not in paper_files or not ref['anchor'] or (not args.formal_only and ref['anchor'] not in paper_files[name]):
                fail(f'paper reference missing at pinned revision: {item["id"]}: {ref}')
        for ref in item['lean']:
            name = safe_path(ref['file'])
            if name not in formal_files or not declaration_pattern.fullmatch(ref['name']):
                fail(f'invalid/unprotected Lean reference: {item["id"]}: {ref}')
            declarations.add((name, ref['name']))
    for item in data['items']:
        if set(item.get('depends_on', [])) - ids:
            fail(f'unknown dependency in {item["id"]}')
    dependencies = {item['id']: item.get('depends_on', []) for item in data['items']}
    visiting, visited = set(), set()
    def visit(item_id):
        if item_id in visiting:
            fail(f'cyclic dependency at {item_id}')
        if item_id in visited:
            return
        visiting.add(item_id)
        for dependency in dependencies[item_id]:
            visit(dependency)
        visiting.remove(item_id)
        visited.add(item_id)
    for item_id in dependencies:
        visit(item_id)
    critical = data['critical_endpoints']
    mapped = {name for _, name in declarations}
    endpoints = (ROOT / 'docs/endpoints.txt').read_text().splitlines()
    if len(set(critical)) != len(critical) or set(critical) - mapped or set(endpoints) - set(critical):
        fail('critical endpoints must be unique, mapped, and include every audited current endpoint')
    if args.lean_audit:
        # Challenge and Solution deliberately repeat declaration names. Their
        # environments must remain separate; only Solution is imported here.
        args.lean_audit.parent.mkdir(parents=True, exist_ok=True)
        for challenge in (False, True):
            selected = sorted((file, name) for file, name in declarations if (file == 'Challenge.lean') == challenge)
            imports = 'import Challenge\n' if challenge else 'import SymplecticStafford.Paper\nimport Solution\n'
            audit = 'module\n' + imports + 'import Lean.Elab.Command\n\n'
            for file, name in selected:
                module = '.'.join(PurePosixPath(file).with_suffix('').parts)
                audit += f'#check {name}\n'
                audit += ('run_cmd do\n  let env ← Lean.getEnv\n'
                          f'  match env.getModuleIdxFor? `{name} with\n'
                          '  | some idx =>\n'
                          f'    unless env.header.moduleNames[idx.toNat]! == `{module} do\n'
                          f'      throwError "map declaration owner differs: {name}"\n'
                          f'  | none => throwError "map declaration owner missing: {name}"\n')
            destination = args.lean_audit.with_suffix('.challenge.lean') if challenge else args.lean_audit
            destination.write_text(audit)
    if args.formal_only:
        print('paper/Lean map: formal-only public replay; private paper Git-object/hash/anchor checks NOT performed')
    print(f'paper/Lean map: {len(ids)} items; {len(paper_files)} recorded paper and {len(formal_files)} formal inputs; {len(declarations)} mapped references; semantic correspondence requires review')


if __name__ == '__main__':
    main()
