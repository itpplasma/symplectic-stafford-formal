#!/usr/bin/env python3
"""Audit committed/project Lean sources, including unused historical files."""
from __future__ import annotations

import re
import subprocess
from pathlib import Path


def code_without_comments_or_strings(text: str) -> str:
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
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
    if depth or string:
        raise ValueError('unterminated comment or string')
    return ''.join(out)


def main() -> None:
    sources = subprocess.check_output(
        ['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard', '--', '*.lean']
    ).decode().split('\0')
    sources = sorted({s for s in sources if s and not set(Path(s).parts) & {'.git', '.lake'}})
    if 'Challenge.lean' not in sources:
        raise SystemExit('source audit: missing Challenge.lean')
    for name in sources:
        path = Path(name)
        if path.is_symlink() or not path.is_file():
            raise SystemExit(f'source audit: not a regular file: {path}')
        data = path.read_bytes()
        text = data.decode('utf-8')
        physical_lines = data.count(b'\n') + int(bool(data) and not data.endswith(b'\n'))
        if name == 'Challenge.lean' and (physical_lines > 1000 or len(data) > 100 * 1024):
            raise SystemExit('source audit: Challenge exceeds Palomar 1000-line/100 KiB limit')
        if physical_lines > 10000:
            raise SystemExit(f'source audit: exceeds Palomar 10000-line limit: {path}')
        try:
            code = code_without_comments_or_strings(text)
        except ValueError as exc:
            raise SystemExit(f'{path}: {exc}') from exc
        if name != 'lakefile.lean' and not re.match(r'\s*module\b', code):
            raise SystemExit(f'source audit: first command must be module: {path}')
        holes = re.findall(r'\b(?:sorry|admit)\b', code)
        if holes != (['sorry'] if name == 'Challenge.lean' else []):
            raise SystemExit(f'source audit: unexpected proof holes: {path}')
        if re.search(r'\baxiom\s+', code):
            raise SystemExit(f'source audit: project axiom declaration: {path}')
        if re.search(r'\bnative_decide\b|Lean\.ofReduceBool', code):
            raise SystemExit(f'source audit: forbidden proof mechanism: {path}')
    print(f'source audit: {len(sources)} Lean files; module/line policy; one challenge hole; no axioms/native shortcuts')


if __name__ == '__main__':
    main()
