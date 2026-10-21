#!/usr/bin/env python3
"""Fail closed on missing endpoint reports or axioms outside the allowlist."""
from __future__ import annotations

import argparse
import re
from pathlib import Path

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--phase-ii', action='store_true', help='compatibility alias; allowlist always enforced')
    parser.add_argument('--endpoints', type=Path)
    parser.add_argument('log', type=Path)
    args = parser.parse_args()
    text = args.log.read_text()
    reports = list(REPORT.finditer(text))
    if not reports:
        raise SystemExit('axiom audit: no complete axiom reports')
    if len(reports) != len(re.findall(r'depends on axioms:|does not depend on any axioms', text)):
        raise SystemExit('axiom audit: malformed axiom report')
    if re.search(r'sorryAx|admitAx|Lean\.ofReduceBool|(^|:) error:', text, re.M):
        raise SystemExit('axiom audit: proof hole, native shortcut, or Lean error')
    if args.endpoints:
        expected = [line.strip() for line in args.endpoints.read_text().splitlines() if line.strip()]
        actual = [report.group(1) for report in reports]
        if actual != expected:
            raise SystemExit(f'axiom audit: endpoint reports differ: expected {expected}, got {actual}')
    axioms = {item.strip() for report in reports for item in (report.group(2) or '').split(',') if item.strip()}
    if axioms - ALLOWED:
        raise SystemExit(f'axiom audit: unapproved axioms: {sorted(axioms - ALLOWED)}')
    print(f'axiom audit: {len(reports)} endpoint reports; axioms={sorted(axioms)}')


if __name__ == '__main__':
    main()
