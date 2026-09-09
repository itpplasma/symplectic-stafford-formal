#!/usr/bin/env python3
"""Fail closed when an endpoint axiom report exceeds the Phase II allowlist."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


ALLOWED_PHASE_II = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(
    r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms"
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase-ii", action="store_true")
    parser.add_argument("log", type=Path)
    args = parser.parse_args()

    text = args.log.read_text()
    reports = list(AXIOM_REPORT.finditer(text))
    if "depends on axioms:" in text and not reports:
        print("axiom audit: malformed axiom report", file=sys.stderr)
        return 1

    axioms = {
        item.strip()
        for report in reports
        for item in (report.group(1) or "").split(",")
        if item.strip()
    }
    forbidden = sorted(axioms - ALLOWED_PHASE_II)
    if args.phase_ii and forbidden:
        print(
            "axiom audit: Phase II endpoint depends on unapproved axioms: "
            + ", ".join(forbidden),
            file=sys.stderr,
        )
        return 1
    print(
        f"axiom audit: checked {len(reports)} endpoint report(s); "
        f"axioms={sorted(axioms)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
