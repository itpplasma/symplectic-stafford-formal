#!/usr/bin/env python3
"""Write provenance for one companion-dossier build."""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUTPUT = Path(os.environ.get(
    "DOSSIER_MANIFEST",
    str(HERE / "symplectic-stafford-description.build-manifest.json"),
))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def command(*args: str) -> str:
    try:
        return subprocess.run(
            args, check=True, capture_output=True, text=True
        ).stdout.strip().splitlines()[0]
    except (OSError, subprocess.CalledProcessError, IndexError):
        return "unavailable"


def git(*args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args], cwd=ROOT, check=True,
            capture_output=True, text=True
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unavailable"


manifest = {
    "project": "symplectic-stafford-formal",
    "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    "source_commit": git("rev-parse", "HEAD"),
    "source_worktree_clean": not bool(git("status", "--porcelain")),
    "inputs": {
        "proof_graph": {
            "path": "docs/proof-graph.yaml",
            "sha256": sha256(ROOT / "docs/proof-graph.yaml"),
        },
        "tex": {
            "path": "docs/dossier/symplectic-stafford-description.tex",
            "sha256": sha256(HERE / "symplectic-stafford-description.tex"),
        },
        "generated_map": {
            "path": "docs/dossier/proof-map.generated.tex",
            "sha256": sha256(HERE / "proof-map.generated.tex"),
        },
        "claim_register": {
            "path": "docs/dossier/claim-register.generated.tex",
            "sha256": sha256(HERE / "claim-register.generated.tex"),
        },
        "lakefile": {
            "path": "lakefile.toml",
            "sha256": sha256(ROOT / "lakefile.toml"),
        },
        "lake_manifest": {
            "path": "lake-manifest.json",
            "sha256": sha256(ROOT / "lake-manifest.json"),
        },
    },
    "engines": {
        "python": command("python3", "--version"),
        "latexmk": command("latexmk", "--version"),
        "lualatex": command("lualatex", "--version"),
    },
    "artifact": {
        "path": "docs/dossier/symplectic-stafford-description.pdf",
        "sha256": sha256(HERE / "symplectic-stafford-description.pdf"),
    },
}
OUTPUT.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
print(f"wrote {OUTPUT}")
