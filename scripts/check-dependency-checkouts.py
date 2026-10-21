#!/usr/bin/env python3
"""Check that Lake's pinned dependency metadata matches its source checkouts."""

from __future__ import annotations

import json
import subprocess
import tomllib
from pathlib import Path


def git(path: Path, *args: str) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(path), *args], text=True, stderr=subprocess.STDOUT
        ).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        output = getattr(exc, "output", "").strip()
        detail = f": {output}" if output else ""
        raise SystemExit(f"dependency checkout {path}: git {' '.join(args)} failed{detail}")


def main() -> int:
    lakefile = tomllib.loads(Path("lakefile.toml").read_text())
    manifest = json.loads(Path("lake-manifest.json").read_text())
    requires = {item["name"]: item for item in lakefile.get("require", [])}
    packages = {item["name"]: item for item in manifest.get("packages", [])}

    for name, requirement in requires.items():
        expected_rev = requirement.get("rev")
        expected_url = requirement.get("git")
        package = packages.get(name)
        if not expected_rev or not expected_url or not package:
            raise SystemExit(f"dependency metadata incomplete for {name}")
        if package.get("rev") != expected_rev or package.get("inputRev") != expected_rev:
            raise SystemExit(f"{name}: manifest revision does not match lakefile")

        checkout = Path(".lake/packages") / name
        if not (checkout / ".git").is_dir():
            raise SystemExit(f"{name}: checkout is missing or is not a git worktree")
        if git(checkout, "rev-parse", "HEAD") != expected_rev:
            raise SystemExit(f"{name}: checkout HEAD does not match pinned revision")
        if git(checkout, "status", "--porcelain"):
            raise SystemExit(f"{name}: checkout has local modifications")
        if git(checkout, "config", "--get", "remote.origin.url") != expected_url:
            raise SystemExit(f"{name}: origin URL does not match lakefile")

    # Lake also resolves transitive git packages.  Verify their checked-out
    # trees against the lock rather than trusting only the direct Mathlib pin.
    for package in packages.values():
        if package.get("type") != "git":
            continue
        name = package.get("name")
        expected_rev = package.get("rev")
        expected_url = package.get("url")
        if not name or not expected_rev or not expected_url:
            raise SystemExit("manifest contains an incomplete git package entry")
        checkout = Path(".lake/packages") / name
        if not (checkout / ".git").is_dir():
            raise SystemExit(f"{name}: checkout is missing or is not a git worktree")
        if git(checkout, "rev-parse", "HEAD") != expected_rev:
            raise SystemExit(f"{name}: checkout HEAD does not match pinned revision")
        if git(checkout, "status", "--porcelain"):
            raise SystemExit(f"{name}: checkout has local modifications")
        if git(checkout, "config", "--get", "remote.origin.url") != expected_url:
            raise SystemExit(f"{name}: origin URL does not match lakefile")

    print(f"dependency checkouts: verified {len(requires)} pinned clean worktree(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
