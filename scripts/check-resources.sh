#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PYTHON'
import os
import shutil
from pathlib import Path

minimum_bytes = int(os.environ.get("MIN_FREE_BYTES", "1073741824"))
minimum_inodes = int(os.environ.get("MIN_FREE_INODES", "10000"))
directories = [os.environ.get("CHECK_DIRS", "."), "/tmp"]
if os.environ.get("TMPDIR"):
    directories.append(os.environ["TMPDIR"])
seen = set()
for directory in directories:
    path = Path(directory)
    if not path.is_dir():
        raise SystemExit(f"resource check: missing directory: {directory}")
    resolved = path.resolve()
    if resolved in seen:
        continue
    seen.add(resolved)
    available_bytes = shutil.disk_usage(path).free
    available_inodes = os.statvfs(path).f_favail
    if available_bytes < minimum_bytes:
        raise SystemExit(f"resource check: less than {minimum_bytes} free bytes on {directory}")
    if available_inodes < minimum_inodes:
        raise SystemExit(f"resource check: less than {minimum_inodes} free inodes on {directory}")
    print(f"resource check: {directory} has {available_bytes} free bytes and {available_inodes} free inodes")
PYTHON
