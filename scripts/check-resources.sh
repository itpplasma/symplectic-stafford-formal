#!/usr/bin/env bash
set -euo pipefail

MIN_FREE_BYTES="${MIN_FREE_BYTES:-1073741824}"
MIN_FREE_INODES="${MIN_FREE_INODES:-10000}"
CHECK_DIRS=("${CHECK_DIRS:-.}" "/tmp")
if [[ -n "${TMPDIR:-}" && "${TMPDIR}" != "/tmp" ]]; then CHECK_DIRS+=("$TMPDIR"); fi

for directory in "${CHECK_DIRS[@]}"; do
  [[ -d "$directory" ]] || { echo "resource check: missing directory: $directory" >&2; exit 2; }
  free_bytes="$(df -P -B1 "$directory" | awk 'NR==2 {print $4}')"
  free_inodes="$(df -Pi "$directory" | awk 'NR==2 {print $4}')"
  if (( free_bytes < MIN_FREE_BYTES )); then
    echo "resource check: less than ${MIN_FREE_BYTES} free bytes on $directory" >&2; exit 1
  fi
  if (( free_inodes < MIN_FREE_INODES )); then
    echo "resource check: less than ${MIN_FREE_INODES} free inodes on $directory" >&2; exit 1
  fi
  echo "resource check: $directory has ${free_bytes} free bytes and ${free_inodes} free inodes"
done
