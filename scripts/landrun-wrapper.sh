#!/usr/bin/env bash
set -euo pipefail

landrun_binary=${PALOMAR_LANDRUN_BIN:?PALOMAR_LANDRUN_BIN must name the pinned Landrun binary}
args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    --unrestricted-*|-unrestricted-*)
      echo "refusing Landrun sandbox widening: $1" >&2; exit 2 ;;
    --log-level|--ro|--rox|--rw|--rwx|--unix|--bind-tcp|--connect-tcp|--env)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      args+=("$1" "$2"); shift 2 ;;
    --best-effort|-ldd|--ldd|-add-exec|--add-exec|--ignore-missing|--log-disable-originating|--log-enable-subprocesses|--log-disable-subdomains)
      args+=("$1"); shift ;;
    -*) echo "unrecognized Landrun option: $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || { echo 'Landrun received no command' >&2; exit 2; }
exec "$landrun_binary" "${args[@]}" -- "$@"
