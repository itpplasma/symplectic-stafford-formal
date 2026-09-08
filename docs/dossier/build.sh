#!/usr/bin/env bash
set -euo pipefail

here=$(cd -- "$(dirname -- "$0")" && pwd)
cd "$here"
python3 generate-proof-map.py
command -v latexmk >/dev/null || { echo 'dossier build: latexmk is required' >&2; exit 1; }
command -v lualatex >/dev/null || { echo 'dossier build: lualatex is required' >&2; exit 1; }
latexmk -lualatex -interaction=nonstopmode -halt-on-error \
  symplectic-stafford-description.tex
test -s symplectic-stafford-description.pdf
python3 build-manifest.py
echo "built $here/symplectic-stafford-description.pdf"
