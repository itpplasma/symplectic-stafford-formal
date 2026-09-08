#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"
./scripts/check-resources.sh

tool_root=.lake/palomar-tools
source_root=$tool_root/src
bin_root=$tool_root/bin
mkdir -p "$source_root" "$bin_root"

lean_toolchain=leanprover/lean4:v4.33.0
comparator_rev=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_rev=15f6055e299ad5b89345e533cc2192f4cc00f659
nanoda_rev=68d5ca9db226849b41a6fff59d796ff19d0a8840
landrun_rev=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4

checkout_exact() {
  local name=$1 url=$2 revision=$3 destination=$source_root/$1
  if [[ -e "$destination" && ! -d "$destination/.git" ]]; then
    echo "refusing to overwrite non-repository $destination" >&2
    exit 1
  fi
  if [[ ! -d "$destination/.git" ]]; then
    git clone --filter=blob:none --no-checkout "$url" "$destination"
  fi
  git -C "$destination" remote set-url origin "$url"
  test -z "$(git -C "$destination" status --porcelain)" || {
    echo "$name checkout has local changes; clean it before bootstrapping" >&2
    exit 1
  }
  git -C "$destination" fetch --tags origin
  git -C "$destination" cat-file -e "$revision^{commit}" 2>/dev/null ||
    git -C "$destination" fetch origin "$revision"
  git -C "$destination" checkout --detach "$revision"
  test "$(git -C "$destination" rev-parse HEAD)" = "$revision"
}

checkout_exact comparator https://github.com/leanprover/comparator "$comparator_rev"
checkout_exact lean4export https://github.com/leanprover/lean4export "$lean4export_rev"
checkout_exact nanoda https://github.com/ammkrn/nanoda_lib "$nanoda_rev"
checkout_exact landrun https://github.com/zouuup/landrun "$landrun_rev"

(cd "$source_root/lean4export" && ELAN_TOOLCHAIN=$lean_toolchain lake build lean4export)
cp "$source_root/lean4export/.lake/build/bin/lean4export" "$bin_root/lean4export"

(cd "$source_root/comparator" &&
  test "$(tr -d '\r\n' < lean-toolchain)" = "leanprover/lean4:v4.34.0-rc1" &&
  ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0-rc1 lake build comparator)
cp "$source_root/comparator/.lake/build/bin/comparator" "$bin_root/comparator"

(cd "$source_root/nanoda" && CARGO_INCREMENTAL=0 cargo build --locked --release --bin nanoda_bin)
cp "$source_root/nanoda/target/release/nanoda_bin" "$bin_root/nanoda"

(cd "$source_root/landrun" && CGO_ENABLED=0 go build -mod=readonly -trimpath -o ../../bin/landrun ./cmd/landrun)

for tool in comparator lean4export nanoda landrun; do test -x "$bin_root/$tool"; done
cat >"$tool_root/revisions.txt" <<EOF
Comparator $comparator_rev
ComparatorLean leanprover/lean4:v4.34.0-rc1
lean4export $lean4export_rev
NanoDa $nanoda_rev
Landrun $landrun_rev
Lean $lean_toolchain
EOF
echo "Palomar tools built at $tool_root"
