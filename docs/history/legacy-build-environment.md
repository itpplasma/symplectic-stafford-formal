# Frozen legacy build environment

The historical scaffolds are retained as research history. They are outside
the current Target A build and have no supported replay mode in the active
package. The current package has exactly one direct dependency, Mathlib;
AlgebraicAnalysis and Stafford38 were removed from the active requirements
because their unused dependency modules shadowed the root Challenge during
Palomar preflight.

Replay the retired scaffolds from the immutable pre-migration checkout
[dccff0d8fe723ec1478d1f63bbbdf648ba240bfa](https://github.com/itpplasma/symplectic-stafford-formal/tree/dccff0d8fe723ec1478d1f63bbbdf648ba240bfa).
Its `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` and verifier scripts
are the authority for the historical environment. Do not add these dependencies
back to the current package to replay historical files.

| Direct component | Frozen revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | db584cd6d46c92f209a44c0f1c829460d327499d |
| [AlgebraicAnalysis](https://github.com/itpplasma/algebraic-analysis) | add0a80d865c88fe9cbc6901bda08a636ce188f9 |
| [Stafford38](https://github.com/itpplasma/stafford38-formal) | 213ae2073030c8a897087152a616b8f8c1292df2 |

The frozen manifest also records every transitive dependency revision. Preserve
it unchanged rather than resolving the dependency branches afresh.

For a separate historical clone:

```sh
git clone https://github.com/itpplasma/symplectic-stafford-formal.git \
  /tmp/symplectic-stafford-legacy
cd /tmp/symplectic-stafford-legacy
git checkout --detach dccff0d8fe723ec1478d1f63bbbdf648ba240bfa
lake exe cache get
bash scripts/verify.sh full
```

These are replay instructions, not a claim that this document's preparation
reran or passed that historical checkout. A replay can require access to its
pinned historical repositories and toolchain.

At the frozen revision, native `verify.sh` supports `full`, `--phase-i` and
`--phase-ii`. It checks exact Lean and direct-dependency pins and checkout
identities, audits all project Lean sources, builds the `SymplecticStafford`
umbrella and Challenge, and replays Solution with `--trust=0`. Full mode uses
`docs/endpoints.txt` for the axiom audit and runs every `tests/*.lean` consumer
with `--trust=0`; phase I uses its own endpoint list, while phase II additionally
runs its axiom-closure checker. This is the pre-migration build scope, including
historical scaffolds and consumers. It is not the current Mathlib-only Target A
verification contract.

The 30 September local verification record and any later local or CI passes
certify only their recorded source and dependency snapshots. Passes before
removing the two active dependencies do not certify the resulting package.
The current dependency-pruned checkout requires a fresh native rebuild,
project CI and complete official Palomar preflight before submission. No
historical pass is promoted by this document.
