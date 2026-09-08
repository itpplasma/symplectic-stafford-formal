# Symplectic Stafford formalization

This is the Lean workspace for the symplectic same-divisor programme. It
keeps the target in the exact noncommutative order

```text
1 = d * R + F * d * S
```

The current checked checkpoint formalizes the original-ring semantic contract,
right-ideal quotient action, opposite transport, ordered affine identities,
conditional right-denominator clearing, and a finite division-coordinate
scalar-pencil lemma. The general finite-length activated-pencil and original-U
source-selection bridges remain open. It deliberately
does not claim the universal higher-dimensional theorem from the companion
paper. The source-selection, filtered-localization, assembly, and terminal
Phase I/II gates remain open in `PLAN.md`; the corresponding files are
conditional scaffolds rather than producer proofs.

The map labels these three interfaces LEAN-SCAFFOLD: filtered chart/power
clearing, divisor-indexed assembly from supplied cofactors, and strong
finite-test induction contracts with integer bounds. Their precise hypotheses
appear in the linked claim register; M02–M11 remain open.

## Reproducible setup

The workspace uses Lean and Mathlib v4.33.0, matching the checked Stafford38
formal project. Exact build revisions are in the lock files:

| Dependency | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| AlgebraicAnalysis | `44921f5914c5dbd40d2d532c2867adce0f519cb9` |
| Stafford38 formal | `784b59925beb9a480519142336bd6434f6eeef16` |

With Lean and Lake installed, run the checkpoint build and consumers:

```sh
lake build
lake env lean --trust=0 tests/StatementOracle.lean
lake env lean --trust=0 tests/S1ConsequencesOracle.lean
./scripts/verify.sh --phase-i
```

`scripts/check-resources.sh` runs before long checks and refuses to proceed
when the checkout, `/tmp`, or `TMPDIR` lacks the configured byte or inode
headroom. The shared dependency cache is intentionally external to this
checkout; do not commit `.lake` or generated `.olean` files.

## Companion description and proof map

[`docs/dossier/symplectic-stafford-description.tex`](docs/dossier/symplectic-stafford-description.tex)
is a standalone LuaLaTeX dossier. It contains a clickable TikZ proof map,
the paper-to-`Challenge.lean` comparison, the principal proof-architecture
interfaces, and verbatim Challenge/Solution listings. Build it with:

```sh
docs/dossier/build.sh
```

The build also writes an ignored `symplectic-stafford-description.build-manifest.json`
with input hashes, engine versions, source commit, and the PDF hash; the release
runbook archives it beside the PDF and checksum file.

The paper source is Markdown in the private research repository, not TeX; the
dossier records that boundary explicitly rather than fabricating a source
correspondence. `docs/proof-graph.yaml` is the machine-readable status graph;
the build regenerates the map and linked claim register from it. The paper
source is frozen at `502b65a1dea53cac52220a08e321bfba525bc72e`, with its
updated terminal instructions at `e3c7077d3d51772d97d8e72bb219a8fc36765682`.

[`docs/phase-instructions.md`](docs/phase-instructions.md) assigns the final
paper's M01–M11 obligations to parallel lanes. Both recursive calls use P_h
to prove P_(h+1); every finite local test is retained. Phase I discharges all
project-owned obligations, and Phase II also discharges registered literature
leaves. The final target is all-dimensional SS-all; `Contract.lean` contains
only a dimension-parametric semantic scaffold with historical B2 fields, not
the paper's full filtered-algebra encoding.

## Palomar and release status

`Challenge.lean` is a Mathlib-only semantic challenge with one intentional
statement placeholder. `Solution.lean` repeats the proposition without
importing the challenge and proves that semantic contract. The comparator
configuration and import-closure audit are present, but passing them is not a
proof of the paper's universal source theorem.

The exact Zenodo/Palomar procedure is documented in
[`docs/release-runbook.md`](docs/release-runbook.md). The repository carries
Apache-2.0 `LICENSE`, `NOTICE`, citation metadata, and `.zenodo.json`, but the
release gate is disabled until Phase I, Phase II, and the Palomar-compatible
replay have committed evidence. No DOI is claimed before Zenodo issues one.
