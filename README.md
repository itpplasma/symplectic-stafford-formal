# Symplectic Stafford formalization

This is the Lean workspace for the symplectic same-divisor programme. It
keeps the target in the exact noncommutative order

```text
1 = d * R + F * d * S
```

The private `itpplasma/symplectic-stafford` exposition, its working notes, and
this Lean development are records of the same internal research project. The
private exposition is not a separately published or presented prior source;
its dated chronology is retained for provenance and mathematical review. This
checkpoint does not make a priority claim and does not yet claim the universal
theorem.

The current checked checkpoint formalizes the original-ring semantic contract,
the right-ideal bridge and quotient-action laws, opposite transport, ordered
common-colon and finite-generation identities, raw and algebraic bounded
filtered/Rees operations, a quotient Rees-module action, an algebraic
power-Ore fraction boundary and finite power-Ore normal forms, finite
bounded-generator filtrations, associated-layer support, explicit right-module
composition filtrations and Jacobson-top generation reflection, finite-support
top and matrix-pencil detection,
explicit spectrum-support, full-symbol and filtered-Noetherianity boundaries,
list-indexed division-LLD source selection, and activated finite-length pencil
consumption,
conditional right-denominator/differential-Ore clearing, a constructive
finite-index P_h successor contract, original-affine source selection, and a
conditional support-union consumer, a faithful weighted-detection boundary,
and a kernel-checked strong-P_h successor obstruction. The latest parallel
wave also adds an actual-right-localization power-Ore bridge, a finite
weighted-matrix inverse/row-action lemma, scalar-extension orbit-pencil
activation, stronger M08 generator expansion, a two-call descent successor
consumer, and terminal/opposite package assembly. These remain conditional
utilities with explicit hypotheses. The
follow-up wave adds finite common-denominator clearing for right-localized
families, a central-field filtered-algebra interface, weighted-detection
composition after nilpotent correction, Jacobson scalar-extension top
comparison, finite scalar bad-set avoidance, and an indexed finite-colon
characteristic-support consumer. These too remain conditional utilities with
explicit hypotheses.
The next wave adds an actual filtered-layer class/support bridge, finite
full-symbol chart control, a module Noetherianity criterion with a
sequence-ring obstruction, bounded below-one inverse data and a diagonal
negative-degree matrix boundary, explicit finite block consumers, certified
nonzero original-U source selection, and indexed support-removal/test-retention
consumption. These remain conditional utilities and independent boundary
evidence; the universal M01–M11 producer is still open.
The latest bounded universal-attempt wave adds checked boundaries for the
proposition-only M01 labels, the A1 principal-open/power-Ore shortcut, and the
gap from genuine Ore localization to bounded inverse degrees; it also adds an
isotypic repeated-division-ring block contract, a source theorem from genuine
finite top bridges, and a source-dependent support-removal obstruction. These
commitments sharpen the missing hypotheses without claiming universal closure.
The continuation wave adds checked boundaries for degree-zero central-field
filtrations, noncommutative associated layers, finite-length Jacobson tops,
noncommutative division-ring pencil exceptions, filtered full-symbol weighting,
the strong-P_h base, and the exact A₁ OreSet obstruction. These are evidence
about the remaining hypotheses, not a terminal theorem.
The latest continuation adds a degree-zero associated-layer equivalence,
strict Rees good-subquotient consumers, a commutative polynomial full-symbol
calibration, finite weighted-faithful detection, a zero-pencil division-ring
obstruction, finite-direction original-U source selection, and explicit
base/two-call endpoint assembly. Each is independently checked and remains
conditional or diagnostic; the release gates stay fail-closed.
The second continuation adds a genuine polynomial filtration boundary,
polynomial Rees Noetherian certificate, finite clearing for actual Ore charts,
a good polynomial-module calibration, split central finite-pencil activation,
a Weyl A₁ original-ring identity, and a concrete Nat support-removal step.
These calibrations narrow the remaining hypotheses without closing the
all-dimensional theorem.
The third continuation adds an additive structural filtered-ring class, finite
homogeneous Rees decomposition, localized-to-original cofactor recombination,
generic weighted good-module detection, finite-central division-block pencils,
a split finite-dimensional original-U source selector, and central-field
support-removal/test-retention bridges. These are checked conditional
interfaces and finite-model consumers; the universal producer and release
gates remain pending.
The fourth continuation composes these interfaces into an associated-graded
support bridge, a Rees Noetherian transfer criterion, localized-to-original
divisor assembly, weighted detection-to-support linkage, finite-central
activated pencils, finite-dimensional same-divisor assembly, and a central-field
two-call successor. These remain conditional consumers with explicit local,
chart, and coefficient hypotheses; the universal producer and release gates
remain pending.
The fifth continuation adds an M01 associated-spectrum adapter, bounded-layer
support/dimension/defect invariance, finite localized assembly with one common
denominator, correction-aware weighted support detection, minimal-prime
finite-central activation, retained finite-test assembly, and a central-field
finite-index endpoint adapter. These are independently trust-disabled checked
and remain conditional on their displayed maps, local certificates, chart
data, and producer hypotheses.
The subsequent independent review corrected the bounded-layer calibration,
strengthened retained-test and activated-block oracles, and conditioned the
central-field support-removal arithmetic on non-exceptional scalars. These
are evidence-strengthening fixes, not universal theorem or release claims.
The general finite-length activated-pencil and universal original-U source
producer remain open. It deliberately does not claim the universal
higher-dimensional theorem in the internal all-dimensional proof candidate.
The source-selection, filtered-localization, assembly, and terminal Phase I/II
gates remain open in `PLAN.md`; the corresponding files are conditional
scaffolds rather than producer proofs.

The map labels the conditional filtered chart/power-clearing, divisor-indexed
assembly, and strong finite-test induction interfaces LEAN-SCAFFOLD. The raw
Rees, Rees-module, power-Ore, finite-filtration/support, common-colon,
finite-pencil, support-boundary,
source-selection, constructive-successor, and opposite-transport modules are
checked utilities, but their missing producer hypotheses keep M01–M11 open.
Precise scopes appear in the linked claim register.

## Reproducible setup

The workspace uses Lean and Mathlib v4.33.0, matching the checked Stafford38
formal project. Exact build revisions are in the lock files:

| Dependency | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| AlgebraicAnalysis | `46f2c819deca0e9735a436bed94ebed03ae35090` |
| Stafford38 formal | `e77e176c381ca2d6b20c030f9227f1b031415d2e` |

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
the internal-proof-to-`Challenge.lean` comparison, the principal
proof-architecture interfaces, and verbatim Challenge/Solution listings.
Build it with:

```sh
docs/dossier/build.sh
```

The build also writes an ignored `symplectic-stafford-description.build-manifest.json`
with input hashes, engine versions, source commit, and the PDF hash; the release
runbook archives it beside the PDF and checksum file.

The internal proof source is Markdown in the private research repository, not
TeX; the dossier records that provenance boundary explicitly rather than
fabricating a source correspondence. `docs/proof-graph.yaml` is the
machine-readable status graph; the build regenerates the map and linked claim
register from it. The internal source snapshot is frozen at
`502b65a1dea53cac52220a08e321bfba525bc72e`, with its updated terminal
instructions at `e3c7077d3d51772d97d8e72bb219a8fc36765682`.

[`docs/phase-instructions.md`](docs/phase-instructions.md) assigns the internal
all-dimensional candidate's M01–M11 obligations to parallel lanes. Both
recursive calls use P_h to prove P_(h+1); every finite local test is retained.
Phase I discharges all project-owned obligations, and Phase II also discharges
registered literature leaves. The final target is all-dimensional SS-all;
`Contract.lean` contains only a dimension-parametric semantic scaffold with
historical B2 fields, not the candidate's full filtered-algebra encoding.

## Palomar and release status

`Challenge.lean` is a Mathlib-only semantic challenge with one intentional
statement placeholder. `Solution.lean` repeats the proposition without
importing the challenge and proves that semantic contract. The comparator
configuration and import-closure audit are present; the local comparator,
NanoDa and Lean-kernel replay pass for this semantic pair. Passing them is not
a proof of the internal candidate's universal source theorem, and the release
gate remains disabled.

The exact Zenodo/Palomar procedure is documented in
[`docs/release-runbook.md`](docs/release-runbook.md). The repository carries
Apache-2.0 `LICENSE`, `NOTICE`, citation metadata, and `.zenodo.json`, but the
release gate is disabled until Phase I, Phase II, and the Palomar-compatible
replay have committed evidence. No DOI is claimed before Zenodo issues one.
