# Symplectic Stafford formalization

A Lean 4 and Mathlib proof of the affine same-divisor theorem for simple
filtered algebras (Target theorem A of the manuscript *Symplectic Stafford.
Same-divisor identities for simple filtered algebras*), together with the
manuscript's section 7 consequences.

Status: the proof is complete in Lean; independent human review of the
mathematics and the final manuscript are still pending.

## The theorem

Let `k` be a field of characteristic zero and `U` a simple,
infinite-dimensional `k`-algebra with an exhaustive, nonnegative,
multiplicative filtration `F₀U = k ⊆ F₁U ⊆ ⋯` by finite-dimensional
subspaces, whose associated graded ring is a commutative affine domain of
finite Krull dimension. Then for all nonzero `d, a ∈ U` and every `B ∈ U`
there are `H, R, S ∈ U` with

```text
1 = d R + (B + H a) d S.
```

The factor order is as displayed. With `B = 0` and `a = 1` this is
Stafford's identity `1 = d R + F d S`.

## What is formalized

- `SymplecticStafford.Paper.FilteredAlgebraData.targetA`
  (`SymplecticStafford/Paper/Induction.lean`): the theorem above.
- `...targetA_left` (`Paper/Opposite.lean`): the left-handed identity
  `1 = R d + S d F`.
- `Paper/ConsequencesForU.lean`: cyclic torsion modules, stable range at most
  2, stably free implies free, and cancellation.
- `Challenge.lean` / `Solution.lean`: the statement in a Mathlib-only form
  (`SymplecticStaffordChallenge.universalStatement`) and its proof, for
  independent statement comparison.

The `Paper/` development imports only Mathlib, contains no `sorry` and
declares no axioms; the 18 endpoints listed in `docs/endpoints.txt` depend
only on `propext`, `Classical.choice` and `Quot.sound`. The only `sorry` in
the repository is the intentional placeholder in `Challenge.lean`, which is
the statement to be proved. How the Lean hypotheses encode the manuscript's
section 1.1, and where the formal proof route differs from the written one,
is described in [docs/target-a-submission-scope.md](docs/target-a-submission-scope.md).

The directories `SymplecticStafford/{Semantics, Filtered, FiniteLength,
Ordered, Source, Induction, Package, Dependency}` hold older conditional
scaffolds. They are not used by the Target A proof, are not built by default,
and only build in the [frozen historical environment](docs/history/legacy-build-environment.md).

## Building and checking

Requires [elan](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.35.0-rc3`) and the single dependency (Mathlib, pinned in
`lakefile.toml`) are fetched automatically.

```sh
lake exe cache get
lake build
bash scripts/verify.sh
```

`lake build` builds the default targets (`SymplecticStafford.Paper`,
`Challenge`, `Solution`). `scripts/verify.sh` additionally checks the
import closure, prints and checks the axioms of every endpoint, runs the
paper/Lean declaration map check and replays `tests/PaperTargetAOracle.lean`
with `--trust=0`. See [docs/building.md](docs/building.md) for the
comparator replay and further options.

## Documentation

- [docs/target-a-submission-scope.md](docs/target-a-submission-scope.md):
  formal statement versus manuscript, and file-to-section map.
- [docs/paper-lean-correspondence.md](docs/paper-lean-correspondence.md) and
  [docs/paper-lean-map.json](docs/paper-lean-map.json): declaration-level
  correspondence with the paper source.
- [docs/building.md](docs/building.md): build, verification and comparator
  replay.
- [docs/verification.md](docs/verification.md): record of verification runs.
- [docs/release-runbook.md](docs/release-runbook.md): release steps.

The paper proof is developed in the companion repository
`itpplasma/symplectic-stafford`.

## Related projects

- [stafford38-formal](https://github.com/itpplasma/stafford38-formal) and
  [algebraic-analysis](https://github.com/itpplasma/algebraic-analysis):
  dependencies of the historical scaffolds only.

## Citing and license

Citation metadata is in [CITATION.cff](CITATION.cff). Licensed under the
Apache License 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
