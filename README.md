# Symplectic Stafford formalization

This repository contains a complete Lean 4 proof of the affine same-divisor
theorem for simple filtered algebras. That theorem is Target theorem A of the
manuscript *Symplectic Stafford. Same-divisor identities for simple filtered
algebras*.

**Theorem.** Let `k` be a field of characteristic zero. Let `U` be a simple,
infinite-dimensional `k`-algebra with an exhaustive, nonnegative,
multiplicative filtration `F₀U = k ⊆ F₁U ⊆ ⋯` by finite-dimensional
subspaces. Suppose its associated graded ring is a commutative affine domain
of finite Krull dimension. Then for all nonzero `d, a ∈ U` and every `B ∈ U`
there are `H, R, S ∈ U` with

```text
1 = d R + (B + H a) d S.
```

The noncommutative factor order is exactly as displayed, and all factors lie
in `U`. With `B = 0` and `a = 1` this is Stafford's identity
`1 = d R + F d S`.

## Where the proof lives

| Declaration | File |
| --- | --- |
| `SymplecticStafford.Paper.FilteredAlgebraData.targetA` | `SymplecticStafford/Paper/Induction.lean` |
| `SymplecticStafford.Paper.FilteredAlgebraData.targetA_left` (`1 = R d + S d F`) | `SymplecticStafford/Paper/Opposite.lean` |
| §7 consequences for `U`: cyclic torsion modules, stable range ≤ 2, stably free ⇒ free, cancellation | `SymplecticStafford/Paper/ConsequencesForU.lean` |
| `SymplecticStaffordChallenge.universalStatement` (Palomar form) | `Challenge.lean`, `Solution.lean` |

- The development in `SymplecticStafford/Paper/` imports Mathlib only.
- It contains no `sorry` and no project axioms.
- The main theorems depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
- `SymplecticStafford/Paper.lean` imports all of it.
- `docs/target-a-submission-scope.md` explains how the formal statement
  matches the manuscript's §1.1 hypotheses. It also maps each Lean file to its
  paper section and lists where the formal proof route differs from the
  written one. The [paper/Lean correspondence](docs/paper-lean-correspondence.md)
  and [machine-readable map](docs/paper-lean-map.json) pin the research source
  and declarations so subsequent changes can be checked for drift. Public
  verification checks the formal side; full source correspondence also
  requires the pinned private research snapshot via `PAPER_REPO`.

The paper proof is in the companion research repository
[symplectic-stafford](https://github.com/itpplasma/symplectic-stafford). Its Section 3 localization gap was closed by
`docs/zariskian-local-package-closure-2026-09-30.md`. Corrections and
simplifications found during formalization are recorded in
`docs/formal-proof-route-2026-09-30.md` there.

The older conditional scaffolds under `SymplecticStafford/{Semantics,
Filtered, FiniteLength, Ordered, Source, Induction, Package}` are retained as
history. The Target A proof does not use them. Their earlier status notes are
archived in `docs/history/`.

## Build and check

The release migration pins Lean `v4.35.0-rc3` and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. Exact dependencies and replay tools
are recorded in the repository configuration and verification evidence. The
Target A proof imports Mathlib only; historical scaffolds use additional
pinned dependencies.

```sh
bash scripts/verify.sh
bash scripts/bootstrap-palomar-tools.sh
bash scripts/verify-palomar.sh
```

The default verifier builds the Mathlib-only proof, checks its 18 endpoints,
and runs the Target A oracle and declaration map checks. `--legacy` selects
the historical scaffolds separately; their compatibility with the new
toolchain is not claimed.

The current Comparator uses the bundled `leanexport`, `leanchecker`,
`nanoda_bin` and `con-ron` tools. Its protected local replay requires Linux
and `bwrap`. The official Palomar CI preflight is pinned to a revision at or
after the required d4e41c1 workflow fix.

The 30 September Lean 4.33.0 and standalone-tool results in
`docs/verification.md` are historical checks of their recorded snapshot.
They do not certify the current toolchain migration. Fresh build, statement
comparison and independent kernel replay must complete before submission;
results are recorded for the exact checked source.

## Status

- The universal theorem is proved in Lean, as are all of the manuscript's
  §7 consequences.
- Historical local Comparator, NanoDa and Lean-kernel checks passed for the
  30 September source. Fresh replay of the release migration is in progress;
  `docs/verification.md` and the machine-readable report identify checked
  snapshots.
- Release preparation and Palomar submission were authorized on 21 October
  2026. Fresh replay, the exact submitted commit and the registration receipt
  are tracked separately in `docs/release-runbook.md` and `release-gates.yaml`.
- Independent human mathematical review remains pending. The final
  human-readable manuscript is a separate later deliverable; the research
  exposition and its corrections supply the current paper correspondence.
- No novelty or priority claim is made here.
