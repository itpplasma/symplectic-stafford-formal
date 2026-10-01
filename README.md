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
| Non-vacuity: the Weyl algebra `Aₙ(k)` satisfies the hypotheses; Stafford 3.8 (`Stafford38.UniversalStatement`) as a corollary | `SymplecticStafford/Examples/WeylInstance.lean` |

- The development in `SymplecticStafford/Paper/` imports Mathlib only. The Weyl
  example additionally uses the PBW normal form and Bernstein symbols of the
  pinned Stafford38 dependency.
- It contains no `sorry` and no project axioms.
- The main theorems depend only on `propext`, `Classical.choice` and
  `Quot.sound`.
- `SymplecticStafford/Paper.lean` imports all of it.
- `docs/target-a-submission-scope.md` explains how the formal statement
  matches the manuscript's §1.1 hypotheses. It also maps each Lean file to its
  paper section and lists where the formal proof route differs from the
  written one.

The paper proof is in the companion research repository
`itpplasma/symplectic-stafford`. Its Section 3 localization gap was closed by
`docs/zariskian-local-package-closure-2026-09-30.md`. Corrections and
simplifications found during formalization are recorded in
`docs/formal-proof-route-2026-09-30.md` there.

The older conditional scaffolds under `SymplecticStafford/{Semantics,
Filtered, FiniteLength, Ordered, Source, Induction, Package}` are retained as
history. The Target A proof does not use them. Their earlier status notes are
archived in `docs/history/`.

## Build and check

The workspace pins Lean `v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. The legacy scaffolds also use
AlgebraicAnalysis v0.3.1 and Stafford38 v1.1.1; the Target A proof does not
depend on them.

```sh
lake build SymplecticStafford.Paper Challenge
lake env lean Solution.lean
lake env lean tests/PaperTargetAOracle.lean
lake build SymplecticStafford.Examples.WeylInstance && lake env lean tests/WeylNonVacuityOracle.lean
./scripts/verify-palomar.sh      # after scripts/bootstrap-palomar-tools.sh
```

`verify-palomar.sh` checks `Solution.lean` against `Challenge.lean` with the
pinned tools:

- Comparator `5756749`, lean4export `15f6055`, NanoDa `68d5ca9`, Landrun `811cfff`.
- The project is compiled and exported with Lean 4.33.0.
- The comparator executable itself is built with the `v4.34.0-rc1` toolchain
  that its own repository pins.

## Status

- The universal theorem is proved in Lean, as are all of the manuscript's
  §7 consequences.
- The hypotheses are non-vacuous: the Bernstein-filtered Weyl algebra
  `Aₙ(k)`, `char k = 0`, is proved simple and an instance, and Stafford's
  Theorem 3.8 for every `n` follows from Target A.
- Palomar comparator, NanoDa and Lean-kernel checks run locally;
  `docs/verification.md` has the results.
- Still outstanding: independent human review of the paper and of the
  statement correspondence, public clean replay, registration and release.
  See `docs/release-runbook.md` and `release-gates.yaml`.
- No novelty or priority claim is made here.
