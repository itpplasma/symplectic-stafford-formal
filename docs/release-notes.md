# Symplectic Stafford formalization v0.1.0

This release candidate proves Target theorem A of the
[Symplectic Stafford](https://github.com/itpplasma/symplectic-stafford)
exposition. For a simple, infinite-dimensional characteristic-zero algebra
with an exhaustive nonnegative multiplicative filtration by finite-dimensional
pieces, `F₀U = k`, and commutative affine domain associated graded ring of
finite Krull dimension, it proves

```text
∀ d ≠ 0, ∀ a ≠ 0, ∀ B, ∃ H R S, 1 = d R + (B + H a) d S.
```

All factors lie in the original algebra, in the displayed order. The
Mathlib-only proof is in `SymplecticStafford/Paper/`; it also proves the
left-handed identity and the module-theoretic consequences in section 7.
The main results use only `propext`, `Classical.choice` and `Quot.sound`.
The independently stated `Challenge.lean` and `Solution.lean` pair compares
Target A through `comparator.json`.

The [submission scope](target-a-submission-scope.md) records the hypotheses,
paper correspondence and proof-route changes. The research exposition and
formal development share an internal research history; no novelty, priority,
independent human review or journal acceptance is claimed. A final
human-readable manuscript is a separate later deliverable.

The [verification record](verification.md), machine-readable replay report and
[release gates](../release-gates.yaml) identify checked snapshots and pending
steps. A prepared release note is not a Palomar registration receipt. Retain
the actual registration URL and submitted commit after submission.

Formal code and documentation are Apache-2.0. Exact Lean/Mathlib pins and
verification-tool revisions are retained in the repository. The active package
has exactly one direct dependency, Mathlib; retired scaffolds replay only in
the [frozen pre-migration environment](history/legacy-build-environment.md).
The dependency-pruned source 8b94e4a2c9114a63a44a7e057e3b03fcafbb95f3 passes
native full private-source verification and
[clean Linux CI](https://github.com/itpplasma/symplectic-stafford-formal/actions/runs/39578127875). The checks include
18 endpoint axiom reports, 96 mapped declarations, the Target A oracle and six
verifier regression tests; the source inventory covers 414 files. The
[complete official Palomar preflight](https://github.com/itpplasma/symplectic-stafford-formal/actions/runs/39578128284)
passes for that exact source and the selected Target A theorem, with no errors
or warnings. The retained mechanical report records con-ron acceptance of
19,824 declarations, NanoDa and Lean acceptance, and Comparator success.
This Target A comparison does not register the section 7 consequences.
The final metadata commit requires its own official preflight before intake;
intake and registration remain pending. Earlier passes remain evidence for
their named snapshots.
