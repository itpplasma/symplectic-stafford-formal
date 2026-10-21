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
Earlier local and CI passes remain evidence for their named snapshots; the
dependency-pruned checkout requires a fresh build and complete preflight.
