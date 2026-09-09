# Finite central division-pencil submission scope

The Palomar challenge is the following bounded statement. Let `K` be an
infinite field, let `E` be a division ring that is finite-dimensional as a
`K`-vector space, and let `V` carry compatible `K`- and `E`-module structures.
The compatibility data consists of a ring homomorphism `ιmap : K →+* E`, its
action on coefficients, centrality of its image in `E`, and agreement of the
induced scalar action on `V`. For a finite family `x : ι → V` that is
`E`-linearly independent and any `y : ι → V`, the set

```text
{z : K | the family (x i + (ιmap z) • y i)ᵢ is not E-linearly independent}
```

is finite.

`Challenge.lean` states this as
`SymplecticStaffordChallenge.FiniteCentralPencilStatement` using Mathlib-only
imports and leaves exactly one deliberate proof hole. `Solution.lean` repeats
the definition independently and proves the compared theorem
`SymplecticStaffordChallenge.universalStatement` by applying
`SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_pencil_spectrum`.
It does not import `Challenge`.

This replaces the earlier comparator for a definitional right-set membership
equivalence. The new statement is a finite-central division-pencil theorem;
it is not the universal Stafford theorem. It does not change the status of
terminal milestones M01–M11 or either project phase.

The result was proved within the current private research development. Its
originality and independent research interest have not been established and
remain open questions; no novelty or priority claim is made here. Submission
readiness still requires clean replay of the repository's challenge/solution
statement comparator, import-closure checks, trust-disabled kernel check, and
the applicable release review.

## Local verification on 2026-09-09

The new compared statement passed independent Sol-low review and the local
Comparator, NanoDa, and Lean default kernel checks. Challenge and Solution
import-closure audits passed. The current uncommitted source is frozen by
base commit plus tracked patch and candidate-file hashes in
`luna-wave-20260909.json`; its full repository checkpoint results are listed
separately there. Two earlier timed build attempts did not reach the
comparator and are not counted as successful gates.

These local results do not establish a public clean replay, editorial
research interest, or completion of the universal Stafford theorem.
