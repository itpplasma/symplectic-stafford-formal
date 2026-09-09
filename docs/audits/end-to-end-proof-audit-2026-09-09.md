# End-to-end paper/formal proof audit

Date: 9 September 2026.  Reviewed against the current formal checkout at
the start of this audit (`4328b936cd2575446a81d01451e8dc535107c879`), the
frozen paper candidate indexed by
`/home/ert/proj/symplectic-stafford/docs/terminal-proof-index-2026-09-08.md`,
the all-dimensional Parts I--III, `docs/proof-graph.yaml`,
`docs/phase-instructions.md`, `Challenge.lean`, and `Solution.lean`.

## Verdict

**FAIL WITH SCOPE.**  The written candidate is not a formally established
proof of the universal same-divisor theorem.  The first load-bearing gap is
the filtered-to-local-length bridge in Part I.3--I.5.  This is not a
refutation of S1 for any particular algebra; it is a failure of the stated
proof implication under the currently available hypotheses.

## First bad bridge

Part I.3 (lines 120--122 of
`all-dimensional-symplectic-stafford-part-I-2026-09-08.md`) says that finite
localized Rees modules make every submodule and quotient of a good
`T_p`-module good with an induced filtration.  Part I.5 (lines 164--173)
then uses this to claim

```text
length_(T_p)(N_p) <= length_(G_p)((gr N)_p) < infinity.
```

There are two unproved requirements in this step:

1. The Rees parameter `z` may be injective on the original localized Rees
   module but need not remain injective on a quotient.  Finite generation of
   a Rees quotient does not imply `z`-torsion-freeness, separatedness, or a
   nonzero associated graded for a nonzero quotient.
2. The displayed associated graded after full-symbol localization is
   `G_(Sigma_p)`, where only homogeneous symbols outside `p` are inverted,
   not the ordinary prime localization `G_p`.  A finite length bound over
   `G_p` therefore does not automatically bound strict chains of filtered
   `T_p`-submodules.  One must prove that every strict filtered inclusion
   survives as a strict graded inclusion in the homogeneous localization.

The concrete unbounded-below model is

```text
R = k[t,t^-1],   F_n R = span_k {t^i | i <= n},   W = (t - 1)R.
```

Here `W` is proper and `R/W` is nonzero, but every class in `R/W` has a
representative in every `F_n` (use `t^n` for the class of `1`).  Thus the
induced quotient filtration is constant and `gr(R/W)=0`.  This shows why a
nonzero filtered quotient cannot be assumed to supply a nonzero graded
factor in an unbounded-below Laurent-type filtration.

The kernel-checked formal analogue is
`SymplecticStafford/FiniteLength/GradedLengthFilteredChainBoundary.lean`:
`sumZero < top` while every induced layer is surjective.  Its independent
oracle was replayed with:

```text
lake env lean --trust=0 tests/GradedLengthFilteredChainBoundaryOracle.lean
```

and passed.  This boundary is a module-level warning, not an assertion that
the actual Weyl localization has infinite length.

## Exact repair condition

No complete repair is available under the paper's current hypotheses.  The
route can be reopened only after proving either a direct finite-length
theorem for the actual `T_p`-module, or a Rees-saturation/Zariskian strictness
theorem which ensures that every proper localized submodule chain produces a
nonzero strict graded factor over `G_(Sigma_p)`, with the homogeneous-versus-
ordinary localization comparison proved at the same time.

The formal `FilteredChainTransfer.strict_survival` field and
`FilteredChainLengthBound.quantitative_length_bound` are correctly scoped
conditional interfaces for precisely this missing input.  They do not prove
that input.

## Conditional suffix that survives

The ordered common-colon identity, finite right-denominator clearing,
activated-pencil arithmetic, old/new support bookkeeping, and terminal
cofactor extraction remain valid conditional on the missing local-length,
support-equivalence, and universal original-U source-production bridges.
The basis `h=1` argument is substantially independent of this particular
local-length gap.  The full induction, Theorem A/B, automatic opposite
application, and Stafford package are not established without it.

## Challenge/Solution and phase scope

`Challenge.lean` deliberately contains one `sorry` and defines a semantic
membership proposition which is definitionally the same existential
certificate used in its statement.  `Solution.lean` repeats that definition
and proves the proposition by `rfl`.  The pair does not state or prove the
terminal theorem `1 = dR + FdS` for the paper's filtered class.  The endpoint
lists and Palomar comparator therefore certify only this semantic checkpoint.

The current graph and phase instructions correctly classify the substantial
Lean declarations as conditional consumers or boundaries.  The executable
phase checks replay the implemented checkpoint; they do not discharge M01--
M11.  Phase I and Phase II must remain pending/partial, and no release or DOI
claim follows from the passing finite regressions, comparator, or audit.

No status metadata was changed by this audit.
