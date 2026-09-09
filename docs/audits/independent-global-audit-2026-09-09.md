# Independent global proof and release audit

Date: 9 September 2026.  This audit reviewed the frozen paper candidate
`itpplasma/symplectic-stafford@502b65a1dea53cac52220a08e321bfba525bc72e`, its
roadmap `e3c7077d3d51772d97d8e72bb219a8fc36765682`, and formal checkout
`7ab5c6a` (the review was performed with concurrent implementation work
excluded from the frozen source packet).

## Verdict

`FAIL WITH SCOPE`.  The paper candidate is a complete self-audited research
candidate, but the formal repository does not establish its universal
same-divisor theorem.  The exact target remains

```text
forall d != 0, exists F R S, 1 = d * R + (F * d) * S
```

in the original algebra, with the stronger affine source statement recorded
in `docs/phase-instructions.md`.

## First unsupported bridge

The first load-bearing gap is Part I.3--I.5's transfer from the localized
filtered/Rees object to finite composition length for the actual `T_p` module.
The paper identifies reduction of the algebraic Rees localization with
`G_(Sigma_p)`, where only homogeneous symbols outside `p` are inverted, but
then bounds chains using ordinary prime localization `G_p`.  It must prove
the comparison and that every proper filtered subquotient yields a nonzero
strict graded factor at the relevant homogeneous localization.  Finite
Rees generation alone does not supply quotient saturation, strictness, or
that comparison.

The formal boundaries
`FiniteLength/GradedLengthFilteredChainBoundary.lean` and
`FiniteLength/PrimeVsHomogeneousLocalizationBoundary.lean` independently
exhibit these missing implications.  Their examples are boundaries for the
inference, not counterexamples to the intended Weyl or symplectic class.
The conditional `FilteredLocalizedGradedBridge` and
`FilteredChainLengthBound` expose the exact hypotheses needed to reopen this
route; they do not prove them.

## Other producer boundaries

The historical `AdmissibleSymplecticClass` contains proposition-valued labels,
not actual filtration, associated-ring, localization, or source data.  The
kernel-checked nontrivial `Z` witness in
`Filtered/AdmissibleLabelsFalsePositive.lean` satisfies those labels while
failing `OriginalSameDivisor Z` by parity.  Therefore the labels cannot be
used as a universal M01 producer.  The M07 source-dependent retention
boundary in `Induction/TestRetentionObstruction.lean` likewise shows that
two lower-call pass certificates alone do not imply retention for the chosen
affine pencil.  These are semantic-contract boundaries, not counterexamples
to the paper's strengthened module hypotheses.

The pinned Stafford38 and AlgebraicAnalysis APIs provide reusable
Weyl-specific and conditional consumers.  The Weyl M01 calibration and
equivalence transfer do not transport to the proposition-valued arbitrary
quantization class.  The bounded quantized-slice interface requires finite
bounded lifts into the original algebra; formal or microlocal slice data do
not supply those lifts automatically.

## Exact evidence and non-claims

The current local replay has 160 trust-disabled oracle files and a 9,161-job
root build under Lean 4.33.0, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, AlgebraicAnalysis
`add0a80d865c88fe9cbc6901bda08a636ce188f9` (v0.3.1), and Stafford38-formal
`213ae2073030c8a897087152a616b8f8c1292df2` (v1.1.1).  The trust-disabled
consumer replays and Palomar comparator cover the semantic checkpoint, not
the universal M01--M11 theorem.  The paper regression has 314 assertions.

`Challenge.lean` deliberately contains the project's one challenge `sorry`;
`Solution.lean` proves the repeated semantic definition by `rfl`.  Neither
file states the filtered-class terminal theorem.  The terminal declarations
in `Package/TerminalBoundary.lean` are conditional on supplied termination
and zero-extraction data.

The release gates are correctly fail-closed: Phase I is `partial`, Phase II
is `checkpoint-only`, Palomar registration is pending, and publication is
disabled.  No Phase I/II completion, universal Lean proof, Zenodo DOI, or
public release follows from the passing checkpoint replays.

## Reopening condition

Reopen the universal route only after an actual algebraic filtered/Rees and
full-symbol Ore construction, a strict homogeneous-localization length
transfer, finite local source/test maps, source-dependent support removal with
carried-test retention, and the original-U simultaneous producer are all
proved and independently replayed.  Until then the checked suffixes remain
conditional consumers and model calibrations.
