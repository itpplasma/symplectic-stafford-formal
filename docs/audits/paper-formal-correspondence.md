# Paper and formal correspondence audit

Audit date: 8 September 2026.  Reader: a referee or release maintainer who
needs to distinguish the final paper candidate from the checked Lean
checkpoint.  The paper repository was inspected at `e3c7077d3d51772d97d8e72bb219a8fc36765682`; the formal checkout was inspected at its current
working tree.

## Executive finding

The formal checkpoint faithfully fixes the ordered right-certificate syntax,
the ring-right-ideal/quotient boundary, and several finite algebraic
consumers. It does not yet formalize the paper's all-dimensional producer,
full localization/support theory, or producer-derived terminal extraction.
Phase I, Phase II, and public-release status must remain pending.

## Exact correspondence

| Paper target or obligation | Formal declaration or file | Finding |
| --- | --- | --- |
| `1 = d * R + (F * d) * S` for every nonzero original `d` | `OriginalSameDivisor` in `SymplecticStafford/Semantics/Contract.lean`; `SameDivisorIdentity` in `Statement.lean` | The proposition's product order matches. No theorem derives it from the paper's filtered/symplectic hypotheses. |
| Strong affine target `1 = d*R + ((B + H*a)*d)*S` | `Ordered/Affine.lean` | Only ring identities are proved. There is no affine source-existence theorem, and centrality of the scalar parameter is not encoded. |
| M01 right ideals and right-module quotients | `RightIdeal`, `RingRightIdeal`, `RightQuotient`, `Semantics/RightIdealBridge.lean` | The bridge connects `twoGeneratedRightIdeal d f` to a `RingRightIdeal` using a proved negation-closure lemma, then proves quotient unit/zero/multiplication and action-respect laws. Arbitrary semiring right ideals still require an explicit negation-closure premise; the filtered-class semantics remain open. |
| M02--M05 filtered/Rees localization, detection, and minimal-prime length | `Filtered/ReesBasic.lean`, `Filtered/ReesQuotient.lean`, `Filtered/ReesAlgebra.lean`, `Filtered/FiniteSupportDetection.lean`, `Filtered/WeightedDetection.lean`, `Filtered/Localization.lean` | Raw bounded-term coherence, an actual bounded coefficient `Subsemiring`, finite associated-top extraction and a supplied weighted detector are checked. The paper's Noetherian Rees quotient, full-symbol Ore/localization, faithful detection and minimal-prime length remain open. |
| M06--M07 finite tests and activated pencils | `FiniteLength/Pencil.lean`, `FiniteLength/PencilBridge.lean`, `FiniteLength/ActivatedPencil.lean`, `FiniteLength/MatrixPencil.lean`, `FiniteLength/RadicalLift.lean`, `Source/OriginalTestContract.lean` | Finite division-coordinate and central matrix-block avoidance, plus conditional top-to-cyclic/lifting consumers, are checked. Division-coefficient LLD, composition-length lifting, `vL=0`, `e=vB+uL`, and one original-U source remain open. |
| M08 common colon and support-union assembly | `Ordered/CommonColon.lean`, `Ordered/RightClear.lean`, `Ordered/SupportUnion.lean`, `Ordered/FiniteGenerationBridge.lean` | Ordered K/J definitions, right-ideal closure, central pencil identity, finite generator membership and conditional affine inclusion are checked. Polynomial localization and the support-union theorem remain open. |
| M09--M10 strong `P_h` and successor induction | `Induction/StrongPh.lean`, `Induction/FiniteIndex.lean`, `Induction/TestRetention.lean`, `Induction/ConcreteSuccessor.lean` | The abstract predicate, finite-index composition, explicit old/new families, carried-list obligations and defect arithmetic are checked. The admissible tests, base, successor construction and support removal are not formalized. |
| M11 original cofactors, opposite hypotheses, and Stafford package | `Semantics/SupportDimension.lean`, `Package/TerminalBoundary.lean`, `Package/Opposite.lean`, `Source/DifferentialOreDescent.lean` | A supplied bottom-support datum or zero-quotient witness yields literal original-U cofactors in the paper's order; left/right S1 transport and a finite-cover differential-Ore clearance consumer are explicit. The chart-to-global bridge, actual characteristic support, filtered-class opposite preservation and banked package consumers remain open. |
| Palomar challenge | `Challenge.lean`, `Solution.lean` | Correctly isolated. The challenge is the definitional membership contract; its one `sorry` is deliberate, and the solution proves the same proposition without importing the challenge. It is not the paper theorem. |

## Status and pin discrepancies

The paper's authoritative current commit is `e3c7077d3d51772d97d8e72bb219a8fc36765682`.
The formal `PLAN.md`, `formalization.yaml`, verification record, and dossier
still identify `502b65a1dea53cac52220a08e321bfba525bc72e`.  Either retain
`502b65a1...` as an explicitly frozen source snapshot or update every source
record together after the final paper commit is selected; a mixed source
boundary is not reproducible correspondence evidence.

The checked Stafford38 formal repository at `e77e176c381ca2d6b20c030f9227f1b031415d2e`
pins AlgebraicAnalysis at its released v0.3.0 commit
`4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`, whereas this formal checkout
pins the newer public AlgebraicAnalysis main head
`46f2c819deca0e9735a436bed94ebed03ae35090` in both `lakefile.toml` and
`lake-manifest.json`.  The newer checkout uses the same Lean/Mathlib pins and
the downstream root and phase-I checkpoint builds pass; the Stafford38
historical pin difference is recorded rather than silently rewritten.

The formal proof graph labels the implemented `ordered-algebra` and
`finite-length-pencil` modules as `GAP`, even though their declarations and
independent consumers compile.  Use an explicit checkpoint status (or a
`LEAN`/`LEAN-CHECKPOINT` kind) for those nodes while retaining the absent
localization/source-selection/assembly nodes as gaps.  Conversely, retain a
gap annotation for the quotient node until actual right-action laws and the
generated ring-right-ideal bridge are proved.

## Safe release wording

The following wording is supported: “This checkpoint proves the original-ring
ordered semantic contract, quotient relation-respecting operation, opposite
certificate transport, ordered identities, finite common right-denominator
clearing, and a coordinatewise finite pencil lemma under the pinned
environment.  It does not formalize or certify the all-dimensional paper
producer or the Stafford package.”  Do not call the checkpoint a proof of
the universal same-divisor theorem, a completed Phase I/II formalization, or
a public Zenodo release.
