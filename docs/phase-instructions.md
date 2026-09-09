# Phase I and Phase II instructions for the final paper

These instructions are for formalization workers and the integrating
controller. They follow paper commit
`502b65a1dea53cac52220a08e321bfba525bc72e` and the authoritative roadmap and
ledger at `e3c7077d3d51772d97d8e72bb219a8fc36765682` in
`itpplasma/symplectic-stafford`. Read that revision's terminal proof index,
main all-dimensional paper, parts I–III, and all-dimensional proof graph.

## The target and semantic audit

Keep `1 = d * R + ((B + H * a) * d) * S` in the original algebra, for every
nonzero original divisor d, arbitrary B and nonzero a. The same-divisor target
is B=0, a=1. Preserve the full simple connected locally finite filtered-domain
hypotheses in PLAN.md; do not add DL/Bn, tensor simplicity, finite-dimensional
modules or an assumed source producer to the statement. Prove degree-zero
equals the central field image. Any left-module encoding must prove its
right U/opposite transport.

Use integer or bottom-extended support dimension with delta(0)=-1. Natural
truncated subtraction at D-(D+1) cannot express the terminal argument.
The current `SupportDimension = WithBot Nat` and integer-valued `StrongPh`
defect are separate interfaces: prove their correspondence for the actual
characteristic support before using them together at termination.
The number of nonzero layers in a finite filtration is not the Krull
dimension of support in `Spec(gr U)`. A support proxy's zero-detection theorem
does not supply this correspondence.

## Project-owned obligations

| ID | Required proof and source | Completion boundary |
| --- | --- | --- |
| M01 | Original U, right ideals/quotients and structural filtered layers; main 0,5 | Literal membership, quotient action, degree-zero field and no hidden existence field |
| M02 | Filtered/Rees Noetherianity and good subquotients; I.1 | Bounded homogeneous Rees bridge and bounded-shift independence of radical characteristic support |
| M03 | Full-symbol Ore/Rees/module localization; I.2–I.3 | Actual algebraic fractions and exact passage; no completion substitute |
| M04 | Weighted-top matrix inversion and detection; I.4 | Nonzero good modules detected even with negative degrees |
| M05 | Minimal-prime local composition length; I.5 | Arbitrary finite good module, only at minimal support primes |
| M06 | Division-coefficient LLD and finite affine tests; II.1–II.4 | One original-U multiplier with all offsets and nonzero tails, including split finite-dimensional selectors |
| M07 | Activated and generating-vector pencils; II.5 | Fixed finite-length module, vL=0 and e=vB+uL, including finite-central division blocks |
| M08 | Common colon ideal and support union; main 1 | Actual finite generators, polynomial containment and constant right clearing |
| M09 | Strong P_h and admissible test lists; main 0,2,3 | All divisors, all B+Ua, every finite local test list and support-retention bridge |
| M10 | Successor and termination; main 3–5 | Two P_h calls for P_(h+1), old/new split, all tests retained |
| M11 | Original R,S, opposite hypotheses and package; main 5–6, III.1 | Exact terminal identity, localized-to-original cofactors, and separately checked banked consumers |

M08 fixes `K={s | G*d*s ∈ dU}` and `J=dU+F*d*K`. For every generator k
with `G*d*k=d*c`, preserve the certificate
`F*d*k=d*(-t*c)+(F+t*G)*d*k` for central t. A free-ring identity alone
does not prove the localization/support-union theorem.

M09 retains each test's actual localization, finite-length cyclic module,
canonical generator, nonzero right tail and offset. M10 first applies P_h to
d, obtains an actual relation `F*d*L0=d*C0`, and applies P_h to `d*L0` with
the old minimal-module tests. Both calls have lower index than P_(h+1).
Control the support of the common quotient by both recursive bounds; remove
all its minimal components with one central scalar while retaining the carried
tests. Terminate at P_(D+1), then extract finite right cofactors in U.

## Parallel lanes and returned evidence

The short-algebra lane owns M01 and ordered M08/M11. The finite-module lane
owns M06–M07. The filtered lane owns M02–M05. The assembly lane specifies
M09 and proves M10 after the APIs are fixed. Package and model workers
consume M11 only at proved scopes. Workers return exact declarations, their
hypotheses, builds, independent consumer evidence and remaining gaps.
The controller alone integrates and promotes authoritative status.

The checked modules provide the following starting points. Every M01–M11
obligation remains open at its full paper scope; each row records only the
proved portion and the construction its consumer still needs.

The 2026-09-09 follow-up wave adds bounded conditional utilities: finite
common denominators for arbitrary right-localized families
(`FullSymbolRightLocalization.common_right_clear`), a concrete central-field
filtered-algebra interface (`CentralField`), weighted detection composed with
a nilpotent correction (`WeightedDetectionComposition`), Jacobson-top scalar
extension (`JacobsonScalarExtension`), finite bad-set union/avoidance
(`FiniteScalarAvoidance`), and an indexed finite-colon characteristic-support
consumer (`CharacteristicSupportFiniteProducer`). These strengthen the
interfaces below without discharging any universal M01–M11 producer.

The next 2026-09-09 wave adds an actual filtered-layer class/support bridge
(`ActualClassSupport`), finite full-symbol chart control
(`FullSymbolFilteredChart`), a module Noetherianity criterion and its
sequence-ring obstruction (`ReesModuleNoetherianCriterion` and
`ReesModuleNoetherianBoundary`), bounded below-one inverse data and a diagonal
negative-degree matrix boundary (`BoundedBelowOneData` and
`WeightedInverseBoundary`), explicit finite composition/division/matrix block
consumers (`ExplicitBlocks`), certified nonzero original-U source selection
(`exists_original_affine_source_of_certified_list`), and indexed
support-removal/test-retention consumption (`FiniteRemovalRetentionBridge`).
These are checked utilities and boundary evidence; the universal M01–M11
constructions remain required.

The subsequent bounded universal-attempt wave adds independent boundary
evidence: `M01StructuralBoundary` and the historical-label sequence-ring
example show that the current proposition-only class is not structural;
`PowerOreA1Obstruction` rejects the principal-open-to-power-Ore shortcut;
`FullSymbolWeightedBoundary` separates actual Ore localization from bounded
inverse-degree data; `IsotypicBlocks` exposes the noncommutative repeated-block
bad-set obligation; `OriginalDivisionProducer` derives one source only from
genuine finite top bridges; and `LayerSupportObstruction` rejects
source-independent strict support removal. None of these closes a universal
M01–M11 obligation.

The continuation wave adds `CentralFieldFiltrationBoundary` (degree-zero
field-image surjectivity obstruction), `M01AssociatedGradedBoundary` (a
constant `Mat₂(ℚ)` filtration with noncommutative associated layer),
`ActualRadicalTop` (finite-length/Jacobson-top extraction from genuine right
composition data), `DivisionEigenBoundary` (the remaining noncommutative
finite-bad-set witness contract), and
`FullSymbolFilteredWeightedBoundary` (chart-control plus bounded-inverse
obstruction). It also records the strong-P_h base obstruction and the typed
power-Ore boundary. These remain checked boundary evidence; no phase gate is
promoted.

The latest continuation lanes add seven further checked scopes: an actual
degree-zero additive equivalence (`M01DegreeZeroBridge`), strict Noetherian
module/subquotient consumers (`ReesGoodSubquotient`), a commutative
polynomial full-symbol/Ore calibration (`FullSymbolPolynomialCalibration`),
finite weighted faithful detection with nilpotent correction
(`WeightedFaithfulCalibration`), a zero-pencil division-ring obstruction
(`DivisionEigenObstruction`), finite-direction original-U source selection
(`exists_original_affine_source_of_actual_directions`), and explicit base plus
two-call endpoint assembly (`BaseTwoCallAssembly`). Their hypotheses remain
visible and none supplies the universal filtered, block, support-removal,
base/successor or terminal producer required for Phase I/II.

The second continuation lanes add concrete positive calibrations: a genuine
ℚ[X] filtration boundary (`M01PolynomialFiltrationBoundary`), a polynomial
Rees Noetherian certificate (`ReesPolynomialNoetherian`), finite clearing for
actual right Ore charts (`FullSymbolActualOreFinite`), a good polynomial
module with negative-weight detection (`PolynomialGoodModuleCalibration`),
split central finite-dimensional pencil activation (`CentralFinitePencil`), a
literal Weyl A₁ original-ring identity (`WeylA1Calibration`), and a concrete
Nat support-removal successor (`NatSupportRemoval`). Each has an independent
trust-disabled oracle; none generalizes the result to the paper's arbitrary
filtered noncommutative class, so no phase gate is promoted.

The third continuation lanes add bounded bridges toward the universal
obligations: `M01StructuralClass` supplies additive filtered-ring layers,
degree-zero field action and least-layer detection; `BoundedReesBridge` gives
finite homogeneous Rees decomposition and a conditional Noetherian criterion;
`FullSymbolOriginalCofactor` performs original-U cofactor recombination after
one actual right-localization denominator; `GoodWeightedModule` supplies a
generic finite weighted good-module detector over `RingFiltrationData`;
`FiniteCentralDivisionPencil` handles finite-dimensional-over-center division
blocks; `FiniteDimensionalProducer` selects a common original-U source from
split finite-dimensional pencils; and `CentralFieldSupportRemoval` supplies
central-field polynomial exceptional-set avoidance with support-removal and
test-retention inputs. Their independent trust-disabled oracles pass, but the
filtered algebraization, local module bridges, and universal source/induction
producers remain unproved. No Phase I/II or publication status changes.

The fourth continuation composes these APIs: `AssociatedGradedSpecBridge`
connects filtered quotient layers to an actual commutative associated module
and its support; `ReesNoetherianTransfer` transfers Noetherianity under finite
homogeneous lifting; `LocalizedDivisorAssembly` combines actual right-chart
clearing with original-U divisor assembly; `GoodWeightedSupportBridge` links
weighted detection to nonzero filtered classes and support; and
`FiniteCentralDivisionActivated`, `FiniteDimensionalAssembly`, and
`CentralFieldTwoCallSuccessor` compose the finite-central pencil, source, and
two-call successor consumers. Every premise remains explicit and every
independent oracle is trust-disabled checked. These compositions do not prove
the universal quantum algebraization or producer, so both phases and release
remain pending.

The filtered lane's `WeightedFaithfulBoundary.lean` makes finite nonempty
coordinates, injective encoding and negative integer weights explicit, while
`WeightedInverseBoundary.lean` records the independent negative-degree unit
obstruction and `InfiniteMultiplicityBoundary.lean` records the failure of
finite length for an infinite-multiplicity module. The ordered
`SupportUnionBoundary.lean` gives a kernel-checked finite-ring counterexample
to promoting finite generation and an auxiliary-divisor relation into a
support union. `Induction/SuccessorObstruction.lean` gives a flat-defect
counterexample to deriving the one-step successor decrease from the lower
`P_h` contract alone. These are boundary evidence, not producer proofs.

| Obligation | Checked module and scope | Required continuation |
| --- | --- | --- |
| M01 | `Semantics/SupportDimension.lean` uses `WithBot Nat`, extracts zero from supplied support/dimension equivalences, and proves that a zero original right quotient is equivalent to membership of `1`. `Semantics/RightIdealBridge.lean` bridges the displayed two-generator semiring carrier to a `RingRightIdeal` under explicit negation closure and proves quotient action laws. `Filtered/OriginalCentralSupport.lean` gives the actual original-ring quotient and central-support zero bridge. `Filtered/CharacteristicSupport.lean` constructs a finite associated-layer support proxy from actual quotient classes, while `Filtered/SpecCharacteristicSupport.lean` states the genuine `Module.support`/annihilator zero-locus boundary for a supplied commutative associated module and an explicit filtered class map. `Filtered/ActualClassSupport.lean` connects a genuine filtered-layer quotient to that support boundary and records the `WithBot Nat`/integer-defect correspondence under explicit class-map data. `Filtered/M01StructuralBoundary.lean` independently shows that the historical proposition-only class labels do not imply even `Nontrivial`. `Filtered/M01StructuralClass.lean` supplies additive filtered-ring layers, degree-zero field action, representative-independent multiplication and least-layer detection, while retaining the missing commutative-affine/domain and support bridge as hypotheses. `Ordered/CharacteristicSupportProducer.lean` consumes an actual per-prime producer and localized common-quotient zero bridge to prove the corresponding support inclusion. | Construct the full characteristic support in `Spec(gr U)` and its zero-detection theorem, encode the actual filtered class and associated module, and connect bottom dimension to the integer defect without assuming negation closure as a hidden instance. |
| M02–M05 | `Filtered/ReesRing.lean` constructs the bounded-polynomial Rees subring from a filtration with negation closure, extending `ReesAlgebra.lean`; `M01StructuralClass.lean` supplies additive layers. `BoundedReesBridge.lean` gives finite homogeneous lifts/decomposition and a conditional Noetherian criterion for the actual `ReesRing`; `ReesModule.lean` checks quotient scalar actions. `GoodFiltration.lean` constructs bounded-generator layers and `GoodWeightedModule.lean` composes them with generic injective weighted detection. `FullSymbolLocalization.lean` and its right-ring/module variants use an actual arbitrary submonoid with supplied Ore data; `FullSymbolRightLocalization.common_right_clear` clears finite right-localized families under that supplied localization, `FullSymbolFilteredChart.lean` packages finite chart bounds, and `FullSymbolOriginalCofactor.lean` recombines a localized identity into literal original-ring cofactors once the chart is supplied. `CommutativeFullSymbol.lean` constructs the regular-element Ore instance for commutative rings, and `CentralField.lean` records a concrete degree-zero central-field/filtered-algebra interface. `PowerOre.lean` and `FinitePowerOre.lean` retain their separate supplied power-Ore hypotheses. `ReesNoetherianCriterion.lean` consumes a terminating leading-term reduction certificate, while `ReesModuleNoetherianBoundary.lean` records why finite layers alone do not provide one. Finite associated-layer detection, weighted triangular detection and `WeightedDetectionComposition.lean` are proved at their displayed scopes; `WeightedMatrixInverse.BoundedBelowOneData` names the inverse degree input and `WeightedInverseBoundary.lean` gives a diagonal negative-degree obstruction. `FiniteLength/MinimalPrimeLocalTheorem.lean` derives finite length for a finite module over a commutative Noetherian local ring when its maximal ideal is minimal over the actual annihilator; `FilteredMinimalPrimeBridge.lean` derives this conclusion over `Localization.AtPrime p` from support dimension zero. `JacobsonScalarExtension.lean` packages Jacobson-top comparison through a supplied scalar-extension orbit basis. The composition-filtration and negative-degree/infinite-multiplicity boundary modules retain their explicit scopes. | Identify the constructed Rees ring and associated layers with the paper's full objects; prove Noetherianity, good subquotients and bounded-shift support independence. Prove that the original noncommutative full inverse-symbol set is Ore, construct faithful localized good modules, and transfer the commutative local-length bound to the actual right module over `T_p`. |
| M06 | `Source/OriginalTestContract.lean` records original-U test lists and affine-source witnesses; `Source/DivisionLLD.lean` and the list-indexed `Source/DivisionLLDList.lean` prove finite exceptional-root avoidance with arbitrary offsets/nonzero tails and an explicit division-ring original-cofactor boundary, preserving one multiplier across a finite test family. The list lane now also removes the source-zero scalar roots, and `OriginalDivisionProducer.lean` packages certified admissibility into a nonzero original-U source with all offsets and right tails retained. `Source/FiniteDimensionalProducer.lean` adds a split finite-dimensional pencil selector with one common original-U multiplier and retained ordered passes. `Source/OriginalTestProducerBoundary.lean` supplies an independent admissibility counterexample showing that the current abstract contract does not itself produce an affine source. `Source/Assembly.lean` still extracts same-divisor S1 only from a supplied divisor-indexed producer with original cofactors. | Prove the actual division-coefficient LLD and construct one multiplier satisfying all paper tests for the admissible class. |
| M07 | `FiniteLength/Pencil.lean`, `ActivatedPencil.lean`, and `RadicalLift.lean` prove finite simultaneous scalar avoidance and finite top-lifting/ordered pencil consequences under supplied coordinates, actions and filtration steps. `MatrixPencil.lean` adds central-field determinant avoidance for finitely many repeated matrix blocks; `FiniteLength/FiniteOrbitPencil.lean` derives finite exceptions from an actual finite orbit basis over the central field; `FiniteCentralDivisionPencil.lean` adds the finite-dimensional-over-center division-block bridge; the activated bridge packages the ordered `vL=0`, `e=vB+uL` interface; `JacobsonTop.lean` proves actual radical-quotient generation reflection for finitely generated right modules; `JacobsonScalarExtension.lean` packages that top comparison through a supplied scalar-extension orbit basis; `ExplicitBlocks.lean` consumes explicit finite composition, division-ring or repeated matrix blocks; `ActivatedFiniteLength.lean` consumes the criterion for arbitrary finite supplied top blocks and retains the ordered pencil identity. `PencilBridge.lean` and the right-cyclic consumer use supplied top maps and generation reflection. | Prove the arbitrary finite-length activated-pencil theorem with `vL=0` and `e=vB+uL`, including repeated simple factors and noncommutative division-ring blocks, and connect the coordinate tests to the actual radical quotient. Radical-quotient generation reflection itself is checked. |
| M08 | `Ordered/CommonColon.lean` constructs K and J and proves the central pencil identity. `ActualM08Producer.lean` derives actual finite right generators from `IsNoetherian Rᵐᵒᵖ R`, using opposite-ring submodules. `CommonColonProducer.lean` constructs original-U common-colon data under an injective ambient map and simultaneous right-clearance of the exact coefficients. `CharacteristicSupportFiniteProducer.lean` consumes indexed colon-generator expansions to produce a finite Module.support union while retaining every original `F*d*k` pencil certificate. `SupportUnion.lean`, `M08SupportUnion.lean` and `FiniteGenerationBridge.lean` prove the displayed finite-span, ideal-membership and conditional support-cover results; `RightClear.lean` combines supplied right-power clearing. | Derive right Noetherianity from the paper's filtered hypotheses, prove polynomial/localization passage, and supply the actual characteristic-support/localized-zero bridge needed for the support-union theorem. Finite generation from right Noetherianity is checked. |
| M09–M10 | `Induction/StrongPh.lean` records abstract tests, integer bounds, two lower-index calls and supplied successor output. `TestRetention.lean`, `ConcreteSuccessor.lean` and `ConstructiveSuccessor.lean` make the finite families and construction data explicit. `TwoCallAffineProducer.lean` constructs the affine pencil source from two lower witnesses and assembles the next witness from supplied defect-removal and carried-test implications. `TwoCallDescentProducer.lean` packages the finite exceptional-set and support/defect equalities, while `FiniteScalarAvoidance.lean` proves the finite bad-set union/avoidance arithmetic. `CentralFieldSupportRemoval.lean` derives central-field polynomial exceptional sets and consumes source-dependent strict-removal/test-retention certificates. `FiniteRemovalRetentionBridge.lean` consumes indexed strict-support removal and test-retention laws to construct the successor witness after one common scalar choice. `SupportRemovalArithmetic.lean` derives the successor defect bound from strict support removal; `FiniteIndex.lean` composes supplied base and successor rules. `SuccessorObstruction.lean` and `Package/TerminalObstruction.lean` record the failure of weaker contracts. | Construct the admissible local tests, the universal base and the two-call successor; establish support removal and retention of every carried test from the actual local module arguments. Source-affine arithmetic does not produce those inputs. |
| M11 | `FiniteIndex.lean` extracts cofactors using supplied zero extraction; `Package/TerminalBoundary.lean` makes the zero-quotient/membership boundary and literal original-U cofactor order explicit; `Package/TerminalObstruction.lean` gives the independent terminal obstruction; `Package/Opposite.lean` proves equivalence of left S1 in U with right S1 in its opposite. `Source/OriginalDivisionProducer.lean` constructs one original affine source from an explicit finite list of division-coefficient pencil bridges. `Filtered/FullSymbolOriginalCofactor.lean` recombines a localized two-generator identity into literal original-ring cofactors after one common right denominator. `Source/DifferentialOreDescent.lean` records finite-cover clearing in original U under explicit chart hypotheses. | Derive original cofactors from actual characteristic support, prove opposite preservation of the filtered class, close the chart-to-global bridge, and check each claimed package consumer. |

Preserve the LEAN-SCAFFOLD classification of conditional localization,
assembly and induction nodes. A successor rule with output fields or an
assembly with cofactor fields proves a consumer only. In particular,
`strongPh_fin_index` assumes P_1 even when D=0, and does not construct the
paper's base case. The current top-pencil theorem assumes every exposed
coordinate of the starting vector is nonzero; its name does not establish
the activation hypotheses of M07.

## Phase I

For each selected terminal target, discharge all M01–M11 obligations in its
transitive proof closure. Only individually audited literature leaves may
remain: register an exact statement, source/version/locator, semantic wrapper,
owner and axiom entry. A proved imported declaration and an admitted external
assumption are different evidence. Project-specific P_h, local length, source
selection, support union and induction may not be relabeled literature.

Audit dependent definitions, instances, wrapper fields and imports as well as
the final proof term. A conditional theorem assuming its missing construction
is development progress, not Phase I. Freeze the source commit and, for
uncommitted review inputs, the worktree patch digest.

## Phase II and release

Replace each registered external assumption with a kernel-checked proof.
Every terminal declaration's transitive axiom closure must lie in
`{propext, Classical.choice, Quot.sound}`. Reject sorryAx, compiler/native
shortcuts, shadowed theorem names and unchecked custom axioms. Compare the
actual endpoint type against an independent mathematical statement, not only
against another copy of a weakened contract.

Retain exact Lean 4.33.0, Mathlib v4.33.0 and public dependency commits from
the verified lock files. Replay from a clean checkout and record invocations,
theorem types, imports, axiom reports and independent kernel results.
The current locks are Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`,
AlgebraicAnalysis `46f2c819deca0e9735a436bed94ebed03ae35090`, and Stafford38
`e77e176c381ca2d6b20c030f9227f1b031415d2e`. Any dependency update requires a
fresh downstream replay; an upstream version or release name is not that
evidence.
A semantic Challenge/Solution success does not release SS-all. Publication
remains controlled by release-gates.yaml and the release runbook.
The current endpoint files contain two semantic membership/generation
declarations, with the definitional Challenge/Solution theorem additionally
checked by the Phase II script. They do not enumerate the terminal M01–M11
closure. The current source audit rejects every project axiom, and no
registered literature-assumption workflow is implemented by these scripts.
Both phase commands therefore remain checkpoint verifiers.

The release-readiness script currently validates status labels and the
`phase`/`result` labels in evidence files. It does not validate the terminal
statement, required-check results, source identity, or publication authorization.
Its success alone cannot justify phase promotion or publication; those
obligations require the independent evidence review in the release runbook.

The independent Fable/Claude audit recorded in
`docs/audits/fable-claude-proof-audit-2026-09-08.md` found no invalid bridge
in the frozen written candidate. That verdict covers the paper-level
dependency reconstruction; human review, complete formal correspondence and
the Phase I, Phase II and Palomar gates remain open.

## Historical and concrete branches

C01–C03 map to M01/M11, P01–P02 to ordered M08, P03 to M07, P04 to M06,
and P05–P07 to M02–M05. The old R01/R02 slots now have written candidate
M08–M10; their formal proofs are required. SS4/P08, DL/Bn/Gabber lower bounds,
cusp/crossing catalogues and alternative Morita routes are optional for this
terminal proof unless a named consumer uses them. Concrete Weyl, Kleinian,
domain-Morita, applicable D(X), and higher-dimensional instances still need
actual class hypotheses. Retain the physical module/progenerator gate and
the exclusions of arbitrary-projective freeness, rank-one cancellation and
automatic simplicity of tensor products.
