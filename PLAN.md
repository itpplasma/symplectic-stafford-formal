# Symplectic Stafford formalization plan

```yaml
phase: parallel-all-dimensional-formalization
phase_i_status: partial
phase_ii_status: checkpoint-only
terminal_theorem_claimed: false
public_release: false
palomar_registration: not-submitted
```

This file owns formal status. Semantic modules implement right ideals,
literal membership, a conditional semiring-to-ring right-ideal bridge with
relation-respecting quotient-action laws, original-ring quotient/central-support
zero detection, support-boundary extraction and explicit opposite orientation.
Ordered modules implement affine identities, the common-colon algebra, an
ordered ambient producer with simultaneous right-clearance, actual finite
right-generation from the opposite-ring Noetherian hypothesis, and
finite-generation/conditional constant-right-denominator clearing. Raw and
algebraic filtered/Rees terms, a ring-valued bounded-polynomial Rees object,
a quotient Rees module with scalar-action laws,
an explicit power-Ore fraction boundary, full arbitrary-submonoid Ore
localization, a strict Rees Noetherianity reduction certificate, finite
associated-top and matrix pencils, finite bounded-generator filtrations,
finite power-Ore normal forms, a finite associated-layer support proxy,
explicit additive ring-filtration layers and associated classes, explicit
right-module composition filtrations and Jacobson-top generation
reflection, a minimal-prime local finite-length core, actual module-support
consumption, differential-Ore finite-cover clearing, concrete finite-index
successor contracts, constructive successor assembly, original-affine source
selection, list-indexed division-LLD source selection, an original-test
producer boundary, an original-U division-test source selector, finite-
orbit-basis activated pencils, infinite-multiplicity and negative-degree
inverse boundaries, faithful weighted detection, explicit M08 support-union
boundary, support-removal defect arithmetic, and strong-P_h/terminal
obstructions are now checked utilities, while filtered, source-assembly and
strong P_h producer modules remain explicit conditional scaffolds. These
utilities do not yet establish the paper's arbitrary finite-length module,
activated-pencil, support-union, or original-U simultaneous-source theorem.

The conditional checkpoints consume supplied data:
`Filtered/Localization.lean` uses filtration/map and power-clearing fields;
`Source/Assembly.lean` extracts S1 from divisor-indexed original certificates;
`Induction/StrongPh.lean` records finite tests, integer bounds, lower-index
calls, supplied successor output and conditional terminal extraction; and
`Induction/FiniteIndex.lean` composes supplied P_1 and successor rules. Their
LEAN-SCAFFOLD map nodes mark consumers, not constructions of the required
data. `SupportDimension`, `RightIdealBridge`, `CharacteristicSupport`,
`ActivatedPencil`,
`MatrixPencil`, `CommonColon`, `FiniteGenerationBridge`,
`M08SupportUnion`, `ReesBasic`, `ReesAlgebra`, `ReesModule`,
`ReesRing`, `CommutativeFullSymbol`, `AssociatedLayerRing`,
`GoodFiltration`, `PowerOre`, `FinitePowerOre`, `FiniteSupportDetection`,
`FiniteSupportQuotient`, `SpecCharacteristicSupport`, `OriginalCentralSupport`,
`FullSymbolOre`, `FullSymbolRightLocalization`,
`FullSymbolRightModuleLocalization`, `FullSymbolLocalization`,
`ReesNoetherianCriterion`,
`NoetherianBoundary`, `RingFiltrationBridge`, `RightFiltration`,
`GoodLocalBridge`, `JacobsonTop`,
`ActivatedFiniteLength`, `FiniteOrbitPencil`, `DerivedOrbitPencil`,
`FilteredMinimalPrimeBridge`, `DivisionLLDList`,
`WeightedFaithfulBoundary`, `WeightedInverseBoundary`,
`InfiniteMultiplicityBoundary`, `MinimalPrimeLocalTheorem`,
`SupportUnionBoundary`,
`CommonColonProducer`, `ConcreteSuccessor`, `ConstructiveSuccessor`,
`ActualM08Producer`, `TwoCallAffineProducer`,
`SuccessorObstruction`, `SupportRemovalArithmetic`, `DifferentialOreDescent`,
`OriginalTestProducerBoundary`, `OriginalDivisionProducer`,
`Package/TerminalBoundary`,
`Package/TerminalObstruction`, and `Package/Opposite` expose explicit
hypotheses and preserve the same boundary. M01–M11 remain open.

The paper candidate is in the sibling `symplectic-stafford` repository at
commit `502b65a1dea53cac52220a08e321bfba525bc72e`. Its claims remain paper
claims until the corresponding Lean declarations and audits are complete.
Its terminal index, roadmap and ledger were refreshed at
`e3c7077d3d51772d97d8e72bb219a8fc36765682`. The paper is a complete
self-audited candidate in every finite dimension; independent mathematical
audit, human review and both formal phases remain separate obligations.

The final target is `∀ d ≠ 0, ∃ F R S, 1 = d * R + (F * d) * S`,
strengthened to `∀ d ≠ 0, ∀ B, ∀ a ≠ 0, ∃ H R S,
1 = d * R + ((B + H * a) * d) * S` in the original algebra.
The ambient algebra is simple, infinite-dimensional and unital over an
infinite characteristic-zero central field, with an exhaustive separated
nonnegative multiplicative locally finite filtration, degree-zero piece equal
to the field, and commutative affine-domain associated graded of finite
dimension. No DL/Bn lower support bound is a premise of this final core.

## Parallel implementation

Use [the phase instructions](docs/phase-instructions.md) and
`docs/proof-graph.yaml`. Mandatory final-paper obligations are M01–M11:
semantics; filtered/Rees foundations; full-symbol Ore localization; faithful
good-module detection; minimal-prime local length; original-U finite tests;
activated pencils; common-colon support union; strong finite-test P_h;
the two-call dimension induction; and original cofactors/opposite/package.
The controller integrates checked changes and owns phase promotion.
The existing `AdmissibleSymplecticClass` in `Contract.lean` is a historical
dimension-parametric scaffold with B2 fields and proposition labels; it does
not encode the final all-dimensional filtered-algebra class. M01 must supply
the actual structural semantics before any terminal endpoint is certified.

`Challenge.lean` and `Solution.lean` currently compare the definitional
membership contract alone. The name `universalStatement` does not identify
the universal Stafford theorem. The dossier states their exact correspondence.

## Gates

Phase I must discharge every project-owned ledger item (including the
original-ring source-selection and assembly interfaces) and record a clean
independent replay. Phase II must then replace the remaining literature
assumptions. The only permitted terminal axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The current executable checks are:

```sh
./scripts/verify.sh --phase-i
./scripts/verify.sh --phase-ii
./scripts/verify-palomar.sh
```

The first command covers the implemented checkpoint only; the latter two are
not release evidence until their complete endpoint sets exist. Publication is
fail-closed by `release-gates.yaml` and `scripts/check-release-readiness.sh`.
