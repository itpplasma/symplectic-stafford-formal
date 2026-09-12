# Symplectic Stafford formalization plan

```yaml
phase: parallel-all-dimensional-formalization
phase_i_status: partial
phase_ii_status: checkpoint-only
terminal_theorem_claimed: false
public_release: false
palomar_registration: not-submitted
```

## Luna-first execution policy (2026-09-09)

The reader of this section is the next controller or proof worker. Finish real
producer obligations quickly while keeping phase and submission claims tied to
replayable evidence. The task packets in [docs/luna-work-packets.md](docs/luna-work-packets.md)
contain source context, owned files, exact goals, and independent oracles; this
PLAN remains the sole status authority.

### Model ladder and ownership

Start every fresh task, including scaffolding and review, with Luna xhigh.
The controller assigns bounded statements and disjoint file ownership. Escalate the same frozen task in this order:
**Luna xhigh → Sol low → Sol medium → Astra low → Astra medium**.
After two failed substantive proof approaches, the 15-minute attempt limit,
or one identified mathematical obstruction, return the exact statement, first
unsupported inference, attempted proof, and compiler output to the controller for the next rung. A stronger model
must repair the same claim or identify its obstruction. Routine compiler
feedback stays on the same rung within the attempt budget; additional hypotheses,
weaker conclusions, and renamed consumer packages do not count as closure.

Run independent tasks in parallel, with at most seven workers across these three
repositories and one controller. Each worker owns disjoint source/test files;
only the controller changes root imports, PLAN, proof graphs, evidence receipts,
and release gates. Workers return source and evidence without committing,
pushing, publishing, or promoting state. Integrate each checked producer promptly.
Start fresh independent mathematical/statement reviews with Luna xhigh as well;
escalate a suspect inference through Sol low, Sol medium, then Astra low or medium for
unresolved mathematical composition. Drafting may precede review, but integration
and readiness require the checks below.


### Active wave: draft first, verify once

The temporary pinned dependency source/cache links became unavailable during
the drafting wave (external filesystem change). Do not fetch or rebuild
them while drafting. The consolidated pass must first restore the exact
locked revisions in one shared cache and rerun the existing pin/source audit.

The latest user instruction is to finish the Lean source drafts across the
parallel work packets before building and fixing. Do not run per-file Lean
checks or full verifiers during this drafting wave. Use existing compiler
logs and project APIs, and report incomplete proof steps explicitly. Once
the source wave is assembled, the controller starts one consolidated build
and repair pass, escalating concrete failures through the model ladder.
Keep unchecked drafts distinct from verified results; no proof holes or
new axioms may be promoted. The resource safeguards below apply when that
consolidated verification starts.

### Resource budget and verification

Reuse each checkout's pinned dependency cache. Do not clone dependencies, create
build worktrees, download new toolchains, or duplicate build trees for this wave.
Use at most three concurrent targeted Lean processes and one full verifier across
all three repositories. Store bounded logs under the existing `.lake` tree;
limit each task's scratch/log output to 64 MiB and 15 minutes per attempt. Before
starting a build, check available bytes and inodes on both the checkout and
`/tmp`; pause dependency-aware builds below 20 GiB free on the checkout,
8 GiB on `/tmp`, or 100,000 free inodes. Direct `lake env lean` checks may
continue against already present pinned artifacts while both filesystems
retain at least 8 GiB and 100,000 free inodes. Such checks must not fetch
packages or materialize dependencies, must omit C/IR outputs, and share the
three-process/64-MiB-per-task limits above. This permits bounded proof
checking; it does not count as completion of the full repository gate.
A full verifier against already present pinned dependencies may also run
below the 20 GiB dependency-materialization reserve under a controller
watchdog: stop its process group if available space drops by 512 MiB from
its starting value, either filesystem falls below 8 GiB or 100,000 free
inodes, or its captured log exceeds 16 MiB. Run only one full verifier,
with no package updates, downloads, cache copies, or dependency replacement.
This exception runs the unchanged full gate; it does not waive any check.
Remove only scratch created by this wave. A toolchain port is a separately
budgeted task, not an automatic cache download.

Freeze review inputs as the exact base commit plus SHA-256 of the binary tracked
diff and a sorted SHA-256 manifest of every untracked candidate source. Keep
unrelated edits outside the candidate manifest. A hashed uncommitted patch is
reproducible review input. Every returned theorem needs its actual carrier,
quantifiers, hypotheses, dependency closure, and an independently motivated
behavioral oracle. No proof holes, new project axioms, or circular existence
fields may enter the live closure. Run the repository's required full verifier
after integration; targeted Lean success is inner-loop evidence only.

### Submission order

Audit already proved, independently meaningful statements before scheduling a
large terminal completion. A bounded submission has its own exact Challenge,
Solution, approved axiom closure, provenance, accepted toolchain, and independent
kernel replay. It does not change the terminal Phase I/II status. Report a result
as ready immediately after those gates pass, naming its precise scope and any
remaining publication step. No percentage estimate, build count, conditional
wrapper, or comparator for a different statement establishes readiness. Public
release and registration follow the concrete final release review.

### Current dispatch

Controller draft wave: `Filtered/FiniteFilteredLengthFormula.lean` and
`tests/FiniteFilteredLengthFormulaOracle.lean` contain a bounded actual
submodule-layer length formula with a concrete `ℚ² ⊃ ℚ×0 ⊃ 0` oracle. They
are unimported and unverified until the consolidated replay; they do not
provide the paper-specific homogeneous-localization comparison or universal
M05 producer. The dependency cache is currently absent, so kernel replay is
deferred under the active draft-first rule.

The follow-up draft `Filtered/FiniteFilteredStrictMap.lean` and its oracle
expose an injective but non-surjective associated-layer map for the same
finite `ℚ² ⊃ ℚ×0 ⊃ 0` model while retaining exact ambient/induced length
formulae. It is boundary evidence only; the paper-specific Rees, homogeneous
localization, and filtered/localized-length comparison remain open.

The bounded M05 continuation `Filtered/M05Luna20260912/SourceLocalizationAdapter.lean`
packages the existing actual source-localization map as a `RingEquiv`, proves
that selected source denominators map to units, and exposes the explicit
source-fraction formula. Its independent oracle transports the concrete
opposite-degree Laurent-Rees inverse calculation through that equivalence.
This closes only the selected-source carrier adapter; the paper-specific
filtered algebra/module comparison with homogeneous localization, including
strictness or faithful homogeneous survival, remains the first unsupported
M05 bridge. The Luna backend attempt failed before output, so no escalation or
phase promotion is claimed.

The unimported `Filtered/M01FiniteHomogeneousReesProducer.lean` draft adds the
next bounded M01 consumer: from an exhaustive additive filtration and a
nonzero element it selects the least layer, produces a nonzero associated
class and actual homogeneous Rees lift, and transports its coefficient symbol
through multiplication. Its companion oracle is present but neither file has
been kernel-replayed because the pinned dependency cache is absent. The first
unsupported project bridge remains the paper-specific filtered
algebra/module-to-homogeneous-localization comparison and faithful homogeneous
survival; this draft does not promote M01–M11 or either phase gate.

Dispatch base: `deadec7`.

The symbol-selected denominator, inverse and regular-symbol degree producers are committed and verified. The working-tree continuation constructs the actual integer fraction filtration, degree-zero subring and degree-minus-one Jacobson inclusion; targeted kernel checks and independent reviews passed, with the concrete nonzero polynomial subtype/orientation oracle compiled and full replay still pending. The actual Laurent Rees subring and both homogeneous denominator inverse orientations are now constructed in `SymbolFractionRees.lean`, independently reviewed and kernel checked. The nonzero polynomial Rees oracle checks opposite degrees and both multiplication orders. `SymbolFractionReesClearance.lean` now constructs one common right homogeneous denominator for the finite nonzero coefficient support, with integer degree bounds preserved; independent review and trust-disabled checking passed. The two-term oracle checks the shifted degrees directly. Next prioritize the actual original-Rees source map and homogeneous localization comparison, Noetherianity/strictness and filtered/localized length transfer for M05. In parallel, construct the structural associated-graded/Rees producer needed by that repair. M06–M07 arbitrary division-block activation and M09–M10 original-U source/test retention need separate proofs. Stop recycling conditional interfaces or Weyl calibrations as universal advances.

The selected Challenge/Solution now targets the finite-central division-pencil theorem; its scoped Comparator, NanoDa, Lean-kernel and import-closure checks passed at the finite-pencil checkpoint. Public clean replay and release review remain pending. The former comparison was only a definitional membership contract. Neither states the universal Stafford theorem. The paper has an unresolved filtered-to-graded localized-length bridge; all M01–M11 remain open at full scope. The accepted-toolchain checkpoint and passing comparator do not close those gaps. The finite-central division-pencil theorem is the first bounded submission candidate because its toolchain and independent proof are already available; research interest and provenance still need review. The current Weyl transfer reproduces the pinned Stafford38 result and is not a new submission claim.

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
`ActualM08Producer`, `TwoCallAffineProducer`, `TwoCallDescentProducer`,
`FullSymbolRightPowerBridge`, `WeightedMatrixInverse`,
`WeightedDetectionComposition`, `CentralField`, `JacobsonScalarExtension`,
`FiniteScalarAvoidance`, `CharacteristicSupportFiniteProducer`,
`ActualClassSupport`, `FullSymbolFilteredChart`, `ReesModuleNoetherianBoundary`,
`ExplicitBlocks`, `FiniteRemovalRetentionBridge`,
`SuccessorObstruction`, `SupportRemovalArithmetic`, `DifferentialOreDescent`,
`OriginalTestProducerBoundary`, `OriginalDivisionProducer`,
`M01StructuralBoundary`, `PowerOreA1Obstruction`,
`FullSymbolWeightedBoundary`, `IsotypicBlocks`, `LayerSupportObstruction`,
`M01AssociatedGradedBoundary`, `CentralFieldFiltrationBoundary`,
`FullSymbolFilteredWeightedBoundary`, `ActualRadicalTop`, `DivisionEigenBoundary`,
`Package/TerminalBoundary`,
`Package/TerminalObstruction`, and `Package/Opposite` expose explicit
hypotheses and preserve the same boundary. M01–M11 remain open.

The 2026-09-09 parallel wave is integrated on the shared branch. It adds an
actual-right-localization-to-power-Ore bridge (`FullSymbolRightPowerBridge`),
a finite nilpotent weighted-matrix inverse and faithful row-action lemma
(`WeightedMatrixInverse`), minimal-support to finite-length consumers
(`FilteredMinimalPrimeBridge`), scalar-extension orbit-pencil activation
(`FiniteOrbitPencil`), stronger right-Noetherian colon-generator expansion
(`ActualM08Producer`), a two-call descent successor constructor
(`TwoCallDescentProducer`), and terminal same-divisor/opposite package
assembly (`terminal_sameDivisor`, `TerminalPackage` and `Package/Opposite`).
Each item is a checked conditional utility with an independent consumer; the
universal filtered chart, finite-length block decomposition, support removal,
and original-U source producer are still supplied hypotheses rather than
proved constructions.

The follow-up 2026-09-09 wave adds finite common denominators for arbitrary
right-localized families (`FullSymbolRightLocalization.common_right_clear`),
composed weighted detection after a nilpotent correction
(`WeightedDetectionComposition`), an explicit central-field filtered-algebra
record (`CentralField`), a Jacobson-top scalar-extension consumer
(`JacobsonScalarExtension`), finite bad-set union/avoidance for the two-call
step (`FiniteScalarAvoidance`), and a finite-colon characteristic-support
consumer with indexed original-ring expansions
(`CharacteristicSupportFiniteProducer`). These declarations remain
conditional on the corresponding geometric/localization inputs and do not
promote any M01–M11 gate.

The subsequent 2026-09-09 wave adds an actual filtered-layer class/support
bridge (`ActualClassSupport`), finite full-symbol chart control
(`FullSymbolFilteredChart`), a module Noetherianity criterion and explicit
sequence-ring obstruction (`ReesModuleNoetherianCriterion` and
`ReesModuleNoetherianBoundary`), bounded below-one inverse data and a diagonal
negative-degree matrix obstruction (`WeightedMatrixInverse` and
`WeightedInverseBoundary`), explicit finite composition/division/matrix block
consumers (`ExplicitBlocks`), certified nonzero original-U source selection
(`DivisionLLDList` and `OriginalDivisionProducer`), and indexed
support-removal/test-retention consumption (`FiniteRemovalRetentionBridge`).
Each is kernel-checked with an independent oracle; the universal geometric
constructions and M01–M11 phase gates remain open.

The later bounded universal-attempt wave adds checked boundary evidence:
`M01StructuralBoundary` and the historical-label/sequence-ring obstruction
show that the current proposition-only class is not a structural filtered
algebra; `PowerOreA1Obstruction` gives the coefficient-left A1 counterexample
to the principal-open-to-power-Ore shortcut; `FullSymbolWeightedBoundary`
shows actual Ore localization does not by itself provide bounded inverse
degrees; `IsotypicBlocks` consumes repeated division-ring block data while
exposing the missing finite bad-set theorem; `OriginalDivisionProducer` now
derives a single source from genuine finite top bridges; and
`LayerSupportObstruction` isolates the missing source-dependent strict support
removal. These are independently checked obstructions or conditional
consumers, not a universal producer or phase promotion.

The current continuation wave adds further checked boundaries: the
degree-zero central-field filtration interface is shown to force a surjective
field image, a constant `Mat₂(ℚ)` filtration demonstrates that generic
filtration data need not have commutative associated layers,
`ActualRadicalTop` extracts finite-length/Jacobson-top consequences from a
genuine right composition filtration, `DivisionEigenBoundary` isolates the
noncommutative finite-bad-set witness requirement, and
`FullSymbolFilteredWeightedBoundary` combines supplied chart control with the
negative-degree unit obstruction. The strong-P_h base obstruction and the
typed A₁ `OreSet` obstruction are also retained. These results narrow the
first missing universal hypotheses; they do not close M01–M11.

The second continuation wave adds positive calibrations and consumers:
`M01PolynomialFiltrationBoundary` gives a genuine ℚ[X] filtration together
with the right-ideal-layer incompatibility; `ReesPolynomialNoetherian` gives
an explicit Noetherian certificate for Mathlib's polynomial Rees algebra;
`FullSymbolActualOreFinite` clears finite families in an actual right Ore
localization; `PolynomialGoodModuleCalibration` supplies a genuine good
polynomial module with negative-weight detection; `CentralFinitePencil`
handles split finite-dimensional central realizations of repeated
division-ring blocks; `WeylA1Calibration` records the literal A₁ original-ring
identity and Stafford38 finite-potential adapter; and `NatSupportRemoval`
checks a non-vacuous concrete successor with carried-test retention. Each
source and oracle is trust-disabled checked. These are model calibrations or
conditional consumers, not the universal filtered-class, arbitrary-block,
support-removal, base or successor producer, so all gates remain pending.

The third continuation wave adds bounded bridges aimed at the first universal
interfaces: `M01StructuralClass` supplies additive-subgroup filtered-ring
layers, degree-zero field action and least-layer detection; `BoundedReesBridge`
decomposes actual bounded Rees elements into homogeneous lifts and gives a
conditional Noetherian criterion; `FullSymbolOriginalCofactor` recombines one
localized two-generator identity into literal original-ring cofactors;
`GoodWeightedModule` constructs generic finite weighted detection over a
`RingFiltrationData`; `FiniteCentralDivisionPencil` handles
finite-dimensional-over-the-center division blocks; `FiniteDimensionalProducer`
selects one original-U source from split finite-dimensional test pencils; and
`CentralFieldSupportRemoval` supplies central-field polynomial exceptional-set
avoidance plus support-removal/test-retention consumption. Every source and
oracle is trust-disabled checked. These interfaces still require the actual
filtered quantum algebraization, finite local-pass/support bridges, and
producer hypotheses, so M01–M11 and both phase gates remain open.

The fourth continuation wave composes those interfaces further:
`AssociatedGradedSpecBridge` maps actual filtered layers to a commutative
associated module and derives support/annihilator zero-locus consequences;
`ReesNoetherianTransfer` transfers Noetherianity to the bounded Rees ring under
finite homogeneous lifting; `FullSymbolOriginalCofactor` is consumed by
`LocalizedDivisorAssembly` to recombine localized divisor certificates into
original-U assembly; `GoodWeightedSupportBridge` turns weighted detection into
a nonzero filtered class and support witness; `FiniteCentralDivisionActivated`
composes finite-central division blocks with the Jacobson-top pencil consumer;
`FiniteDimensionalAssembly` packages per-divisor split finite-dimensional source
selection into SameDivisorS1; and `CentralFieldTwoCallSuccessor` composes
central-field polynomial avoidance with the two-call successor. All are
trust-disabled checked consumers with explicit hypotheses. The general quantum
algebraization, denominator construction, local module bridges, and universal
producer remain open; no phase gate is promoted.

The fifth continuation wave adds further explicit compositions:
`M01AssociatedSpecAdapter` attaches a supplied commutative associated-ring/module
map to the structural M01 class; `BoundedLayerSupport` transports quotient
support, dimension, and integer defect across an explicit bounded layer
reindexing; `FullSymbolFiniteAssembly` clears a finite family of localized
identities with one supplied right denominator;
`CorrectedGoodWeightedSupportBridge` retains negative-weight detection through
a nilpotent correction; `MinimalPrimeCentralActivated` composes minimal-prime
local length with finite-central activated pencils; `FiniteTestFamilyAssembly`
retains all offsets and nonzero tails through divisor assembly; and
`CentralFieldFiniteIndex` packages the two-call successor into the finite-index
endpoint. Each remains conditional on its displayed algebraic, local, chart,
or producer data, so the universal higher-dimensional source theorem and phase
gates remain open.

An independent review of this fifth wave corrected the bounded-layer oracle
description, strengthened retained-test negative checks, made the activated
block oracle consume its ordered identity, and conditioned central-field
support removal on non-exceptional scalars before deriving the output defect
bound. The corrected source/oracle set remains conditional and does not alter
the universal obstruction or any release gate.

The seventh frontier wave then tested the first unsupported producers with
distinct discovery, falsification, repair, and abstraction lanes. It adds a
one-way finite-dimensional original-U source selector
(`FiniteDimensionalOneWayProducer`) and records three independent boundaries:
central-field scalar avoidance does not imply source-dependent strict support
removal (`CentralFieldSupportObstruction`), finite generation does not imply
finite bad sets for arbitrary repeated division-ring pencils
(`RepeatedDivisionBlockBoundary`), and torsion modules need not admit finite
faithful weighted coordinate detectors (`FiniteCoordinateDetectorBoundary`).
The structural lane also identified the missing finite-support associated-ring
assembly and compatible quotient-module presentation; the Rees lane isolated
the homogeneous ideal-lifting certificate; and the Ore lane rechecked the A1
power-Ore counterexample. Every new source/oracle pair passed
`lake env lean --trust=0`. These results sharpen the hypotheses but do not
construct the universal algebraic source, so Phase I, Phase II, Palomar and
publication remain fail-closed.

The eighth frontier wave adds an explicit affine-graded presentation for the
bounded Rees ring (`LocallyFiniteAffineGradedRing` and
`BoundedReesRingPresentation`) and a determinant-free finite-central pencil
theorem (`FiniteCentralDivisionLLD`). Both are kernel-checked conditional
bridges. An independent audit then located the first load-bearing gap in the
paper's Part I.5: homogeneous-symbol localization gives `G_{Sigma_p}`, not
the ordinary prime localization `G_p`, so the asserted ungraded local-length
bound is unavailable. The proposed repair is a graded-length-to-filtered-chain
theorem over `G_{Sigma_p}`; until that and the actual support/localization map
are proved, M05 feeds no universal M09/M10 construction and both phase gates
remain open.

The ninth frontier wave records the exact interfaces exposed by that audit.
`GradedFilteredLength` proves one-step length additivity only when an actual
filtered quotient is linearly equivalent to the corresponding localized
graded factor. `GradedLengthFilteredChainBoundary` gives a strict filtered
submodule whose every induced layer map is surjective, so graded length alone
cannot establish strict filtered-chain descent without a Zariskian/strictness
hypothesis. `ReesModuleActionBridge` constructs the honest bounded-Rees module
action by evaluation at the central value one and explicitly does not identify
it with the filtered action. `FiniteLengthSourceMapBoundary` shows that finite
length and a top bridge do not manufacture an original-U source map.
`WeylHigherDimensionalMonicization` supplies a positive Weyl-only calibration:
every nonzero presented Weyl element is scalar or has an original-ring monic
outer representative with a positive-coordinate remainder factorization.
All five source/oracle pairs are conditional or boundary evidence; they do
not supply the universal original-U producer, close M01--M11, or promote any
phase or release gate.

The tenth frontier wave adds three bounded advances. `BoundedBelowStrictnessContract`
proves that an exhaustive monotone finite-below filtration with zero bottom
layer makes layer-surjectivity force equality, giving a precise sufficient
strictness hypothesis (without asserting it for `T_p`). `ReesModuleShift`
records degree-shifted filtered linear maps and their induced quotient maps,
including the existing single-term Rees action, while refusing to infer a
full Rees/associated action. `OriginalOrbitProducer` uses an explicit finite
orbit basis for each local cyclic image to select one original-U affine source
for a finite test list. The Weyl calibration is also extended by
`WeylHigherDimensionalEvolutionary` and the degree-one assembly theorem to a
literal original-ring certificate for bounded finite-potential families.
These results remain conditional/calibration evidence; arbitrary source maps,
the homogeneous localization, and the universal M01--M11 producer remain
unproved, so all phase and release gates stay closed.

The eleventh frontier wave adds a conditional filtered/localized
associated-graded chain-transfer package (`FilteredLocalizedGradedBridge`), a
finite algebraic Rees specialization/evaluation bridge
(`ReesAlgebraicSpecialization`), a finite original-coefficient source package
(`OriginalFiniteCoefficientSource`), and arbitrary coefficient-left outer-monic
Weyl division with an explicit remainder bound
(`WeylHigherDimensionalArbitraryMonic`). The phase verifier now checks the
complete transitive axiom allowlist and every direct/transitive Lake checkout
against the locked revisions and origin URLs. Targeted source/oracle replay
passes; the integrated root build completes 8,911 jobs and all 150
trust-disabled oracle files pass, with the Challenge/Solution, paper
regression and Palomar replay also green. These additions remain conditional
or Weyl-only and do not supply the universal quantum algebraization/source
producer; Phase I, Phase II, Palomar registration and publication remain
fail-closed.

The twelfth frontier wave composes the repaired Part I.5 interfaces. It adds a
quantitative filtered-chain length bound
(`FilteredChainLengthBound`), a kernel-checked distinction between
homogeneous-symbol and ordinary prime localization
(`PrimeVsHomogeneousLocalizationBoundary`), finite Rees-to-original cofactor
assembly (`ReesFiniteAssembly`), divisor-indexed finite-coefficient assembly
(`OriginalFiniteCoefficientAssembly`), and a coordinate-affine higher-rank
Weyl same-divisor calibration (`WeylCoordinateAffineCalibration`). The
integrated library build completes 8,916 jobs and the new source/oracle pairs
are replayed under trust-disabled Lean. These remain conditional, boundary, or
Weyl-family results; no universal M01--M11 producer or phase/release gate is
promoted.

The thirteenth frontier wave adds a pinned AlgebraicAnalysis/Stafford38 API
bridge, a concrete Weyl M01 filtration/associated-symbol calibration and
all-rank algebra-equivalence transfer, a bounded quantized-slice-to-original-U
consumer interface, a stronger homogeneous-versus-ordinary localization
finite-length boundary, and a central-eigenvalue independence lemma over a
division ring with an independent oracle. The end-to-end paper audit records
the first invalid bridge at the filtered-to-graded localized-length step;
these checked interfaces and concrete calibrations therefore remain conditional
and do not promote M01--M11, either phase, Palomar registration, or publication.

The fourteenth frontier wave adds an exact-sequence support-union consumer and
an actual-support counterexample for M08, a source-dependent test-retention
boundary and pointwise base-producer obstruction for M09--M10, an
unstructured repeated-block activated-pencil boundary for M07, and a
nontrivial integral-domain false positive for the proposition-only historical
class. The independent global audit confirms that the first unsupported
bridge remains the filtered/Rees localized-length comparison. These are
kernel-checked boundaries and audits, not a universal producer or phase/release
promotion.

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

`Challenge.lean` and `Solution.lean` now compare the finite-central
division-pencil theorem. The existing identifier `universalStatement` is
retained for comparator compatibility and does not identify the universal
Stafford theorem. `docs/pencil-submission-scope.md` states the exact new
correspondence; older dossier listings describe the superseded checkpoint.

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
not release evidence until their complete endpoint sets exist. Publication
remains disabled in `release-gates.yaml`; the readiness script is a status and
evidence-label smoke check, not a proof of the terminal theorem. Release also
requires every listed independent replay/comparator and explicit human
authorization.

## Finite-filtration producer and bounded comparison

`FiniteFilteredModule.isFiniteLength_of_layers` now constructs finite length
of a module from a genuine finite descending filtration and finite length of
each successive quotient. Its rational-plane oracle has a nonzero proper
intermediate submodule. Luna xhigh implemented the proof; independent Sol-low
review passed. This closes the bounded finite-filtration subtask, while M05
still requires the actual localized filtration and comparison theorem.

The selected finite-central-pencil Challenge/Solution pair also passed
independent Sol-low statement review and targeted compilation. Fresh full
verification is recorded in the current wave receipt; previous comparator
receipts concern the former membership definition and cannot certify this
new pair. No universal phase or release gate is promoted.

## Canonical ideal-quotient support producer

`Ordered/M08IdealQuotientExact.lean` now constructs the canonical exact
sequence `J/I -> A/I -> A/J` for a commutative ring and ideals `I <= J`.
Injectivity, exactness, and surjectivity are proved from representatives,
and the existing exact-support theorem yields the support union. Luna
xhigh implemented it; independent Sol-low review passed after the integer
`(6) <= (2)` oracle was strengthened to prove that the right map kills
class 2 and preserves a nonzero class 1.

The producer is imported by the root and included in both endpoint lists.
Its current replay evidence is `docs/ideal-quotient-wave-20260909.json`.
The next M08 step is the actual identification of common-colon
characteristic modules with these quotients. No universal M08 obligation,
project phase, or public release gate is promoted.

## Symbol-selected denominator producer

`Filtered/SymbolDenominatorSubmonoid.lean` constructs an original-ring
submonoid from multiplicative, nonzero subsets of the actual associated
layers of an additive filtered ring. It proves selected-degree additivity
and stability under lower-order subtraction by equality of quotient
classes. The oracle uses the ordinary degree filtration on `ℚ[X]` and
compares the nonzero top classes of `X²-X` and `X²`.

This is the first construction for the localized-filtration repair. The
paper's particular symbol family, Ore property, degree-controlled fraction
filtration, and degree-zero inverse membership remain open. No M05 or
universal release gate is promoted. Review and replay evidence are recorded
in `docs/symbol-denominator-wave-20260909.json`.

## Lower-perturbation inverse with degree-zero witness

`Filtered/SymbolFractionInverse.lean` proves every selected symbol witness
has the least selected degree and that lower perturbations preserve it.
For an actual right Ore localization with exactly the selected denominator
set, it constructs the right fractions and proves both inverse identities
for `1-a/s`, with inverse `s/(s-a)` in the degree-zero fraction predicate.

That predicate is not yet a subring or a complete localized filtration.
The next step is degree-controlled Ore clearance from regular leading
symbols, followed by additive and multiplicative closure. The particular
paper localization, Rees Noetherianity, and the M05 comparison remain open.
Review and replay are recorded in `docs/fraction-inverse-wave-20260909.json`.

`Filtered/RegularSymbolDegree.lean` now supplies the degree-control
prerequisite: if the actual degree-i symbol of `s` is left regular on
every associated layer and `s*x` lies in degree n, then x lies in degree
`n-i` when `i <= n`, and x is zero otherwise. The proof uses the least
filtration degree and a nonzero quotient class. A polynomial degree
oracle verifies regular symbols and the nonzero boundary. This does not
yet construct paper-specific regularity or the fraction-filtration
closure; it is included in the same fraction-inverse wave receipt.

## Integer fraction filtration and degree-zero Jacobson boundary

`Filtered/SymbolFractionFiltration.lean` constructs the actual integer-indexed
additive fraction pieces, proves additive and multiplicative closure using
Ore cofactor degree estimates, and builds the degree-zero subring. Its
hypotheses retain the actual selected-symbol Ore localization and associated
layer left regularity; closure is proved rather than assumed.

`Filtered/SymbolFractionJacobson.lean` constructs the explicit inverse of
`1-q` inside that subring for every degree-minus-one element and proves the
degree-minus-one left ideal lies in its Jacobson radical. Both multiplication
orders and the noncommutative Jacobson criterion are explicit.

The sources passed targeted kernel checks and independent Luna-xhigh review.
The combined nonzero polynomial-fraction oracle now also compiles and
independently checks both subtype inverse orders and the Jacobson sign.
Full repository replay remains pending; these working-tree modules are not a verified main checkpoint.
The paper-specific symbol/Ore/regularity construction, homogeneous Rees
comparison, Noetherianity, strictness and localized-length transfer remain open.
