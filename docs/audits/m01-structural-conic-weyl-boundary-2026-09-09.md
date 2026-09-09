# M01 structural conic/Weyl boundary

Date: 9 September 2026.

This audit checks whether the current formal M01 class can obtain its
filtered-algebra data from the paper's conic symplectic-quantization
hypothesis, using the pinned Stafford38-formal and algebraic-analysis APIs.
The result is a positive Weyl calibration and a negative generic bridge.  It
does not promote M01 or either phase gate.

## Current M01 class requirements

`AdmissibleSymplecticClass` in `SymplecticStafford/Semantics/Contract.lean`
stores `noetherian`, `simple`, `infiniteDimensional`, filtration, and
associated-graded conditions as propositions.  It does not contain a carrier
family, multiplication bounds, exhaustiveness witness, scalar embedding, or a
map from the associated graded object back to those layers.

`M01FilteredAlgebra` in
`SymplecticStafford/Filtered/M01StructuralClass.lean` is the repaired
original-ring interface: it contains an actual exhaustive multiplicative
`AdditiveFilteredRingData`, centrality of the specified field image, and an
exact degree-zero scalar-image equality.  Its associated layers are genuine
additive quotients, and multiplication of classes is defined.  It still does
not construct the global commutative affine-domain associated graded algebra.

The older `RingFiltrationData` interface is not a substitute: its layers are
right submodules for the whole ring.  The formal polynomial calibration in
`M01PolynomialFiltrationBoundary.lean` proves that the ordinary scalar degree
zero layer of `ℚ[X]` cannot have that type.  The constant `Mat₂(ℚ)` calibration
in `M01AssociatedGradedBoundary.lean` separately proves that concrete
filtered multiplication alone does not imply a commutative associated layer.

## The model-specific positive result

The pinned Stafford38 API has exactly the needed data for its presented Weyl
model.  In `Stafford38/Weyl/Filtration.lean`:

* `one_mem_bernsteinPiece` proves the unit is in degree zero;
* `mul_mem_bernsteinPiece` proves the exact additive degree bound; and
* `exists_mem_bernsteinPiece` proves exhaustiveness.

In `Stafford38/Weyl/MonicNormalization.lean`,
`eq_algebraMap_of_mem_bernsteinPiece_zero` identifies degree zero with the
field image.  Centrality is the ordinary `Algebra.commutes` theorem.  In
`Stafford38/Weyl/GradedAlgebra.lean`, the concrete pieces assemble into
`PresentedAssociatedGraded`, whose commutative ring structure is transported
through `presentedAssociatedGradedAlgEquiv` to the polynomial symbol ring.

These facts are now exposed without changing the terminal contract by
`SymplecticStafford.Filtered.WeylM01Calibration`:

```text
presentedWeylBernsteinFiltration
presentedWeylM01
presentedWeylBernsteinGradedSymbolEquiv
```

The independent oracle is
`tests/WeylM01CalibrationOracle.lean`.  It checks the original-ring degree
zero equality, exhaustive membership, multiplicative degree addition,
central scalar action, commutativity of the concrete graded object, and
injectivity of its symbol equivalence under `lake env lean --trust=0`.

This is a genuine higher-rank Weyl calibration, not a theorem about all conic
quantizations.  The global graded ring is supplied by the Stafford38 PBW
construction and is not inferred from the generic M01 filtration record.

## Generic conic quantization bridge status

The sibling paper audit
`/home/ert/proj/symplectic-stafford/notes/quantized-slice-transfer-audit-2026-09-07.md`
records the remaining quantum step precisely.  Formal or microlocal conic
slice information does not currently provide, for an arbitrary algebra `U`:

1. an algebraic carrier family `F_N ⊆ U` with finite, exhaustive,
   multiplicative bounds;
2. exact scalar degree-zero identification and faithful central action;
3. an algebraic Rees ring and a map from its associated graded to the
   classical commutative cone; or
4. one global source in the original `U` after localization and completion.

The paper audit also records four invalid substitutes.  Principal-symbol opens
need not be powers of a right Ore lift.  Raw `h`-adic specialization can
collapse at `h = 1`.  Torus-finiteness in an orbit completion does not imply
membership in the selected algebraic chart.  A universal differential
coefficient filtration would force locally nilpotent adjoints, which is
unavailable on rigid E8 fibers.

Thus the Stafford38 result proves the M01 package for a named PBW family, but
there is no sound theorem in the current project that transports it to the
paper's proposition-valued conic class. The missing theorem is an algebraic
quantization/algebraization construction with a compatible commutative graded
identification. Until that construction exists, the generic M01--M11 and
Phase I/II gates remain correctly fail-closed.

## Version evidence

The source and oracle were checked against the repository's exact pins:

```text
Lean:             leanprover/lean4:v4.33.0
Mathlib:          db584cd6d46c92f209a44c0f1c829460d327499d
AlgebraicAnalysis:add0a80d865c88fe9cbc6901bda08a636ce188f9 (v0.3.1)
Stafford38-formal:213ae2073030c8a897087152a616b8f8c1292df2 (v1.1.1)
```

No release metadata or phase status is changed by this calibration.
