# M05 quantitative localization-length contrast

Date: 9 September 2026

This checkpoint sharpens the Part I.5 boundary between ordinary prime
localization and localization at the homogeneous symbols outside a prime.
It is an independently replayable model calculation, not a claim about the
unconstructed quantum localization.

## Kernel-checked result

`SymplecticStafford/FiniteLength/PrimeVsHomogeneousLocalizationBoundary.lean`
now proves, for the A1 coefficient model,

* the Laurent coefficient ring `ℚ[T,T⁻¹]` has a proper nonzero ideal and its
  regular module is not finite length;
* the fraction field of `ℚ[T]`, which models the corresponding ordinary-prime
  coefficient module, has regular-module length exactly one;
* these facts are combined in
  `homogeneous_vs_ordinary_length_contrast`.

The theorem uses Hopkins--Levitzki for the implication from finite length of a
regular module to Artinianity, and a nontrivial evaluation kernel to contradict
Artinianity of the Laurent ring.  The fraction-field statement uses the
division-ring simple-module instance and `Module.length_eq_one`.

The independent consumer is
`tests/PrimeVsHomogeneousLocalizationBoundaryOracle.lean`.  Both the source
and oracle replay with `lake env lean --trust=0`; the source module also builds
through `lake build SymplecticStafford.FiniteLength.PrimeVsHomogeneousLocalizationBoundary`.
The resulting proof depends only on the Lean kernel's ordinary quotient and
ring facts (`propext`, choice, and quotient soundness); it introduces no
axiom or release-gate change.

## Exact M05 replacement obligation

The calculation does not prove that the actual filtered module is either
coefficient model.  It rules out the paper shortcut

```text
finite length over G_p  ⇒  finite length over G_{Σ_p}  ⇒  finite filtered-chain bound.
```

To reopen that route, a producer must supply one of the following exact
bridges for the *actual* module and its homogeneous-symbol localization:

1. a direct finite-length theorem for the localized actual module; or
2. a Rees-saturation/Zariskian strictness theorem giving an exhaustive
   bounded-below filtration whose every proper localized submodule inclusion
   has a non-surjective associated layer map over `G_{Σ_p}`, together with an
   action-preserving identification of each filtered quotient with that
   localized graded factor.

The existing `FilteredLocalizedGradedBridge`,
`GradedFilteredLength`, and `BoundedBelowStrictnessContract` consume precisely
these supplied maps, strict-survival witnesses, and quotient equivalences.
They do not construct the chart, the Rees module, the homogeneous Ore
localization, or the original-U source.  Thus this quantitative model result
strengthens the obstruction while leaving M01--M11 and both phase gates
unchanged.
