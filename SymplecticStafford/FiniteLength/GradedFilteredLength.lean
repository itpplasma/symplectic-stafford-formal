import Mathlib.RingTheory.Length
import Mathlib.RingTheory.FiniteLength

/-!
# An exact graded-length to filtered-extension bridge

The homogeneous-symbol localization at a minimal support point is
`G_{Σ_p}`, not the ordinary localization `G_p`.  Consequently a graded
composition argument can be transferred to a filtered module only after the
actual adjacent filtered quotient has been identified with the corresponding
graded factor (with the same coefficient action).

This file records and proves that local step.  `GradedFilteredExtension`
contains a genuine filtered submodule, its finite-length graded factor, and a
linear equivalence from the actual quotient to that factor.  The resulting
length formula is exact and uses the original quotient sequence.  In
particular, no ordinary prime localization, commutativity of a symbol ring,
or unproved identification of a Rees/associated-graded object is hidden in
the theorem.

The interface is deliberately one-step: a future `G_{Σ_p}` construction can
iterate it along a finite graded composition chain.  It is stronger than
merely assuming that the filtered module has finite length, while making the
missing quotient/action bridge explicit.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {G : Type w} [AddCommGroup G] [Module R G]

/-- One exact adjacent step in a filtered-to-graded length transfer.

`submodule` is an actual filtered layer of `M`; `gradedFactor` is the
corresponding (already localized, if appropriate) graded factor.  The
equivalence is required to be `R`-linear, so it preserves the full submodule
lattice relevant to composition length.  This is the precise action
compatibility missing from a bare additive or ungraded identification.
-/
structure GradedFilteredExtension where
  submodule : Submodule R M
  submodule_finite : IsFiniteLength R submodule
  graded_factor_finite : IsFiniteLength R G
  quotient_equiv : (M ⧸ submodule) ≃ₗ[R] G

namespace GradedFilteredExtension

variable (E : GradedFilteredExtension (R := R) (M := M) (G := G))

/-- The actual quotient in one filtered step has finite length. -/
theorem quotient_isFiniteLength :
    IsFiniteLength R (M ⧸ E.submodule) := by
  exact E.quotient_equiv.symm.isFiniteLength E.graded_factor_finite

/-- Finite length is closed under this actual filtered extension. -/
theorem isFiniteLength (E : GradedFilteredExtension (R := R) (M := M) (G := G)) :
    IsFiniteLength R M := by
  have hsub : IsNoetherian R E.submodule ∧ IsArtinian R E.submodule :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp E.submodule_finite
  have hquot : IsNoetherian R (M ⧸ E.submodule) ∧
      IsArtinian R (M ⧸ E.submodule) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp E.quotient_isFiniteLength
  apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
  exact
    ⟨(isNoetherian_iff_submodule_quotient E.submodule).mpr ⟨hsub.1, hquot.1⟩,
      (isArtinian_iff_submodule_quotient E.submodule).mpr ⟨hsub.2, hquot.2⟩⟩

/-- Exact additivity of length for the filtered step and its graded factor. -/
theorem length_eq_add (E : GradedFilteredExtension (R := R) (M := M) (G := G)) :
    Module.length R M = Module.length R E.submodule + Module.length R G := by
  have hExact :
      Module.length R M = Module.length R E.submodule +
        Module.length R (M ⧸ E.submodule) :=
    Module.length_eq_add_of_exact E.submodule.subtype E.submodule.mkQ
      (Submodule.subtype_injective E.submodule)
      E.submodule.mkQ_surjective
      (LinearMap.exact_subtype_mkQ E.submodule)
  rw [hExact, E.quotient_equiv.length_eq]

end GradedFilteredExtension

end

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.GradedFilteredExtension.quotient_isFiniteLength
#print axioms
  SymplecticStafford.FiniteLength.GradedFilteredExtension.isFiniteLength
#print axioms
  SymplecticStafford.FiniteLength.GradedFilteredExtension.length_eq_add
