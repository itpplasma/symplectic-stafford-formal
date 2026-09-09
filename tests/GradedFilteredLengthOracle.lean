import SymplecticStafford.FiniteLength.GradedFilteredLength
import Mathlib.Algebra.Field.Rat

/-!
# Independent oracle for the exact graded/filtered extension bridge

This oracle uses the actual quotient by the zero submodule as the graded
factor.  It exercises both finite-length closure and exact length additivity;
the theorem is not discharged by a proposition-valued placeholder.
-/

namespace SymplecticStafford.FiniteLength.GradedFilteredLengthOracle

open SymplecticStafford.FiniteLength

def zeroExtension :
    GradedFilteredExtension (R := ℚ) (M := ℚ)
      (G := ℚ ⧸ (⊥ : Submodule ℚ ℚ)) where
  submodule := ⊥
  submodule_finite := by
    exact IsFiniteLength.of_subsingleton
  graded_factor_finite := by
    have hfinite : IsFiniteLength ℚ ℚ := by
      apply isFiniteLength_iff_isNoetherian_isArtinian.mpr
      constructor <;> infer_instance
    exact IsFiniteLength.of_surjective hfinite
      (Submodule.mkQ_surjective (⊥ : Submodule ℚ ℚ))
  quotient_equiv := LinearEquiv.refl ℚ _

example : IsFiniteLength ℚ ℚ :=
  GradedFilteredExtension.isFiniteLength zeroExtension

example :
    Module.length ℚ ℚ =
      Module.length ℚ (⊥ : Submodule ℚ ℚ) +
        Module.length ℚ (ℚ ⧸ (⊥ : Submodule ℚ ℚ)) :=
  GradedFilteredExtension.length_eq_add zeroExtension

end SymplecticStafford.FiniteLength.GradedFilteredLengthOracle

#print axioms
  SymplecticStafford.FiniteLength.GradedFilteredLengthOracle.zeroExtension
#print axioms
  SymplecticStafford.FiniteLength.GradedFilteredExtension.isFiniteLength
#print axioms
  SymplecticStafford.FiniteLength.GradedFilteredExtension.length_eq_add
