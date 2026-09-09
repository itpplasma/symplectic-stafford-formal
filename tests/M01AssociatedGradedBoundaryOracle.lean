import SymplecticStafford.Filtered.M01AssociatedGradedBoundary

/-! Independent oracle for the noncommutative constant-filtration boundary. -/

namespace SymplecticStafford.M01AssociatedGradedBoundaryOracle

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.RingFiltrationData

example :
    constantMatrixFiltration.carrier 0 = (⊤ : Submodule MatrixRingᵐᵒᵖ MatrixRing) := by
  rfl

example :
    constantMatrixFiltration.carrier 0 =
      constantMatrixFiltration.carrier 7 := by
  rfl

example :
    matrixE01 * matrixE10 ≠ matrixE10 * matrixE01 :=
  matrixE01_mul_E10_ne_E10_mul_E01

example :
    ¬ (∀ (a b : MatrixRing), a * b = b * a) :=
  associatedLayerRing_commutativity_is_not_a_filtration_consequence

example :
    associatedLayerMul constantMatrixFiltration 0 0
        matrixE01Class matrixE10Class ≠
      associatedLayerMul constantMatrixFiltration 0 0
        matrixE10Class matrixE01Class :=
  associatedLayerMul_matrixE01_E10_ne_E10_E01

end SymplecticStafford.M01AssociatedGradedBoundaryOracle

#print axioms SymplecticStafford.Filtered.constantMatrixFiltration_is_not_commutative
