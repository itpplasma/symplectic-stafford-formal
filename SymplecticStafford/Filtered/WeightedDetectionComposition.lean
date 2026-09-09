import Mathlib.Data.Matrix.Basic
import SymplecticStafford.Filtered.WeightedFaithfulBoundary
import SymplecticStafford.Filtered.WeightedMatrixInverse

/-!
# Weighted detection after a finite correction

This file composes the two finite M04 interfaces.  A supplied weighted
triangular action first produces a nonzero output coordinate.  A correction
matrix `C` may then mix those output coordinates on the right, provided a
finite nilpotence certificate makes `1 - C` invertible.  The row convention
is deliberate: the corrected output is `vecMul w (1 - C)`, so no commuting
of coefficients is used.

The result is still conditional on both supplied finite certificates.  In
particular, this file does not construct a weighted matrix from a filtered
module, prove that a strict degree drop is nilpotent, or establish the
full-symbol Ore input of the paper.
-/

namespace SymplecticStafford.Filtered

universe u v

section

variable {ι : Type u} {K : Type v}
variable [Nonempty ι] [Fintype ι] [DecidableEq ι] [Ring K]
variable [NoZeroDivisors K]

namespace WeightedTriangularData

variable (T : WeightedTriangularData (ι := ι) (K := K))

/-- A weighted-triangular output remains nonzero after a finite nilpotent
right correction.  The matrix inverse is used in the original ring, with
the output row acting on the right. -/
theorem corrected_action_ne_zero_of_nonzero
    (C : Matrix ι ι K) (n : ℕ) (hC : C ^ n = 0)
    {v : ι → K} (hv : ∃ j, v j ≠ 0) :
    ∃ i, Matrix.vecMul (fun j => T.action v j) (1 - C) i ≠ 0 := by
  rcases T.action_ne_zero_of_nonzero hv with ⟨i, hi⟩
  by_contra hzero
  have hrow : Matrix.vecMul (fun j => T.action v j) (1 - C) = 0 := by
    funext j
    by_contra hj
    exact hzero ⟨j, hj⟩
  have hvanish : (fun j => T.action v j) = 0 :=
    WeightedMatrixInverse.vecMul_eq_zero_of_mul_one_sub_eq_zero
      (fun j => T.action v j) C n hC hrow
  exact hi (congrFun hvanish i)

end WeightedTriangularData

section Faithful

variable {M : Type*} [AddCommGroup M] [Module K M]

variable (D : FaithfulWeightedDetector (ι := ι) (K := K) (M := M))

/-- Faithful finite-coordinate detection survives a finite nilpotent right
correction.  This is the composition theorem used by the finite M04 core. -/
theorem FaithfulWeightedDetector.detect_after_nilpotent_right_correction
    (C : Matrix ι ι K) (n : ℕ) (hC : C ^ n = 0)
    {x : M} (hx : x ≠ 0) :
    ∃ i, Matrix.vecMul
      (fun j => D.triangular.action (D.encode x) j) (1 - C) i ≠ 0 := by
  have hencoded : ∃ j, (D.encode x) j ≠ 0 := by
    by_contra h
    apply D.encode_ne_zero hx
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  exact D.triangular.corrected_action_ne_zero_of_nonzero C n hC hencoded

end Faithful

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.WeightedTriangularData.corrected_action_ne_zero_of_nonzero
#print axioms
  SymplecticStafford.Filtered.FaithfulWeightedDetector.detect_after_nilpotent_right_correction
