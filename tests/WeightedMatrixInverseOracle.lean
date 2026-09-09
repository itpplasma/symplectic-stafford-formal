import SymplecticStafford.Filtered.WeightedMatrixInverse
import Mathlib.Tactic

/- Independent behavioral oracle: the finite inverse is checked in a
   noncommutative matrix ring, with both left and right products. -/
namespace SymplecticStafford.Filtered.WeightedMatrixInverseOracle

open WeightedMatrixInverse

def strictCorrection : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 0, 0]

theorem strictCorrection_sq : strictCorrection ^ 2 = 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [strictCorrection, Matrix.mul_apply, Fin.sum_univ_succ]

example : IsUnit (1 - strictCorrection) := by
  exact isUnit_one_sub_of_pow_eq_zero strictCorrection 2 strictCorrection_sq

example : ∃ S : Matrix (Fin 2) (Fin 2) ℤ,
    (1 - strictCorrection) * S = 1 ∧
      S * (1 - strictCorrection) = 1 := by
  exact finite_inverse_of_pow_eq_zero strictCorrection 2 strictCorrection_sq

end SymplecticStafford.Filtered.WeightedMatrixInverseOracle
