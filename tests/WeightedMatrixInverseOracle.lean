module

public import SymplecticStafford.Filtered.WeightedMatrixInverse
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose] public section

/- Independent behavioral oracle: the finite inverse is checked in a
   noncommutative matrix ring, with both left and right products. -/
namespace SymplecticStafford.Filtered.WeightedMatrixInverseOracle

open WeightedMatrixInverse

def toyBoundedData : BoundedBelowOneData ℚ where
  degree := fun q => if q = 0 then ⊥ else 0
  degree_zero := by simp
  degree_one := by norm_num
  degree_add_le_max := by
    intro a b
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      by_cases hab : a + b = 0 <;>
      simp [ha, hb, hab]
  degree_mul_le_add := by
    intro a b
    by_cases ha : a = 0
    · subst a
      simp
    by_cases hb : b = 0
    · subst b
      simp
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    simp [ha, hb, hab]
  below_one_inverse := by
    intro c hc
    by_cases hc0 : c = 0
    · subst c
      refine ⟨1, by ring, by ring, ?_⟩
      simp
    · simp [hc0] at hc

example (c : ℚ) (hc : toyBoundedData.degree c < 0) :
    IsUnit (1 - c) := by
  exact BoundedBelowOneData.isUnit_one_sub_of_negative toyBoundedData hc

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
