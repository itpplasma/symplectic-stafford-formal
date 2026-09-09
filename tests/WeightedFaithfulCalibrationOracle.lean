import Mathlib.Tactic
import SymplecticStafford.Filtered.WeightedFaithfulCalibration

/- Independent oracle: a finite free detector with an explicitly negative
   weight remains faithful after a concrete nilpotent right correction. -/
namespace SymplecticStafford.Filtered.WeightedFaithfulCalibrationOracle

open WeightedFaithfulCalibration

def weight : Fin 2 → Int := fun i => if i = 0 then 3 else -4

def correction : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 1; 0, 0]

theorem correction_sq : correction ^ 2 = 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [correction, Matrix.mul_apply, Fin.sum_univ_succ]

def input : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0

theorem input_ne_zero : input ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [input] at h0

example : ∃ i, Matrix.vecMul
    (fun j => (identityDetector weight).triangular.action
      ((identityDetector weight).encode input) j) (1 - correction) i ≠ 0 := by
  exact identity_detect_after_nilpotent_right_correction
    weight correction 2 correction_sq input_ne_zero

example : weight 1 = -4 := by
  simp [weight]

end SymplecticStafford.Filtered.WeightedFaithfulCalibrationOracle
