import Mathlib.Tactic
import Stafford38.Weyl.IteratedEquivalence

/-! Independent behavioral oracle for the coordinate-affine calibration.

The oracle does not invoke `presentedWeyl_coordinate_affine`.  It uses the
newest Weyl commutator and a concrete rank-two transverse tail with two
noncommuting old coefficients, then checks the literal original-ring
cofactor order.
-/

namespace SymplecticStafford.WeylCoordinateAffineCalibrationOracle

open Stafford38.WeylIteratedEquivalence

abbrev W := PresentedWeyl ℚ 2

private def x : W := presentedCoordinate ℚ 1
private def p : W := presentedMomentum ℚ 1
private def a : W := previousWeylEmbedding ℚ 1 (presentedCoordinate ℚ 0)
private def b : W := previousWeylEmbedding ℚ 1 (presentedMomentum ℚ 0)
private def A : W := a + b * p
private def d : W := x - A

private theorem a_commutes_p : a * p = p * a := by
  exact (presentedMomentum_commutes_previous ℚ 1
    (presentedCoordinate ℚ 0)).symm

private theorem b_commutes_p : b * p = p * b := by
  exact (presentedMomentum_commutes_previous ℚ 1
    (presentedMomentum ℚ 0)).symm

private theorem tail_commutes : A * p = p * A := by
  dsimp [A]
  calc
    (a + b * p) * p = a * p + (b * p) * p := add_mul _ _ _
    _ = p * a + (b * p) * p := by
      rw [a_commutes_p]
    _ = p * a + (p * b) * p := by rw [b_commutes_p]
    _ = p * a + p * (b * p) := by rw [mul_assoc]
    _ = p * (a + b * p) := (mul_add p a (b * p)).symm

example : b * a = a * b + 1 := by
  simpa [a, b] using congrArg (previousWeylEmbedding ℚ 1)
    (presentedMomentum_mul_coordinate ℚ 0)

example :
    ∃ R S : W, 1 = d * R + p * d * S := by
  refine ⟨0 - p, 1, ?_⟩
  dsimp [d]
  have hw : p * x = x * p + 1 := presentedMomentum_mul_coordinate ℚ 1
  change 1 = (x - A) * (0 - p) + p * (x - A) * 1
  simp only [sub_mul, mul_sub, zero_mul, mul_zero, one_mul, mul_one]
  rw [tail_commutes, hw]
  noncomm_ring

#print axioms tail_commutes

end SymplecticStafford.WeylCoordinateAffineCalibrationOracle
