module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.WeightedDetectionComposition

@[expose] public section

/- Independent behavioral oracle for the composition theorem.  The matrix is
  an explicit 2-by-2 rational nilpotent correction; both products are in the
  row/right order used by the theorem. -/
namespace SymplecticStafford.Filtered.WeightedDetectionCompositionOracle

open WeightedTriangularData

def diagonalSystem : WeightedTriangularData (ι := Fin 2) (K := ℚ) where
  weight := fun i => (i : Nat)
  coefficient := fun i j => if i = j then 1 else 0
  lower_vanish := by
    intro i j h
    by_cases hij : i = j
    · subst j
      simp at h
    · simp [hij]
  same_weight_vanish := by
    intro i j hij _
    simp [hij]
  diagonal_ne_zero := by
    intro i
    simp

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

def detector : FaithfulWeightedDetector
    (ι := Fin 2) (K := ℚ) (M := Fin 2 → ℚ) where
  encode := LinearMap.id
  encode_injective := by
    intro x y h
    exact h
  triangular := diagonalSystem

example : ∃ i, Matrix.vecMul
    (fun j => detector.triangular.action (detector.encode input) j)
    (1 - correction) i ≠ 0 := by
  exact detector.detect_after_nilpotent_right_correction
    correction 2 correction_sq (by exact input_ne_zero)

/- The actual row is `[1, -1]`, so this check also exercises the
   noncommuting right-product orientation rather than only existence. -/
example : Matrix.vecMul
    (fun j => detector.triangular.action (detector.encode input) j)
    (1 - correction) = fun i => if i = 0 then 1 else -1 := by
  funext i
  fin_cases i <;>
    norm_num [detector, diagonalSystem, input, correction,
      WeightedTriangularData.action, Matrix.vecMul,
      Fin.sum_univ_succ]

end SymplecticStafford.Filtered.WeightedDetectionCompositionOracle
