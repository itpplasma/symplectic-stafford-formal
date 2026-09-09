import SymplecticStafford.Filtered.WeightedDetectionComposition

/-!
# Concrete finite faithful calibration for weighted detection

The abstract M04 detector is genuinely inhabited by finite free modules.  The
identity encoding on `ι → K`, with diagonal coefficients and arbitrary integer
weights, satisfies all triangular hypotheses; in particular, a negative
weight is harmless.  The calibration below is deliberately finite and
algebraic.  It does not identify this module with a good filtered module over
the paper's noncommutative algebra, so it cannot close the universal M04
bridge.
-/

namespace SymplecticStafford.Filtered

universe u v

namespace WeightedFaithfulCalibration

variable {ι : Type u} {K : Type v}
variable [Nonempty ι] [Fintype ι] [DecidableEq ι]
variable [Ring K] [Nontrivial K] [NoZeroDivisors K]

/-- Diagonal action with the supplied integer weights. -/
def diagonalSystem (weight : ι → Int) :
    WeightedTriangularData (ι := ι) (K := K) where
  weight := weight
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

/-- The identity finite-coordinate encoding is faithful. -/
def identityDetector (weight : ι → Int) :
    FaithfulWeightedDetector (ι := ι) (K := K) (M := ι → K) where
  encode := LinearMap.id
  encode_injective := by
    intro x y h
    exact h
  triangular := diagonalSystem weight

theorem identity_detect_nonzero (weight : ι → Int) {v : ι → K}
    (hv : v ≠ 0) :
    ∃ i, (identityDetector weight).triangular.action
      ((identityDetector weight).encode v) i ≠ 0 := by
  exact (identityDetector weight).detect_nonzero hv

theorem identity_detect_after_nilpotent_right_correction
    (weight : ι → Int) (C : Matrix ι ι K) (n : ℕ) (hC : C ^ n = 0)
    {v : ι → K} (hv : v ≠ 0) :
    ∃ i, Matrix.vecMul
      (fun j => (identityDetector weight).triangular.action
        ((identityDetector weight).encode v) j) (1 - C) i ≠ 0 := by
  apply FaithfulWeightedDetector.detect_after_nilpotent_right_correction
    (D := identityDetector (ι := ι) (K := K) weight) C n hC hv

end WeightedFaithfulCalibration

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.WeightedFaithfulCalibration.identity_detect_nonzero
#print axioms SymplecticStafford.Filtered.WeightedFaithfulCalibration.identity_detect_after_nilpotent_right_correction
