import Mathlib.Tactic
import SymplecticStafford.Filtered.PolynomialGoodModuleCalibration

/- Independent oracle for an actual nat-degree-filtered good module over
   `ℚ[X]`, including a negative weighted slot and right correction. -/
namespace SymplecticStafford.Filtered.PolynomialGoodModuleCalibrationOracle

open scoped Polynomial
open PolynomialGoodModuleCalibration

example : ModuleHasDegreeAtMost moduleFiltration 1 (Polynomial.X : ℚ[X]) := by
  simpa using moduleFiltration_explicit_bound (Polynomial.X : ℚ[X])

example : ∃ i, detector.triangular.action
    (detector.encode (Polynomial.X : ℚ[X])) i ≠ 0 := by
  rcases good_module_detect_nonzero (p := (Polynomial.X : ℚ[X]))
      (by simp) with ⟨n, hn, hdet⟩
  exact hdet

example : ∃ i, Matrix.vecMul
    (fun j => detector.triangular.action
      (detector.encode (Polynomial.X : ℚ[X])) j)
    (1 - correction) i ≠ 0 := by
  rcases good_module_detect_after_correction
      (p := (Polynomial.X : ℚ[X])) (by simp) with ⟨n, hn, hdet⟩
  exact hdet

end SymplecticStafford.Filtered.PolynomialGoodModuleCalibrationOracle
