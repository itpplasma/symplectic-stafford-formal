import SymplecticStafford.Filtered.FullSymbolWeightedBoundary
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Monic

/- Independent oracle for the M03-to-M04 boundary: actual Ore/right-clearing
   data alone does not make a strict negative correction invertible. -/
namespace SymplecticStafford.Filtered.FullSymbolWeightedBoundaryOracle

open scoped Polynomial

example : ¬ IsUnit (FullSymbolWeightedBoundary.identityData.numerator
    ((1 : ℤ[X]) - Polynomial.X)) :=
  FullSymbolWeightedBoundary.numerator_one_sub_X_not_isUnit

end SymplecticStafford.Filtered.FullSymbolWeightedBoundaryOracle
