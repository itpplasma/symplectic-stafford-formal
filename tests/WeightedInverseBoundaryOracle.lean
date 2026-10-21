module

public import SymplecticStafford.Filtered.WeightedInverseBoundary

@[expose] public section

namespace SymplecticStafford.Filtered.WeightedInverseBoundaryOracle

open scoped Polynomial

example : PolynomialNegativeDegree (Polynomial.X : ℤ[X]) :=
  polynomial_X_negativeDegree

example : ¬ IsUnit ((1 : ℤ[X]) - Polynomial.X) :=
  polynomial_one_sub_X_not_isUnit

example :
    ¬ (∀ c : ℤ[X], PolynomialNegativeDegree c → IsUnit (1 - c)) :=
  negativeDegree_does_not_force_one_sub_unit

example : ¬ IsUnit (1 - diagonalNegativeCorrection) :=
  one_sub_diagonalNegativeCorrection_not_isUnit

end SymplecticStafford.Filtered.WeightedInverseBoundaryOracle
