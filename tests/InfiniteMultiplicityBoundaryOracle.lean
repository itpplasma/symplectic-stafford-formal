module

public import SymplecticStafford.FiniteLength.InfiniteMultiplicityBoundary

@[expose] public section

namespace SymplecticStafford.FiniteLength.InfiniteMultiplicityBoundaryOracle

example : ¬ Module.Finite ℚ (ℕ →₀ ℚ) :=
  finsupp_nat_rat_not_moduleFinite

example : ¬ IsFiniteLength ℚ (ℕ →₀ ℚ) :=
  finsupp_nat_rat_not_isFiniteLength

end SymplecticStafford.FiniteLength.InfiniteMultiplicityBoundaryOracle
