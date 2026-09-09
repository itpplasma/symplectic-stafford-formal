import SymplecticStafford.Filtered.M01DegreeZeroBridge

/-! Independent oracle for the concrete degree-zero quotient equivalence. -/

namespace SymplecticStafford.M01DegreeZeroBridgeOracle

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.RingFiltrationData
open SymplecticStafford.Filtered.CentralFieldFilteredAlgebra

def rationalConstantFiltration : RingFiltrationData (R := ℚ) where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def rationalFilteredAlgebra : CentralFieldFilteredAlgebra ℚ ℚ where
  filtration := rationalConstantFiltration
  central := by intro k a; simp [mul_comm]
  degree_zero := by
    ext a
    constructor
    · intro ha
      exact ⟨a, by simp⟩
    · rintro ⟨k, rfl⟩
      simp [rationalConstantFiltration]

example :
    Function.Injective
      (degreeZeroMap rationalFilteredAlgebra) :=
  degreeZeroMap_injective rationalFilteredAlgebra

example :
    Function.Surjective
      (degreeZeroMap rationalFilteredAlgebra) :=
  degreeZeroMap_surjective rationalFilteredAlgebra

example :
    degreeZeroClass rationalFilteredAlgebra (1 : ℚ) ≠ 0 := by
  exact degreeZeroClass_ne_zero rationalFilteredAlgebra one_ne_zero

example :
    degreeZeroEquiv rationalFilteredAlgebra (1 : ℚ) ≠ 0 := by
  simpa using (degreeZeroClass_ne_zero rationalFilteredAlgebra one_ne_zero)

end SymplecticStafford.M01DegreeZeroBridgeOracle

#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.degreeZeroMap_injective
