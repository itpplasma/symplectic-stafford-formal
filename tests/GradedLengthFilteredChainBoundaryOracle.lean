import SymplecticStafford.FiniteLength.GradedLengthFilteredChainBoundary

/- Independent oracle for the strict filtered-chain boundary. -/
namespace SymplecticStaffordTest.GradedLengthFilteredChainBoundary

open SymplecticStafford.FiniteLength

example : sumZero ≠ (⊤ : Submodule ℚ LaurentVector) :=
  sumZero_ne_top

example : sumZero ≠ (⊥ : Submodule ℚ LaurentVector) :=
  sumZero_nontrivial

example : layerSurjective sumZero :=
  sumZero_layerSurjective

example :
    sumZero < (⊤ : Submodule ℚ LaurentVector) ∧
      layerSurjective sumZero :=
  strict_inclusion_invisible

end SymplecticStaffordTest.GradedLengthFilteredChainBoundary
