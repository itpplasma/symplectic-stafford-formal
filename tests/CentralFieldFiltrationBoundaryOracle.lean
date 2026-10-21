module

public import SymplecticStafford.Filtered.CentralFieldFiltrationBoundary

@[expose] public section

/- Independent oracle for the degree-zero/right-submodule incompatibility. -/
namespace SymplecticStaffordTest.CentralFieldFiltrationBoundary

open SymplecticStafford.Filtered

def rationalTop : CentralFieldFilteredAlgebra ℚ ℚ where
  filtration :=
    { carrier := fun _ => ⊤
      one_mem := by simp
      mul_mem := by
        intro i j a b ha hb
        simp
      monotone := by
        intro i j hij a ha
        simp
      exhaustive := by
        intro a
        exact ⟨0, by simp⟩ }
  central := by
    intro k a
    exact mul_comm _ _
  degree_zero := by
    ext a
    constructor
    · intro ha
      exact ⟨a, by simp⟩
    · rintro ⟨k, rfl⟩
      simp

example : Function.Surjective (algebraMap ℚ ℚ) :=
  rationalTop.algebraMap_surjective

example :
    (rationalTop.filtration.carrier 0 : Set ℚ) = Set.univ :=
  rationalTop.degree_zero_forces_top

example (a : ℚ) : a ∈ rationalTop.filtration.carrier 0 := by
  have htop := rationalTop.degree_zero_forces_top
  change a ∈ (rationalTop.filtration.carrier 0 : Set ℚ)
  rw [htop]
  trivial

end SymplecticStaffordTest.CentralFieldFiltrationBoundary
