import SymplecticStafford.Filtered.CentralField

/-! Independent trust-disabled checks for the concrete M01 central-field API. -/

namespace SymplecticStafford.CentralFieldOracle

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.CentralFieldFilteredAlgebra
open SymplecticStafford.Filtered.RingFiltrationData

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

example : Function.Injective (algebraMap ℚ ℚ) :=
  CentralFieldFilteredAlgebra.algebraMap_injective ℚ ℚ

example (a : ℚ) :
    a ∈ rationalTop.filtration.carrier 0 ↔
      ∃ k : ℚ, a = algebraMap ℚ ℚ k :=
  CentralFieldFilteredAlgebra.mem_degree_zero_iff ℚ ℚ rationalTop a

example (n : ℕ) (k a : ℚ) (ha : a ∈ rationalTop.filtration.carrier n) :
    algebraMap ℚ ℚ k * a ∈ rationalTop.filtration.carrier n ∧
      a * algebraMap ℚ ℚ k ∈ rationalTop.filtration.carrier n :=
  CentralFieldFilteredAlgebra.scalar_mem_same_layer ℚ ℚ rationalTop k ha

example {a : ℚ} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ rationalTop.filtration.carrier n,
      associatedClass rationalTop.filtration n a hna ≠ 0 :=
  CentralFieldFilteredAlgebra.separated_detection ℚ ℚ rationalTop ha

end SymplecticStafford.CentralFieldOracle

#print axioms SymplecticStafford.CentralFieldOracle.rationalTop
