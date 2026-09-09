import SymplecticStafford.FiniteLength.BoundedBelowStrictnessContract

/- Independent oracle for the bounded-below strictness contract. -/
namespace SymplecticStaffordTest.BoundedBelowStrictnessContract

open SymplecticStafford.FiniteLength

example
    (F : NatFiltration (R := ℚ) (M := ℚ →₀ ℚ))
    {A B : Submodule ℚ (ℚ →₀ ℚ)}
    (h : natLayerSurjective F A B) : A = B :=
  layerSurjective_eq_of_boundedBelow F h

example
    (F : NatFiltration (R := ℚ) (M := ℚ →₀ ℚ))
    {A B : Submodule ℚ (ℚ →₀ ℚ)} (hAB : A ≤ B) (hne : A ≠ B) :
    ¬ (∀ n : ℕ, ∀ x ∈ B, x ∈ F.carrier n →
      ∃ y, y ∈ A ∧ y ∈ F.carrier n ∧ x - y ∈ previousLayer F n) :=
  strict_inclusion_has_strict_layer F hAB hne

end SymplecticStaffordTest.BoundedBelowStrictnessContract
