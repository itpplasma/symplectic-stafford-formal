module

public import tests.SymbolFractionReesOracle
public import SymplecticStafford.Filtered.M05SelectedSourceSurvivalProducer

@[expose] public section

/-!
# Independent oracle for the selected-source survival producer

The polynomial filtration on `ℚ[X]` is a concrete exhaustive multiplicative
filtration.  The element `X^2` forces the least layer to be degree two.  The
oracle consumes the resulting nonzero class, homogeneous Rees lift, actual
right-localized numerator, and source-map compatibility equation.

This is an oracle for the selected source construction only; it does not
identify that construction with either paper localization used in M05.
-/

namespace SymplecticStaffordTest.M05SelectedSourceSurvivalProducerOracle

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStaffordTest.SymbolFractionReesOracle
open SymplecticStafford.Filtered.SymbolFractionReesLocalization
open SymplecticStafford.Filtered.SymbolFractionReesMap

theorem polynomial_selected_source_survives :
    ∃ n : ℕ, ∃ hna : (Polynomial.X ^ 2) ∈ polyFiltration.carrier n,
      n = 2 ∧
      (∀ k < n, (Polynomial.X ^ 2) ∉ polyFiltration.carrier k) ∧
      let q := AdditiveFilteredRingData.associatedClass
        polyFiltration n (Polynomial.X ^ 2) hna
      let p := ReesNoetherianTransfer.shiftedHomogeneousLift
        polyFiltration n 0 q
      q ≠ 0 ∧
      p ≠ 0 ∧
      sourceNumerator concreteData p ≠ 0 ∧
      sourceLocalizationMap concreteData (sourceNumerator concreteData p) =
        SymbolFractionReesMap.map concreteData p := by
  obtain ⟨n, hna, hmin, hq, hp, hlocalized, hcompat⟩ :=
    exists_minimal_layer_selected_source_survival concreteData
      (a := Polynomial.X ^ 2) (by simp)
  have hlow : 2 ≤ n := by
    have h := hna
    change (Polynomial.X ^ 2).natDegree ≤ n at h
    simpa using h
  have hn : n = 2 := by
    apply Nat.le_antisymm
    · by_contra h
      have hlt : 2 < n := by omega
      apply hmin 2 hlt
      change (Polynomial.X ^ 2).natDegree ≤ 2
      simp
    · exact hlow
  refine ⟨n, hna, hn, hmin, ?_⟩
  simpa using And.intro hq
    (And.intro hp (And.intro hlocalized hcompat))

example :
    ∃ n : ℕ, ∃ hna : (Polynomial.X ^ 2) ∈ polyFiltration.carrier n,
      n = 2 := by
  obtain ⟨n, hna, hn, _⟩ := polynomial_selected_source_survives
  exact ⟨n, hna, hn⟩

end

end SymplecticStaffordTest.M05SelectedSourceSurvivalProducerOracle

#print axioms
  SymplecticStaffordTest.M05SelectedSourceSurvivalProducerOracle.polynomial_selected_source_survives
