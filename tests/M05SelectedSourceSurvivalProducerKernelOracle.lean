import tests.SymbolFractionReesOracle
import SymplecticStafford.Filtered.M05SelectedSourceSurvivalProducerKernel

/-!
# Independent oracle for the kernel-checked selected-source producer

The concrete filtration on `ℚ[X]` makes the least layer of `X^2` visibly
equal to two.  This oracle consumes the checked producer and separately
forces that layer, then checks the nonzero class, nonzero Rees lift, nonzero
actual source numerator, and its source-map transport equation.

Only the concrete selected-source construction is tested here; no paper
localization or global M05 conclusion is used.
-/

namespace SymplecticStaffordTest.M05SelectedSourceSurvivalProducerKernelOracle

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStaffordTest.SymbolFractionReesOracle
open SymplecticStafford.Filtered.SymbolFractionReesLocalization
open SymplecticStafford.Filtered.SymbolFractionReesMap

theorem polynomial_selected_source_survives_kernel :
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
    exists_minimal_layer_selected_source_survival_kernel concreteData
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
    ∃ n : ℕ, ∃ _hna : (Polynomial.X ^ 2) ∈ polyFiltration.carrier n,
      n = 2 := by
  obtain ⟨n, hna, hn, _⟩ := polynomial_selected_source_survives_kernel
  exact ⟨n, hna, hn⟩

end

end SymplecticStaffordTest.M05SelectedSourceSurvivalProducerKernelOracle

#print axioms
  SymplecticStaffordTest.M05SelectedSourceSurvivalProducerKernelOracle.polynomial_selected_source_survives_kernel
