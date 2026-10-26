import Mathlib.Tactic
import SymplecticStafford.Filtered.M01FiniteHomogeneousReesProducerKernel
import SymplecticStafford.Filtered.SymbolFractionReesLocalization

/-!
# Kernel-checked selected-source survival producer

This is the bounded M05 continuation of the checked M01 kernel producer.  A
nonzero source element is assigned its least filtration layer; the resulting
associated class and homogeneous Rees lift are nonzero, and the Rees lift has
a nonzero numerator in the actual selected-source right localization.  The
last assertion also records the existing source-map transport equation.

The result is only about the concrete selected-source localization already
provided by `SymbolFractionReesLocalization`.  It does not claim paper
localization, Noetherianity, faithfulness, or any M01--M11 closure.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

open SymplecticStafford
open AdditiveFilteredRingData
open SymbolFractionFiltration
open SymbolFractionReesLocalization
open ReesNoetherianTransfer

variable {R : Type u} [Ring R]

theorem exists_minimal_layer_selected_source_survival_kernel
    (C : SymbolFractionFiltration.Data R) {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ C.inverse.filtration.carrier n,
      (∀ k < n, a ∉ C.inverse.filtration.carrier k) ∧
      let q := associatedClass C.inverse.filtration n a hna
      let p := shiftedHomogeneousLift C.inverse.filtration n 0 q
      q ≠ 0 ∧
      p ≠ 0 ∧
      sourceNumerator C p ≠ 0 ∧
      sourceLocalizationMap C (sourceNumerator C p) =
        SymbolFractionReesMap.map C p := by
  obtain ⟨n, hna, hmin, hq, hp, _hpcoeff, _hxclass, _hsymbol, _hmul⟩ :=
    exists_minimal_layer_homogeneous_symbol_kernel
      C.inverse.filtration ha
  have hlocalized :
      sourceNumerator C
          (shiftedHomogeneousLift C.inverse.filtration n 0
            (associatedClass C.inverse.filtration n a hna)) ≠ 0 := by
    intro hzero
    apply hp
    apply sourceNumerator_injective C
    simpa using hzero
  refine ⟨n, hna, hmin, ?_⟩
  change
    (associatedClass C.inverse.filtration n a hna) ≠ 0 ∧
      shiftedHomogeneousLift C.inverse.filtration n 0
          (associatedClass C.inverse.filtration n a hna) ≠ 0 ∧
      sourceNumerator C
          (shiftedHomogeneousLift C.inverse.filtration n 0
            (associatedClass C.inverse.filtration n a hna)) ≠ 0 ∧
      sourceLocalizationMap C
          (sourceNumerator C
            (shiftedHomogeneousLift C.inverse.filtration n 0
              (associatedClass C.inverse.filtration n a hna))) =
        SymbolFractionReesMap.map C
          (shiftedHomogeneousLift C.inverse.filtration n 0
            (associatedClass C.inverse.filtration n a hna))
  exact ⟨hq, hp, hlocalized,
    sourceLocalizationMap_commutes C
      (shiftedHomogeneousLift C.inverse.filtration n 0
        (associatedClass C.inverse.filtration n a hna))⟩

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.exists_minimal_layer_selected_source_survival_kernel
