import Mathlib.Tactic
import SymplecticStafford.Filtered.M01FiniteHomogeneousReesProducer
import SymplecticStafford.Filtered.SymbolFractionReesLocalization

/-!
# A selected-source M01/M05 survival producer

The existing selected-symbol datum already contains an actual right Ore
localization of the original ring, the degree-controlled fraction filtration,
and the Laurent-Rees comparison.  This file consumes that concrete datum at
the precise boundary where M01 meets M05: a nonzero original element yields a
least associated layer, a nonzero homogeneous Rees lift, and a nonzero
numerator in the actual selected source localization.

The theorem does not identify this selected source localization with the
paper's homogeneous localization `G_{Σ_p}` or ordinary localization `G_p`.
That identification, the filtered/module action comparison, and strict or
faithful survival for the paper module remain separate hypotheses.
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

theorem exists_minimal_layer_selected_source_survival
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
    exists_minimal_layer_homogeneous_symbol C.inverse.filtration ha
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
  SymplecticStafford.Filtered.exists_minimal_layer_selected_source_survival
