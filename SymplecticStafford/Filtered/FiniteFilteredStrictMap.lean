import Mathlib.Tactic
import SymplecticStafford.Filtered.FiniteFilteredLengthFormula
import SymplecticStafford.Filtered.StrictFiniteGradedChain

/-!
# A bounded strict filtered-map witness

This is the next paper-independent interface after the finite filtered length
formula.  For a proper actual submodule `A`, the intersection filtration on
`A` has an associated-layer map into the ambient filtration which is
injective but fails to be surjective at one finite layer.  The same witness
retains the exact finite length formulas for the ambient and induced
filtrations.

The result is deliberately finite and literal: it does not construct the
original Rees algebra, a homogeneous localization, or the comparison between
localized graded length and the paper's filtered module.  Those missing
hypotheses are precisely what a later M05 producer must consume.
-/

namespace SymplecticStafford.Filtered

universe u v

noncomputable section

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

namespace FiniteFilteredStrictMap

open StrictFiniteGradedChain

variable (F : FiniteFilteredModule (R := R) (M := M))
variable (A : Submodule R M)

/- The map is kept as an actual quotient-level linear map, rather than an
   abstract graded proxy.  The two length equations in the witness are the
   exact finite formulas from `FiniteFilteredLengthFormula`. -/
structure Witness (hA : A < (⊤ : Submodule R M)) where
  layer : Fin F.height
  injective : Function.Injective (layerMap F A layer)
  not_surjective : ¬ Function.Surjective (layerMap F A layer)
  missingClass : filteredLayerQuotient F layer
  missingClass_not_in_range :
    ∀ q : filteredLayerQuotient (inducedFiltration F A) layer,
      layerMap F A layer q ≠ missingClass
  missingClass_ne_zero : missingClass ≠ 0
  ambient_length :
    Module.length R M =
      ∑ k ∈ Finset.Ico 0 F.height, F.layerLength k
  induced_length :
    Module.length R A =
      ∑ k ∈ Finset.Ico 0 F.height,
        (inducedFiltration F A).layerLength k

/-- Every proper actual filtered submodule exposes a finite strict layer. -/
theorem exists_witness (hA : A < (⊤ : Submodule R M)) :
    Nonempty (Witness F A hA) := by
  rcases exists_layerMap_not_surjective_of_lt_top F A hA with ⟨k, hk⟩
  classical
  have hmissing : ∃ q : filteredLayerQuotient F k,
      ∀ p : filteredLayerQuotient (inducedFiltration F A) k,
        layerMap F A k p ≠ q := by
    by_contra hcover
    push_neg at hcover
    exact hk hcover
  rcases hmissing with ⟨q, hq⟩
  have hq_ne_zero : q ≠ 0 := by
    intro hq_zero
    apply hq 0
    simpa [hq_zero]
  refine ⟨{
    layer := k
    injective := layerMap_injective F A k
    not_surjective := hk
    missingClass := q
    missingClass_not_in_range := hq
    missingClass_ne_zero := hq_ne_zero
    ambient_length := FiniteFilteredModule.length_eq_sum_layerLength F
    induced_length :=
      FiniteFilteredModule.length_eq_sum_layerLength
        (inducedFiltration F A) }⟩

theorem exists_strict_layer (hA : A < (⊤ : Submodule R M)) :
    ∃ k : Fin F.height,
      Function.Injective (layerMap F A k) ∧
        ¬ Function.Surjective (layerMap F A k) := by
  rcases exists_witness F A hA with ⟨W⟩
  exact ⟨W.layer, W.injective, W.not_surjective⟩

end FiniteFilteredStrictMap

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.FiniteFilteredStrictMap.exists_witness
#print axioms
  SymplecticStafford.Filtered.FiniteFilteredStrictMap.exists_strict_layer
