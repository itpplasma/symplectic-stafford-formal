module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Induction.LayerSupportObstruction

@[expose] public section

/-!
# Independent oracle for the finite-layer support obstruction

This checks the concrete nonzero support and the impossibility of strict
removal when the support assignment has no source dependence.  It does not
replay a witness stored in a producer structure.
-/

namespace SymplecticStafford.Induction.LayerSupportObstructionOracle

open SymplecticStafford.Induction

example : (sourceIndependentLayerSupport 0).Nonempty := by
  exact scalarLayerSupport_nonempty

example : scalarLayerFiltration.QuotientSupportDimension ≠
    (⊥ : SupportDimension) := by
  exact scalarLayerSupport_dimension_nonbot

example : ∀ f g : ℤ,
    sourceIndependentLayerSupport f = sourceIndependentLayerSupport g := by
  intro f g
  exact sourceIndependentLayerSupport_eq f g

example : ¬ SourceIndependentPencilStrictRemoval := by
  exact not_sourceIndependentPencilStrictRemoval

example :
    (sourceIndependentLayerSupport 0).Nonempty ∧
      scalarLayerFiltration.QuotientSupportDimension ≠
        (⊥ : SupportDimension) ∧
      ¬ SourceIndependentPencilStrictRemoval := by
  exact actual_layer_facts_do_not_supply_strict_removal

end SymplecticStafford.Induction.LayerSupportObstructionOracle

#print axioms SymplecticStafford.Induction.actual_layer_facts_do_not_supply_strict_removal
