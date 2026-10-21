module

public import SymplecticStafford.Filtered.CharacteristicSupport

@[expose] public section

/-!
# Boundary of the finite-layer support interface

`FiniteFilteredModule.QuotientSupport` is an actual finite-layer module
support, and its nonemptiness/zero boundary is proved from the filtration.
It is not, however, indexed by a source in the original algebra.  This file
records a concrete obstruction: even for a nonzero filtered module, a support
assignment which only remembers this quotient support is source-independent,
so it cannot satisfy the strict support-removal law consumed by the M09/M10
two-call bridge.

The missing implication is therefore not finite scalar avoidance.  One still
needs a source-dependent quotient/localization theorem identifying the support
being removed and proving strictness for the actual affine pencil source.
-/

namespace SymplecticStafford.Induction

open SymplecticStafford.Filtered
open FiniteFilteredModule

/- A concrete nonzero finite filtered module over the original scalar ring
   used by the characteristic-support oracle. -/
def scalarLayerFiltration : FiniteFilteredModule (R := ℤ) (M := ℤ) where
  height := 2
  carrier := fun k => if k = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  separated := by simp

/- This is deliberately source-independent: it is exactly the finite support
   currently available from an actual filtered module quotient. -/
def sourceIndependentLayerSupport (_f : ℤ) : Set (Fin scalarLayerFiltration.height) :=
  scalarLayerFiltration.QuotientSupport

theorem scalarLayerSupport_nonempty :
    (sourceIndependentLayerSupport 0).Nonempty := by
  apply scalarLayerFiltration.quotientSupport_nonempty_of_exists_ne_zero
  exact ⟨7, by norm_num⟩

theorem scalarLayerSupport_dimension_nonbot :
    scalarLayerFiltration.QuotientSupportDimension ≠
      (⊥ : SupportDimension) := by
  exact scalarLayerFiltration.quotientSupportDimension_ne_bot_of_quotient_nonzero
    (x := (7 : ℤ)) (by norm_num)

theorem sourceIndependentLayerSupport_eq (f g : ℤ) :
    sourceIndependentLayerSupport f = sourceIndependentLayerSupport g := rfl

/- The exact shape of the two-call strictness law, with the integer affine
   pencil used only to make the source dependence explicit. -/
def SourceIndependentPencilStrictRemoval : Prop :=
  ∀ old new z : ℤ,
    sourceIndependentLayerSupport (old + new * z) ⊂
      sourceIndependentLayerSupport old

theorem not_sourceIndependentPencilStrictRemoval :
    ¬ SourceIndependentPencilStrictRemoval := by
  intro h
  exact ssubset_irrefl _ (h 0 0 0)

/- The finite filtered-module facts above are compatible with nonzero support,
   but they do not entail the strict source-removal premise required by the
   successor.  This is the first unsupported bridge in the present interface.
-/
theorem actual_layer_facts_do_not_supply_strict_removal :
    (sourceIndependentLayerSupport 0).Nonempty ∧
      scalarLayerFiltration.QuotientSupportDimension ≠
        (⊥ : SupportDimension) ∧
      ¬ SourceIndependentPencilStrictRemoval := by
  exact ⟨scalarLayerSupport_nonempty,
    scalarLayerSupport_dimension_nonbot,
    not_sourceIndependentPencilStrictRemoval⟩

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.scalarLayerSupport_nonempty
#print axioms SymplecticStafford.Induction.not_sourceIndependentPencilStrictRemoval
#print axioms SymplecticStafford.Induction.actual_layer_facts_do_not_supply_strict_removal
