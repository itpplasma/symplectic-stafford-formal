import SymplecticStafford.Filtered.ActualClassSupport

/-!
# Independent oracle for the actual filtered-class support bridge

The one-step filtration of `ℤ` has a nonzero quotient class.  The class map
in this oracle is the identity on that actual quotient, so the support and
kernel conclusions exercise quotient representatives rather than a supplied
whole-module map.  The defect witness also checks the non-bottom integer
encoding against the same nonempty spectrum support.
-/

namespace SymplecticStafford.ActualClassSupportOracle

open SymplecticStafford
open SymplecticStafford.Filtered

def integerOneStep : FiniteFilteredModule (R := ℤ) (M := ℤ) where
  height := 1
  carrier := fun n => if n = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n
    cases n with
    | zero => simp
    | succ n => simp
  separated := by simp

def integerLayer : Fin integerOneStep.height := ⟨0, by decide⟩

abbrev integerQuotient := filteredLayerQuotient integerOneStep integerLayer

def integerClassMap : ActualFilteredClassMap integerOneStep ℤ integerQuotient where
  layer := integerLayer
  classMap := AddMonoidHom.id integerQuotient
  surjective := Function.surjective_id
  classMap_eq_zero_iff := by
    intro q
    change q = 0 ↔ q = 0
    rfl

def oneClass : integerOneStep.carrier integerLayer.1 :=
  ⟨1, by simp [integerOneStep, integerLayer]⟩

example : (oneClass : ℤ) ∉ integerOneStep.carrier (integerLayer.1 + 1) := by
  simp [integerOneStep, integerLayer, oneClass]

example :
    (SpecCharacteristicSupport ℤ integerQuotient).Nonempty := by
  exact integerClassMap.specSupport_nonempty_of_not_mem_next oneClass
    (by simp [integerOneStep, integerLayer, oneClass])

example :
    SpecCharacteristicSupport ℤ integerQuotient = ∅ ↔
      ∀ x : integerOneStep.carrier integerLayer.1,
        (x : ℤ) ∈ integerOneStep.carrier (integerLayer.1 + 1) := by
  exact integerClassMap.specSupport_empty_iff_layer_killed

def integerDefect :
    SpecSupportDimensionDefect integerOneStep integerClassMap where
  dimension := (0 : SupportDimension)
  defect := 0
  defect_eq_dimension := rfl
  dimension_bot_iff_support_empty := by
    constructor
    · intro h
      exact False.elim ((WithBot.coe_ne_bot :
        (0 : SupportDimension) ≠ ⊥) h)
    · intro hs
      exact False.elim ((Set.not_nonempty_iff_eq_empty.mpr hs)
        (integerClassMap.specSupport_nonempty_of_not_mem_next oneClass
          (by simp [integerOneStep, integerLayer, oneClass])))

example : integerDefect.defect > -1 := by
  norm_num [integerDefect]

example : integerDefect.defect ≤ -1 ↔
    ∀ x : integerOneStep.carrier integerLayer.1,
      (x : ℤ) ∈ integerOneStep.carrier (integerLayer.1 + 1) := by
  exact integerDefect.defect_le_neg_one_iff_layer_killed

end SymplecticStafford.ActualClassSupportOracle

#print axioms SymplecticStafford.ActualClassSupportOracle.integerClassMap
#print axioms SymplecticStafford.ActualClassSupportOracle.integerDefect
