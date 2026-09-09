import SymplecticStafford.Filtered.M01StructuralClass
import SymplecticStafford.Semantics.Contract

/-!
# A nontrivial semantic false positive for the historical class

`AdmissibleSymplecticClass` stores the geometric hypotheses as bare
propositions.  The zero-ring witness in `M01StructuralBoundary` already
shows that these labels do not imply nontriviality.  This file gives a
nontrivial, domain-valued witness for which the terminal original-ring
same-divisor identity is false: all labels can be declared `True` on `ℤ`, but
the divisor `2` cannot generate `1` together with any second same-divisor
generator because the right side is even.

This is a formal-contract obstruction, not a counterexample to the intended
paper class.  It identifies the exact missing bridge: a producer theorem must
first connect the proposition-valued labels to an actual filtered algebra,
domain/simplicity, and the M02--M04 constructions.  No source, localization,
or phase gate is inferred from the labels alone.
-/

namespace SymplecticStafford.Filtered

open SymplecticStafford

/- Constant dimension data makes both historical B2 fields tautological. -/
def integerCharacteristicDimension :
    CharacteristicDimensionData ℤ where
  charDim := fun _ => 2

def integerOppositeCharacteristicDimension :
    CharacteristicDimensionData ℤᵐᵒᵖ where
  charDim := fun _ => 2

theorem integerCharacteristicDimension_B2 :
    B2 integerCharacteristicDimension := by
  intro M _ _ _
  exact le_rfl

theorem integerOppositeCharacteristicDimension_B2 :
    B2 integerOppositeCharacteristicDimension := by
  intro M _ _ _
  exact le_rfl

/-- Every historical label is inhabited on the nontrivial domain `ℤ`. -/
def integerLabeledAdmissibleClass :
    AdmissibleSymplecticClass ℤ where
  noetherian := True
  simple := True
  infiniteDimensional := True
  nonnegativeSeparatedLocallyFiniteFiltration := True
  associatedGradedCommAffineDomain := True
  associatedGradedDimension := 1
  rightCharacteristicDimension := integerCharacteristicDimension
  leftCharacteristicDimension := integerOppositeCharacteristicDimension
  right_B2 := integerCharacteristicDimension_B2
  left_B2 := integerOppositeCharacteristicDimension_B2

/- The obstruction is the parity of the *actual ordered certificate*; no
   commutation or hidden localization is used. -/
theorem integer_not_originalSameDivisor :
    ¬ OriginalSameDivisor ℤ := by
  intro h
  obtain ⟨F, r, s, hEq⟩ := h (d := (2 : ℤ)) (by norm_num)
  have he : Even ((2 : ℤ) * r + (F * 2) * s) := by
    refine ⟨r + F * s, ?_⟩
    ring
  have h1 : Even (1 : ℤ) := by
    rw [hEq]
    exact he
  rcases h1 with ⟨k, hk⟩
  omega

/-- The current proposition-only semantic contract cannot imply M01--M04's
    original-U source producer, even for a nontrivial integral domain. -/
theorem labels_do_not_imply_originalSameDivisor :
    ¬ (AdmissibleSymplecticClass ℤ → OriginalSameDivisor ℤ) := by
  intro producer
  exact integer_not_originalSameDivisor
    (producer integerLabeledAdmissibleClass)

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.integer_not_originalSameDivisor
#print axioms SymplecticStafford.Filtered.labels_do_not_imply_originalSameDivisor
