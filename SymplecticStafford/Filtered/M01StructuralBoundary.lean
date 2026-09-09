import SymplecticStafford.Filtered.CentralField
import SymplecticStafford.Semantics.Contract
import Mathlib.Data.ZMod.Basic

/-!
# First missing M01 structural bridge

`AdmissibleSymplecticClass` currently stores the filtered-algebra hypotheses as
uninterpreted propositions.  Thus those labels do not provide an actual
filtration, a degree-zero scalar embedding, or a nontrivial/domain structure
from which an associated graded ring could be built.  The zero ring is a
minimal counterexample: every label (including both historical B2 fields) can
be inhabited, while the ring has no nonzero element.

This is an obstruction, not a replacement class.  A future structural M01
record must expose actual filtered algebra data and its nontrivial/domain
properties before `Spec (gr U)` support can be constructed.
-/

namespace SymplecticStafford.Filtered

open SymplecticStafford

/-- All proposition labels in the historical semantic class can be inhabited
    on the zero ring. -/
def zeroLabeledAdmissibleClass :
    AdmissibleSymplecticClass (ZMod 1) := by
  let Dr : CharacteristicDimensionData (ZMod 1) :=
    { charDim := fun _ => 2 }
  let Dl : CharacteristicDimensionData (ZMod 1)ᵐᵒᵖ :=
    { charDim := fun _ => 2 }
  refine
    { noetherian := True
      simple := True
      infiniteDimensional := True
      nonnegativeSeparatedLocallyFiniteFiltration := True
      associatedGradedCommAffineDomain := True
      associatedGradedDimension := 0
      rightCharacteristicDimension := Dr
      leftCharacteristicDimension := Dl
      right_B2 := ?_
      left_B2 := ?_ }
  · intro M _ _ _
    change 2 ≤ 2
    decide
  · intro M _ _ _
    change 2 ≤ 2
    decide

theorem zeroLabeledAdmissibleClass_subsingleton :
    Subsingleton (ZMod 1) := by
  infer_instance

/- The labels alone cannot entail even the basic nontriviality needed by an
   actual filtered algebra over a field. -/
theorem admissibleClass_labels_do_not_imply_nontrivial :
    ¬ (AdmissibleSymplecticClass (ZMod 1) → Nontrivial (ZMod 1)) := by
  intro h
  letI : Nontrivial (ZMod 1) := h zeroLabeledAdmissibleClass
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

theorem zeroLabeledClass_is_not_actual_nontrivial_model :
    zeroLabeledAdmissibleClass.associatedGradedCommAffineDomain = True ∧
      ¬ Nontrivial (ZMod 1) := by
  constructor
  · rfl
  · intro h
    letI := h
    exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.admissibleClass_labels_do_not_imply_nontrivial
#print axioms SymplecticStafford.Filtered.zeroLabeledClass_is_not_actual_nontrivial_model
