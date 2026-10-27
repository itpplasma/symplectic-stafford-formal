module

public import SymplecticStafford.Filtered.M01StructuralBoundary

@[expose] public section

/-!
# Independent oracle for the first M01 structural gap

The historical proposition-valued class can be instantiated on `ZMod 1`.
The oracle checks that all labels are accepted while the underlying ring is
subsingleton, so no actual filtered-domain/associated-graded construction can
be extracted from those labels alone.
-/

namespace SymplecticStafford.M01StructuralBoundaryOracle

open SymplecticStafford
open SymplecticStafford.Filtered

example :
    zeroLabeledAdmissibleClass.associatedGradedCommAffineDomain = True := by
  rfl

example :
    zeroLabeledAdmissibleClass.nonnegativeSeparatedLocallyFiniteFiltration =
      True := by
  rfl

example : Subsingleton (ZMod 1) :=
  zeroLabeledAdmissibleClass_subsingleton

example : ¬ Nontrivial (ZMod 1) := by
  intro h
  letI := h
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 1) 1)

example :
    ¬ (AdmissibleSymplecticClass (ZMod 1) → Nontrivial (ZMod 1)) :=
  admissibleClass_labels_do_not_imply_nontrivial

example :
    zeroLabeledAdmissibleClass.associatedGradedCommAffineDomain = True ∧
      ¬ Nontrivial (ZMod 1) :=
  zeroLabeledClass_is_not_actual_nontrivial_model

end SymplecticStafford.M01StructuralBoundaryOracle

#print axioms SymplecticStafford.Filtered.zeroLabeledClass_is_not_actual_nontrivial_model
