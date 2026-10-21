module

public import SymplecticStafford.Filtered.AdmissibleLabelsFalsePositive

@[expose] public section

/-!
# Independent oracle for the semantic false positive

The oracle checks the nontrivial `ℤ` witness and the exact ordered
same-divisor failure.  It does not treat the witness as an intended geometric
model and does not alter any phase or release status.
-/

namespace SymplecticStafford.AdmissibleLabelsFalsePositiveOracle

open SymplecticStafford
open SymplecticStafford.Filtered

example : Nontrivial ℤ := by infer_instance

example : NoZeroDivisors ℤ := by infer_instance

example :
    integerLabeledAdmissibleClass.associatedGradedCommAffineDomain = True := by
  rfl

example :
    ¬ OriginalSameDivisor ℤ :=
  integer_not_originalSameDivisor

example :
    ¬ (AdmissibleSymplecticClass ℤ → OriginalSameDivisor ℤ) :=
  labels_do_not_imply_originalSameDivisor

end SymplecticStafford.AdmissibleLabelsFalsePositiveOracle

#print axioms SymplecticStafford.Filtered.integer_not_originalSameDivisor
#print axioms SymplecticStafford.Filtered.labels_do_not_imply_originalSameDivisor
