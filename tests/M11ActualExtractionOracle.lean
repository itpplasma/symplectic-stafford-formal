import SymplecticStafford.Package.M11ActualExtraction

/-!
Independent trust-disabled oracle for actual M11 extraction.  The unit
divisor over `ℤ` makes the ordered right ideal equal to the whole ring, so its
actual original quotient has empty central support.  The oracle then checks
both direct support extraction and the dimension/defect route.
-/

namespace SymplecticStafford.M11ActualExtractionOracle

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Induction

theorem unitSupportEmpty :
    OriginalCentralCharacteristicSupport
      (twoGeneratedRingRightIdeal (1 : ℤ) 2) = ∅ := by
  apply (originalCentralCharacteristicSupport_empty_iff_one_mem
    (twoGeneratedRingRightIdeal (1 : ℤ) 2)).mpr
  exact ⟨1, 0, by norm_num⟩

noncomputable example : OriginalCofactors (1 : ℤ) 2 :=
  originalCofactors_of_empty_centralCharacteristicSupport 1 2 unitSupportEmpty

def unitDefect : OriginalSupportDimensionDefect (1 : ℤ) 2 where
  dimension := ⊥
  defect := -1
  defect_eq_dimension := rfl
  dimension_bot_iff_support_empty := by
    constructor
    · intro _
      exact unitSupportEmpty
    · intro _
      rfl

noncomputable example : OriginalCofactors (1 : ℤ) 2 :=
  originalCofactors_of_actual_support_defect unitDefect (by rfl)

end SymplecticStafford.M11ActualExtractionOracle

#print axioms SymplecticStafford.originalCofactors_of_empty_centralCharacteristicSupport
#print axioms SymplecticStafford.originalCofactors_of_actual_support_defect
