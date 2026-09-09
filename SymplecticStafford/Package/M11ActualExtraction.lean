import SymplecticStafford.Filtered.OriginalCentralSupport
import SymplecticStafford.Package.TerminalBoundary

/-!
# Actual M11 extraction from original quotient support

The terminal step does not need a separately supplied `zero_extraction` map
once the defect is tied to the actual central support of the original
two-generator quotient.  Empty support is equivalent to a zero original
quotient, hence to membership of `1` in the literal ordered right ideal; the
cofactors are then extracted without changing any factor order.

The dimension/support linkage remains explicit because a bare integer defect
does not determine a support.  This is the exact data needed at the endpoint,
not a pre-built cofactor or same-divisor witness.
-/

namespace SymplecticStafford

universe u

open SymplecticStafford.Filtered
open SymplecticStafford.Induction

section

variable {R : Type u} [Ring R]

/-- Literal cofactors obtained from the genuine central support of the
    original quotient by the ordered two-generator right ideal. -/
noncomputable def originalCofactors_of_empty_centralCharacteristicSupport
    (d f : R)
    (h : OriginalCentralCharacteristicSupport
      (twoGeneratedRingRightIdeal d f) = ∅) :
    OriginalCofactors d f := by
  have hm : (1 : R) ∈ twoGeneratedRingRightIdeal d f :=
    (originalCentralCharacteristicSupport_empty_iff_one_mem
      (twoGeneratedRingRightIdeal d f)).mp h
  let r : R := Classical.choose hm
  have hm' : ∃ s : R, (1 : R) = d * r + (f * d) * s := by
    simpa [r] using Classical.choose_spec hm
  let s : R := Classical.choose hm'
  exact ⟨r, s, Classical.choose_spec hm'⟩

/-- An endpoint defect object whose dimension is tied to the actual original
    quotient support.  The support equivalence is explicit rather than
    hidden in an integer-valued predicate. -/
structure OriginalSupportDimensionDefect (d f : R) where
  dimension : SupportDimension
  defect : Int
  defect_eq_dimension : defect = supportDimensionDefect dimension
  dimension_bot_iff_support_empty :
    dimension = (⊥ : SupportDimension) ↔
      OriginalCentralCharacteristicSupport
        (twoGeneratedRingRightIdeal d f) = ∅

theorem OriginalSupportDimensionDefect.bot_of_defect_le_neg_one
    {d f : R} (D : OriginalSupportDimensionDefect d f)
    (hdefect : D.defect ≤ -1) :
    D.dimension = (⊥ : SupportDimension) := by
  rw [D.defect_eq_dimension, supportDimensionDefect_le_neg_one_iff] at hdefect
  exact hdefect

/-- Genuine terminal original-U extraction from an actual quotient support
    defect.  No abstract `TerminationInterface.zero_extraction` is used. -/
noncomputable def originalCofactors_of_actual_support_defect
    {d f : R} (D : OriginalSupportDimensionDefect d f)
    (hdefect : D.defect ≤ -1) :
    OriginalCofactors d f := by
  have hbot : D.dimension = (⊥ : SupportDimension) :=
    D.bot_of_defect_le_neg_one hdefect
  have hempty : OriginalCentralCharacteristicSupport
      (twoGeneratedRingRightIdeal d f) = ∅ :=
    D.dimension_bot_iff_support_empty.mp hbot
  exact originalCofactors_of_empty_centralCharacteristicSupport d f hempty

end

end SymplecticStafford

#print axioms
  SymplecticStafford.originalCofactors_of_empty_centralCharacteristicSupport
#print axioms SymplecticStafford.originalCofactors_of_actual_support_defect
