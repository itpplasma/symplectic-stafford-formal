import SymplecticStafford.Semantics.RightIdealBridge
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! Independent M01 checks for the semiring-to-ring right-ideal bridge. -/

namespace SymplecticStafford.RightIdealBridgeOracle

open SymplecticStafford

section Integers

example :
    twoGeneratedRightIdealRingBridge (2 : ℤ) 3 =
      twoGeneratedRingRightIdeal (2 : ℤ) 3 :=
  twoGeneratedRightIdealRingBridge_eq 2 3

example : (8 : ℤ) ∈ twoGeneratedRightIdealRingBridge 2 3 := by
  rw [twoGeneratedRightIdealRingBridge_mem_iff_coefficients]
  exact ⟨4, 0, by norm_num⟩

example :
    Quotient.mk
        (rightIdealSetoid (twoGeneratedRightIdealRingBridge (2 : ℤ) 3)) 8 =
      (0 : TwoGeneratedRightQuotient (2 : ℤ) 3) ↔
    ∃ r s : ℤ, (8 : ℤ) = 2 * r + (3 * 2) * s :=
  twoGeneratedRightQuotient_mk_eq_zero_iff_coefficients 2 3 8

example :
    quotientRightAction (twoGeneratedRightIdealRingBridge (2 : ℤ) 3)
        (Quotient.mk
          (rightIdealSetoid (twoGeneratedRightIdealRingBridge (2 : ℤ) 3)) 8) 5 =
      quotientRightAction (twoGeneratedRightIdealRingBridge (2 : ℤ) 3)
        (Quotient.mk
          (rightIdealSetoid (twoGeneratedRightIdealRingBridge (2 : ℤ) 3)) 0) 5 := by
  apply twoGeneratedRightQuotient_action_respects
  change (8 : ℤ) - 0 ∈ twoGeneratedRightIdeal 2 3
  change (8 : ℤ) ∈ twoGeneratedRightIdeal 2 3
  exact ⟨4, 0, by norm_num⟩

example :
    QuotientIsZero (twoGeneratedRightIdealRingBridge (1 : ℤ) 3) := by
  apply (twoGeneratedRightQuotient_isZero_iff_certificate (1 : ℤ) 3).mpr
  exact ⟨1, 0, by norm_num⟩

end Integers

section Rationals

example :
    (1 : ℚ) ∈ twoGeneratedRightIdealRingBridge 2 3 := by
  rw [twoGeneratedRightIdealRingBridge_mem_iff_coefficients]
  exact ⟨(1 / 2 : ℚ), 0, by norm_num⟩

example :
    QuotientIsZero (twoGeneratedRightIdealRingBridge (2 : ℚ) 3) := by
  apply (twoGeneratedRightQuotient_isZero_iff_certificate (2 : ℚ) 3).mpr
  exact ⟨(1 / 2 : ℚ), 0, by norm_num⟩

example (q : TwoGeneratedRightQuotient (2 : ℚ) 3) :
    quotientRightAction (twoGeneratedRightIdealRingBridge (2 : ℚ) 3)
        (quotientRightAction (twoGeneratedRightIdealRingBridge (2 : ℚ) 3) q 2) 3 =
      quotientRightAction (twoGeneratedRightIdealRingBridge (2 : ℚ) 3) q (2 * 3) :=
  twoGeneratedRightQuotient_action_mul 2 3 q 2 3

end Rationals

end SymplecticStafford.RightIdealBridgeOracle
