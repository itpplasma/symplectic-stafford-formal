module

public import SymplecticStafford.Ordered.CommonColon
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Independent concrete consumers for the M08 common-colon checkpoint.

The integer instance gives a concrete arithmetic oracle for the displayed
ordered products.  The examples instantiate the generic algebraic statements;
they do not supply a geometric support theorem or a universal source.
-/

namespace SymplecticStaffordTest.CommonColon

open SymplecticStafford
open SymplecticStafford.Ordered

example : (4 : ℤ) ∈ commonColon 2 3 := by
  exact ⟨12, by norm_num⟩

example : (4 + 6 : ℤ) ∈ commonColon 2 3 := by
  apply commonColon_add_mem
  · exact ⟨12, by norm_num⟩
  · exact ⟨18, by norm_num⟩

example : (4 * 5 : ℤ) ∈ commonColon 2 3 := by
  apply commonColon_right_mul_mem
  exact ⟨12, by norm_num⟩

example : (5 : ℤ) * 2 * 4 =
    2 * (-7 * 12) + (5 + 7 * 3) * 2 * 4 := by
  apply central_commonColon_identity 2 5 3 4 12 7
  · simp
  · intro x
    noncomm_ring

example : (40 : ℤ) ∈ commonIdeal 2 5 3 := by
  refine ⟨0, 4, ?_, ?_⟩
  · exact ⟨12, by norm_num⟩
  · norm_num

example : (40 : ℤ) ∈
    (twoGeneratedRightIdeal 2 (5 + 7 * 3)).carrier := by
  have hsub := commonIdeal_subset_affineRightIdeal (R := ℤ) 2 5 3 7
      (by intro x; noncomm_ring)
  apply hsub
  refine ⟨0, 4, ?_, ?_⟩
  · exact ⟨12, by norm_num⟩
  · norm_num

end SymplecticStaffordTest.CommonColon
