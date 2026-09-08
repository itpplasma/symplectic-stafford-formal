import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Field.Rat
import SymplecticStafford.Package.Opposite

/-!
# Independent opposite-ring package oracle

The rational field has explicit right and left certificates using inverses.
The examples exercise both handed transport theorems without asserting the
unproved symplectic producer.
-/

namespace SymplecticStaffordTest.PackageOpposite

open SymplecticStafford

def rationalRight : SameDivisorS1 (R := ℚ) := by
  intro d hd
  refine ⟨0, d⁻¹, 0, ?_⟩
  simp [hd]

def rationalLeft : LeftSameDivisorS1 (R := ℚ) := by
  intro d hd
  refine ⟨0, d⁻¹, 0, ?_⟩
  simp [hd]

example : SameDivisorS1 (R := ℚᵐᵒᵖ) :=
  leftSameDivisorS1_opposite rationalLeft

example : LeftSameDivisorS1 (R := ℚᵐᵒᵖ) :=
  rightSameDivisorS1_opposite rationalRight

example : LeftSameDivisorS1 (R := ℚ) ↔
    SameDivisorS1 (R := ℚᵐᵒᵖ) :=
  leftSameDivisorS1_iff_rightSameDivisorS1_opposite

end SymplecticStaffordTest.PackageOpposite

#print axioms SymplecticStaffordTest.PackageOpposite.rationalRight
#print axioms SymplecticStaffordTest.PackageOpposite.rationalLeft
