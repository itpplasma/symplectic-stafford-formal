import AlgebraicAnalysis.Ore.RightLocalization
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Full-symbol localization with original right denominators

The paper's source assembly is right-sided.  Mathlib's Ore localization is
left-oriented, so the algebraic-analysis package implements the right-sided
construction by passing to the opposite ring.  This file gives the filtered
lane a precise certificate for that construction.

`RightData.denominators` is an arbitrary saturated submonoid of the original
ring, not the powers of a selected lift.  Its `ore` field is an actual Ore
structure on the opposite submonoid.  The exported results provide the
injective original-ring map and the exact right-denominator clearing theorem
in the original localization.  The certificate is therefore suitable for a
future characteristic-symbol producer, while its Ore and regularity fields
remain explicit obligations of that producer.  No completion, principal
power shortcut, or Noetherianity claim is made.
-/

namespace SymplecticStafford.Filtered

universe u

namespace FullSymbolRightLocalization

variable {R : Type u} [Ring R]

structure Data (R : Type u) [Ring R] where
  denominators : Submonoid R
  /-- Right regularity of every original-ring denominator. -/
  regular : denominators ≤ nonZeroDivisorsRight R
  /-- The opposite denominator set has the genuine Ore equations. -/
  ore : OreLocalization.OreSet
    (AlgebraicAnalysis.OreRightLocalization.oppositeSubmonoid denominators)

namespace Data

open AlgebraicAnalysis.OreRightLocalization

variable (C : Data R)

abbrev Localization : Type u :=
  @RightOreLocalization R (inferInstance : Ring R) C.denominators C.ore

def numerator : R →+* C.Localization :=
  @rightNumeratorRingHom R (inferInstance : Ring R) C.denominators C.ore

theorem regular_opposite :
    oppositeSubmonoid C.denominators ≤ nonZeroDivisorsLeft Rᵐᵒᵖ := by
  intro s hs y hsy
  apply MulOpposite.unop_injective
  apply C.regular hs
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_zero] using
    congrArg MulOpposite.unop hsy

theorem numerator_injective : Function.Injective C.numerator := by
  intro a b hab
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  apply MulOpposite.op_injective
  apply OreLocalization.numeratorHom_inj C.regular_opposite
  exact congrArg MulOpposite.unop hab

/- Every right-localized element has one denominator in the original
  submonoid which clears it on the RIGHT. -/
theorem right_clear (q : C.Localization) :
    ∃ a s : R, s ∈ C.denominators ∧ IsUnit (C.numerator s) ∧
      q * C.numerator s = C.numerator a := by
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  exact rightOre_clear q

theorem denominator_unit (s : C.denominators) :
    IsUnit (C.numerator (s : R)) := by
  letI : OreLocalization.OreSet (oppositeSubmonoid C.denominators) := C.ore
  exact isUnit_op.mpr (OreLocalization.numerator_isUnit
    (R := Rᵐᵒᵖ) (S := oppositeSubmonoid C.denominators)
      (⟨MulOpposite.op (s : R), s.property⟩ : oppositeSubmonoid C.denominators))

end Data

end FullSymbolRightLocalization

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.regular_opposite
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.numerator_injective
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.right_clear
#print axioms SymplecticStafford.Filtered.FullSymbolRightLocalization.Data.denominator_unit
