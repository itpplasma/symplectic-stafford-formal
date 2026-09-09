import Mathlib.Algebra.Ring.NonZeroDivisors
import SymplecticStafford.Filtered.FullSymbolLocalization

/-!
# An unconditional commutative full-symbol instance

For a commutative ring, the saturated submonoid of regular elements has the
genuine Mathlib Ore structure.  This file packages that instance through the
same `FullSymbolLocalization.Data` API used by the noncommutative filtered
lane.  It is a concrete algebraic construction and a useful calibration
case; it is not a claim that a commutative associated graded ring alone
produces an Ore set in the original noncommutative algebra.
-/

namespace SymplecticStafford.Filtered

open scoped nonZeroDivisors

universe u

namespace CommutativeFullSymbol

variable {R : Type u} [CommRing R]

/-- The saturated regular-element denominator set in a commutative ring. -/
def data : FullSymbolLocalization.Data R where
  denominators := R⁰
  regular := by
    intro s hs
    exact hs.1
  ore := inferInstance

theorem numerator_injective : Function.Injective (data.numerator (R := R)) :=
  data.numerator_injective

theorem exists_fraction (x : (data (R := R)).Localization) :
    ∃ a : R, ∃ s : (data (R := R)).denominators,
      x = (data (R := R)).fraction a s := by
  exact (data (R := R)).exists_fraction x

theorem ore_witness (a : R) (s : (data (R := R)).denominators) :
    ∃ b : R, ∃ t : (data (R := R)).denominators, (t : R) * a = b * (s : R) := by
  exact (data (R := R)).ore_witness a s

end CommutativeFullSymbol

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.CommutativeFullSymbol.numerator_injective
#print axioms SymplecticStafford.Filtered.CommutativeFullSymbol.exists_fraction
#print axioms SymplecticStafford.Filtered.CommutativeFullSymbol.ore_witness
