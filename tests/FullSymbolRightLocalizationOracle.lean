import Mathlib.Tactic.NormNum
import SymplecticStafford.Filtered.FullSymbolRightLocalization

/- Independent oracle for the right-sided full-symbol interface.  The
  denominator set is an arbitrary submonoid (here all powers of `2`) and the
  right clearing equation is checked in the original ring orientation. -/
namespace SymplecticStaffordTest.FullSymbolRightLocalization

open SymplecticStafford.Filtered

def powersData : FullSymbolRightLocalization.Data ℚ where
  denominators := Submonoid.powers (2 : ℚ)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

example : Function.Injective powersData.numerator :=
  powersData.numerator_injective

example (q : powersData.Localization) :
    ∃ a s : ℚ, s ∈ powersData.denominators ∧
      IsUnit (powersData.numerator s) ∧
        q * powersData.numerator s = powersData.numerator a :=
  powersData.right_clear q

example (s : powersData.denominators) :
    IsUnit (powersData.numerator (s : ℚ)) :=
  powersData.denominator_unit s

end SymplecticStaffordTest.FullSymbolRightLocalization
