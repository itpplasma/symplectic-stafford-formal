module

public import SymplecticStafford.Filtered.FullSymbolActualOreFinite
public import SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

@[expose] public section

/- Independent behavioral consumer: finite original-ring values are cleared
   in the actual polynomial Ore chart, with the multiplication order retained. -/
namespace SymplecticStaffordTest.FullSymbolActualOreFinite

open Polynomial
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolActualOreFinite
open SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

noncomputable section

example : ∃ s : powersLocalization.denominators, ∀ x ∈
    ([X ^ 2, X ^ 4] : List (ℚ[X])), ∃ a : ℚ[X],
      powersLocalization.numerator x *
          powersLocalization.numerator (s : ℚ[X]) =
        powersLocalization.numerator a := by
  exact finite_source_values_common_right_clear powersLocalization [X ^ 2, X ^ 4]

end
end SymplecticStaffordTest.FullSymbolActualOreFinite

#print axioms
  SymplecticStafford.Filtered.FullSymbolActualOreFinite.finite_source_values_common_right_clear
