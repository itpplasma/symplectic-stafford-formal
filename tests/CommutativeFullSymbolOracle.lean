import SymplecticStafford.Filtered.CommutativeFullSymbol

/- Independent calibration of full-symbol fractions over `ℤ`, using the
   saturated regular-element submonoid rather than powers of one element. -/
namespace SymplecticStaffordTest.CommutativeFullSymbol

open SymplecticStafford.Filtered
open scoped nonZeroDivisors

example : Function.Injective
    (CommutativeFullSymbol.data.numerator (R := ℤ)) :=
  CommutativeFullSymbol.numerator_injective

example (x : (CommutativeFullSymbol.data (R := ℤ)).Localization) :
    ∃ a : ℤ, ∃ s : (CommutativeFullSymbol.data (R := ℤ)).denominators,
      x = (CommutativeFullSymbol.data (R := ℤ)).fraction a s :=
  CommutativeFullSymbol.exists_fraction x

example (a : ℤ) (s : (CommutativeFullSymbol.data (R := ℤ)).denominators) :
    ∃ b : ℤ, ∃ t : (CommutativeFullSymbol.data (R := ℤ)).denominators,
      (t : ℤ) * a = b * (s : ℤ) :=
  CommutativeFullSymbol.ore_witness a s

end SymplecticStaffordTest.CommutativeFullSymbol
