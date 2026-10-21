module

public import tests.SymbolFractionReesOracle
public import SymplecticStafford.Filtered.M05Luna20260912.SourceLocalizationAdapter

@[expose] public section

/-!
Independent behavioral oracle for the M05 adapter. The concrete polynomial
filtration supplies nonzero degree +1 and -1 Laurent-Rees terms whose product
is one. The oracle transports that nontrivial inverse calculation back through
the actual source localization equivalence; it does not merely restate the
equivalence's surjectivity.
-/

namespace SymplecticStaffordTest.M05Luna20260912

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.M05Luna20260912
open SymplecticStaffordTest.SymbolFractionReesOracle

theorem source_preimages_retain_the_x_inverse_calculation :
    (sourceLocalizationEquiv concreteData).symm xTerm *
        (sourceLocalizationEquiv concreteData).symm xInverseTerm =
      1 := by
  apply (sourceLocalizationEquiv concreteData).injective
  simp only [map_mul, (sourceLocalizationEquiv concreteData).apply_symm_apply,
    (sourceLocalizationEquiv concreteData).map_one]
  exact xTerm_mul_inverse

theorem source_preimage_of_x_is_nonzero :
    (sourceLocalizationEquiv concreteData).symm xTerm ≠ 0 := by
  intro hzero
  have htarget := congrArg (sourceLocalizationEquiv concreteData) hzero
  apply xTerm_ne_zero
  simpa using htarget

end

end SymplecticStaffordTest.M05Luna20260912

#print axioms
  SymplecticStaffordTest.M05Luna20260912.source_preimages_retain_the_x_inverse_calculation
#print axioms
  SymplecticStaffordTest.M05Luna20260912.source_preimage_of_x_is_nonzero
