module

public import SymplecticStafford.Filtered.FullSymbolRightLocalization
public import SymplecticStafford.Filtered.WeightedInverseBoundary

@[expose] public section

/-!
# The full-symbol/Ore interface does not imply M04 bounded detection

`FullSymbolRightLocalization.Data` records regular denominators, genuine Ore
equations, injectivity of the original-ring map, and finite right clearing.
It records no degree function, leading-symbol map, or bounded inverse for a
strictly negative correction.  The example below makes that missing bridge
concrete: localizing `ℤ[X]` only at powers of `1` has all of those full-symbol
fields, but `1-X` remains noninvertible in the localization.

Thus M03's current algebraic/Ore data cannot, by itself, derive the bounded
Schur-pivot input required by M04.  The proof uses only the right-clearing
equation and numerator injectivity, with the original noncommutative order
retained in the localization calculation.
-/

namespace SymplecticStafford.Filtered

open scoped Polynomial

namespace FullSymbolWeightedBoundary

noncomputable def identityData :
    FullSymbolRightLocalization.Data ℤ[X] where
  denominators := Submonoid.powers (1 : ℤ[X])
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

theorem numerator_one_sub_X_not_isUnit :
    ¬ IsUnit (identityData.numerator ((1 : ℤ[X]) - Polynomial.X)) := by
  intro hu
  rcases identityData.right_clear
      (↑(hu.unit⁻¹) : identityData.Localization) with ⟨a, s, hs, _, ha⟩
  have hsu : s = 1 := by
    change s ∈ Submonoid.powers (1 : ℤ[X]) at hs
    have hs' : ∃ n : Nat, (1 : ℤ[X]) ^ n = s := by
      simpa only [Submonoid.mem_powers_iff] using hs
    rcases hs' with ⟨n, hn⟩
    simpa using hn.symm
  have hq : identityData.numerator ((1 : ℤ[X]) - Polynomial.X) *
      (↑(hu.unit⁻¹) : identityData.Localization) = 1 := by
    calc
      identityData.numerator ((1 : ℤ[X]) - Polynomial.X) *
          ↑hu.unit⁻¹ = ↑hu.unit * ↑hu.unit⁻¹ := by rw [hu.unit_spec]
      _ = 1 := hu.unit.val_inv
  have hqa : (↑(hu.unit⁻¹) : identityData.Localization) =
      identityData.numerator a := by
    simpa [hsu] using ha
  have hca : identityData.numerator ((1 : ℤ[X]) - Polynomial.X) *
      identityData.numerator a = 1 := by
    rw [← hqa]
    exact hq
  have hca' : identityData.numerator
      (((1 : ℤ[X]) - Polynomial.X) * a) = identityData.numerator 1 := by
    simpa using hca
  have hca'' : ((1 : ℤ[X]) - Polynomial.X) * a = 1 :=
    identityData.numerator_injective hca'
  have hunit : IsUnit ((1 : ℤ[X]) - Polynomial.X) := by
    refine ⟨⟨_, a, hca'', ?_⟩, rfl⟩
    simpa [mul_comm] using hca''
  exact polynomial_one_sub_X_not_isUnit hunit

end FullSymbolWeightedBoundary

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolWeightedBoundary.numerator_one_sub_X_not_isUnit
