import SymplecticStafford.Filtered.FullSymbolOriginalCofactor
import SymplecticStafford.Filtered.FullSymbolPolynomialCalibration
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

/- Independent behavioral consumer: a localized two-generator identity is
   recombined after one common RIGHT denominator, preserving the
   noncommutative factor order in the original ring. -/
namespace SymplecticStaffordTest.FullSymbolOriginalCofactorOracle

open Polynomial
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolOriginalCofactor
open SymplecticStafford.Filtered.FullSymbolPolynomialCalibration
open SymplecticStafford.Filtered.FullSymbolRightLocalization

open scoped Matrix

noncomputable section

example :
    ∃ (s r t : ℚ[X]), s ∈ powersLocalization.denominators ∧
      s = (1 : ℚ[X]) * r + (X * (1 : ℚ[X])) * t := by
  let q₁ : powersLocalization.Localization :=
    powersLocalization.numerator (1 : ℚ[X])
  let q₂ : powersLocalization.Localization := 0
  have hidentity : powersLocalization.numerator (1 : ℚ[X]) * q₁ +
      (powersLocalization.numerator X * powersLocalization.numerator
        (1 : ℚ[X])) * q₂ = 1 := by
    simp [q₁, q₂]
  exact localized_two_generator_to_original powersLocalization
    (1 : ℚ[X]) X q₁ q₂ hidentity

/- A noncommutative consumer: the identity is built in a matrix ring from an
   arbitrary unit `u`, with the ordered correction `u⁻¹ * f * u`. -/
abbrev M := Matrix (Fin 2) (Fin 2) ℚ

noncomputable def matrixIdentityData : FullSymbolRightLocalization.Data M where
  denominators := Submonoid.powers (1 : M)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore :=
    { ore_right_cancel := by
        intro r₁ r₂ s h
        have hs' : (s : Mᵐᵒᵖ).unop ∈ Submonoid.powers (1 : M) := s.property
        rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
        have hs1 : (s : Mᵐᵒᵖ) = 1 := by
          apply MulOpposite.op_injective
          simpa using hn.symm
        exact ⟨1, by simpa [hs1] using h⟩
      oreNum := fun r s => r
      oreDenom := fun r s => 1
      ore_eq := by
        intro r s
        have hs' : (s : Mᵐᵒᵖ).unop ∈ Submonoid.powers (1 : M) := s.property
        rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
        have hs1 : (s : Mᵐᵒᵖ) = 1 := by
          apply MulOpposite.op_injective
          simpa using hn.symm
        simpa [hs1] }

example (u : Mˣ) (f : M) :
    ∃ (s r t : M), s ∈ matrixIdentityData.denominators ∧
      s = (u : M) * r + (f * (u : M)) * t := by
  let d : M := (u : M)
  let di : M := ((u⁻¹ : Mˣ) : M)
  let q₂ : matrixIdentityData.Localization :=
    matrixIdentityData.numerator (1 : M)
  let q₁ : matrixIdentityData.Localization :=
    matrixIdentityData.numerator di -
      matrixIdentityData.numerator di * matrixIdentityData.numerator f *
        matrixIdentityData.numerator d
  have hdi : matrixIdentityData.numerator d *
      matrixIdentityData.numerator di = 1 := by
    dsimp [d, di]
    rw [← map_mul, u.mul_inv, map_one]
  have hidentity : matrixIdentityData.numerator d * q₁ +
      (matrixIdentityData.numerator f * matrixIdentityData.numerator d) * q₂ = 1 := by
    dsimp [q₁, q₂]
    calc
      matrixIdentityData.numerator d *
          (matrixIdentityData.numerator di -
            matrixIdentityData.numerator di * matrixIdentityData.numerator f *
              matrixIdentityData.numerator d) +
          (matrixIdentityData.numerator f * matrixIdentityData.numerator d) *
            matrixIdentityData.numerator (1 : M) =
          matrixIdentityData.numerator d * matrixIdentityData.numerator di -
            (matrixIdentityData.numerator d * matrixIdentityData.numerator di) *
              (matrixIdentityData.numerator f * matrixIdentityData.numerator d) +
            matrixIdentityData.numerator f * matrixIdentityData.numerator d := by
              simp only [map_one, mul_one, mul_sub, mul_assoc]
      _ = 1 := by rw [hdi, one_mul, sub_add_cancel]
  exact localized_two_generator_to_original matrixIdentityData d f q₁ q₂ hidentity

end
end SymplecticStaffordTest.FullSymbolOriginalCofactorOracle

#print axioms
  SymplecticStafford.Filtered.FullSymbolOriginalCofactor.localized_two_generator_to_original
