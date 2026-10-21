module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Data.Matrix.Basic
public import SymplecticStafford.Source.LocalizedDivisorAssembly
public import SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

@[expose] public section

/- Independent trust-disabled consumers for localized-to-original assembly.
   The first uses an arbitrary matrix unit and retains the ordered `f * d`
   term.  The second builds a complete divisor-indexed producer over ℚ and
   checks the existing same-divisor endpoint consumer. -/
namespace SymplecticStaffordTest.LocalizedDivisorAssemblyOracle

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolRightLocalization
open SymplecticStafford.Filtered.FullSymbolPolynomialCalibration
open SymplecticStafford.Source

noncomputable section

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
    ∃ (r t : M), (1 : M) = (u : M) * r +
      (f * (u : M)) * t := by
  let d : M := (u : M)
  let di : M := ((u⁻¹ : Mˣ) : M)
  let C : LocalizedDivisorCertificate d f :=
    { chart := matrixIdentityData
      q₁ := matrixIdentityData.numerator di -
        matrixIdentityData.numerator di * matrixIdentityData.numerator f *
          matrixIdentityData.numerator d
      q₂ := matrixIdentityData.numerator (1 : M)
      localized_identity := by
        have hdi : matrixIdentityData.numerator d *
            matrixIdentityData.numerator di = 1 := by
          dsimp [d, di]
          rw [← map_mul, u.mul_inv, map_one]
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
      denominator_right_inverse := by
        intro s
        have hs' : (s : M) ∈ Submonoid.powers (1 : M) := s.property
        rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
        refine ⟨1, ?_⟩
        simpa using hn.symm }
  exact ⟨C.toAssemblyWitness.right₁, C.toAssemblyWitness.right₂,
    C.toAssemblyWitness.identity⟩

noncomputable def rationalIdentityData : FullSymbolRightLocalization.Data ℚ where
  denominators := Submonoid.powers (1 : ℚ)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

noncomputable def rationalProducer :
    DivisorIndexedLocalizedProducer (R := ℚ) where
  chart := fun _ _ => rationalIdentityData
  source := fun _ _ => 0
  q₁ := fun d _ => rationalIdentityData.numerator d⁻¹
  q₂ := fun _ _ => 0
  localized_identity := by
    intro d hd
    have hd' : d ≠ 0 := hd
    rw [mul_zero, add_zero, ← map_mul, mul_inv_cancel₀ hd', map_one]
  denominator_right_inverse := by
    intro d hd s
    have hs' : (s : ℚ) ∈ Submonoid.powers (1 : ℚ) := s.property
    rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
    refine ⟨1, ?_⟩
    simpa using hn.symm

example : SymplecticStafford.SameDivisorS1 (R := ℚ) :=
  rationalProducer.sameDivisor

end
end SymplecticStaffordTest.LocalizedDivisorAssemblyOracle

#print axioms
  SymplecticStafford.Source.LocalizedDivisorCertificate.toAssemblyWitness
#print axioms
  SymplecticStafford.Source.DivisorIndexedLocalizedProducer.sameDivisor
