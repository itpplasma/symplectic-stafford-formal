import SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

/- Independent behavioral consumer for the concrete polynomial calibration.
   The source is an actual polynomial ring and the denominator is the genuine
   power-Ore submonoid at `X`; the oracle checks finite chart passage and the
   nonzero algebraic symbol class. -/
namespace SymplecticStaffordTest.FullSymbolPolynomialCalibration

open Polynomial
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

noncomputable section

def u2 : ReesTerm sourceFiltration :=
  { degree := 2, value := X ^ 2,
    bounded := by simp [HasDegreeAtMost, sourceFiltration] }

def u4 : ReesTerm sourceFiltration :=
  { degree := 4, value := X ^ 4,
    bounded := by simp [HasDegreeAtMost, sourceFiltration] }

example : ReesQuotient.mk symbolLift ≠ ReesQuotient.zero :=
  symbolLift_nonzero

example : Function.Injective powersLocalization.numerator :=
  powersLocalization.numerator_injective

example : ∃ (N : ℕ) (s : powersLocalization.denominators),
    ∀ x ∈ [u2, u4], x.degree ≤ N ∧
      HasDegreeAtMost chartFiltration N
        (powersLocalization.numerator x.value) ∧
      ∃ a : ℚ[X],
        powersLocalization.numerator x.value *
            powersLocalization.numerator (s : ℚ[X]) =
          powersLocalization.numerator a := by
  exact finite_symbol_chart_control [u2, u4]

example : ∃ n : ℕ,
    ∃ a : ℚ[X],
      powersLocalization.numerator (X ^ 2) *
          powersLocalization.numerator (X ^ n) =
        powersLocalization.numerator a := by
  obtain ⟨a, s, hs, hu, hq⟩ := powersLocalization.right_clear
    (powersLocalization.numerator (X ^ 2))
  rcases (Submonoid.mem_powers_iff (s : ℚ[X]) X).mp hs with ⟨n, hn⟩
  refine ⟨n, a, ?_⟩
  rw [← hn] at hq
  simpa [map_pow] using hq

end
end SymplecticStaffordTest.FullSymbolPolynomialCalibration

#print axioms
  SymplecticStafford.Filtered.FullSymbolPolynomialCalibration.finite_symbol_chart_control
