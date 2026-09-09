import SymplecticStafford.Filtered.FullSymbolFilteredChart
import SymplecticStafford.Filtered.FullSymbolOre
import Mathlib.Algebra.Polynomial.Derivative

/-!
# An actual algebraic full-symbol calibration

This is a concrete filtered algebra, not a formal chart label: the source is
`ℚ[X]`, the denominator is the nonzero element `X`, and the chart is the
genuine Mathlib Ore localization at its powers.  The finite chart theorem is
therefore instantiated with an actual algebraic numerator map.  This example
is deliberately commutative; it calibrates the passage and does not weaken
the noncommutative `xp` obstruction.
-/

namespace SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

open Polynomial

noncomputable section

def sourceFiltration : FiltrationData ℚ[X] where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by intro i j a b ha hb; simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij a ha; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def powersLocalization : FullSymbolRightLocalization.Data ℚ[X] where
  denominators := Submonoid.powers X
  regular := by
    intro s hs a hzero
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    exact (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero n Polynomial.X_ne_zero)
  ore := inferInstance

def chartFiltration : FiltrationData powersLocalization.Localization where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by intro i j a b ha hb; simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij a ha; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def chart : FullSymbolFilteredChart.Data ℚ[X] where
  localization := powersLocalization
  sourceFiltration := sourceFiltration
  chartFiltration := chartFiltration
  map_filtered := by
    intro n a ha
    simp [HasDegreeAtMost, chartFiltration]

def symbolLift : ReesTerm sourceFiltration :=
  { degree := 1
    value := X
    bounded := by simp [HasDegreeAtMost, sourceFiltration] }

theorem symbolLift_nonzero :
    ReesQuotient.mk symbolLift ≠ ReesQuotient.zero := by
  intro h
  have hv := congrArg ReesQuotient.value h
  change (X : ℚ[X]) = 0 at hv
  exact Polynomial.X_ne_zero hv

def chart_with_symbol : FullSymbolOreCertificate.Data ℚ[X]
    powersLocalization.Localization where
  localization :=
    { sourceFiltration := sourceFiltration
      chartFiltration := chartFiltration
      map := powersLocalization.numerator
      map_filtered := chart.map_filtered
      denominator := X
      denominator_mem := ⟨1, by simp [HasDegreeAtMost, sourceFiltration]⟩
      right_clearable := by
        intro q
        rcases powersLocalization.right_clear q with ⟨a, s, hs, hu, hq⟩
        rcases (Submonoid.mem_powers_iff s X).mp hs with ⟨n, hn⟩
        refine ⟨n, a, ?_⟩
        rw [← hn] at hq
        simpa [map_pow] using hq
      inverse :=
        ↑((powersLocalization.denominator_unit
          ⟨X, Submonoid.mem_powers X⟩).unit⁻¹)
      denominator_mul_inverse :=
        (powersLocalization.denominator_unit
          ⟨X, Submonoid.mem_powers X⟩).mul_val_inv
      inverse_mul_denominator :=
        (powersLocalization.denominator_unit
          ⟨X, Submonoid.mem_powers X⟩).val_inv_mul
      right_ore := by
        intro a n
        exact ⟨n, a, by simp [mul_comm]⟩ }
  symbolLift := symbolLift
  symbolLift_value := rfl
  symbolLift_nonzero := symbolLift_nonzero
  map_injective := powersLocalization.numerator_injective

theorem finite_symbol_chart_control
    (xs : List (ReesTerm sourceFiltration)) :
    ∃ (N : ℕ) (s : chart.localization.denominators),
      ∀ x ∈ xs, x.degree ≤ N ∧
        HasDegreeAtMost chartFiltration N
          (chart.localization.numerator x.value) ∧
        ∃ a : ℚ[X],
          chart.localization.numerator x.value *
              chart.localization.numerator (s : ℚ[X]) =
            chart.localization.numerator a := by
  exact chart.finite_symbol_chart_control xs

end
end SymplecticStafford.Filtered.FullSymbolPolynomialCalibration

#print axioms
  SymplecticStafford.Filtered.FullSymbolPolynomialCalibration.finite_symbol_chart_control
