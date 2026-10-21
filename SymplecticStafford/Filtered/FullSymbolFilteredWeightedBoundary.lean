module

public import SymplecticStafford.Filtered.FullSymbolFilteredChart
public import SymplecticStafford.Filtered.FullSymbolWeightedBoundary

@[expose] public section

/-!
# Filtered-chart boundary for negative weighted pivots

The finite Rees/chart control interface and the genuine right Ore interface
can hold simultaneously without supplying the M04 pivot inverse.  This file
instantiates both interfaces on the polynomial ring, using the actual right
localization at powers of `1`.  The source and chart filtrations are the
exhaustive constant filtrations; this is intentional: it isolates the exact
logical boundary and does not smuggle in a degree or leading-symbol claim.

The element `X` is a bounded Rees term and has a common right denominator in
the supplied chart, but `1 - X` remains noninvertible.  Thus finite Rees
boundedness plus full-symbol/Ore clearing is strictly weaker than the
negative-degree unit criterion needed by weighted Schur elimination.
-/

namespace SymplecticStafford.Filtered

open scoped Polynomial

namespace FullSymbolFilteredWeightedBoundary

/-- The exhaustive filtration used only to expose the interface boundary. -/
def constantFiltrationFor {R : Type} [Semiring R] : FiltrationData R where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; trivial
  exhaustive := by intro x; exact ⟨0, trivial⟩

@[simp] theorem constantFiltrationFor_degreeAtMost
    {R : Type} [Semiring R] (n : ℕ) (x : R) :
    HasDegreeAtMost (constantFiltrationFor (R := R)) n x := by
  trivial

noncomputable def chartData : FullSymbolFilteredChart.Data ℤ[X] where
  localization := FullSymbolWeightedBoundary.identityData
  sourceFiltration := constantFiltrationFor
  chartFiltration := constantFiltrationFor
  map_filtered := by
    intro n a ha
    trivial

noncomputable def xTerm : ReesTerm chartData.sourceFiltration where
  degree := 0
  value := Polynomial.X
  bounded := constantFiltrationFor_degreeAtMost 0 Polynomial.X

theorem xTerm_value : xTerm.value = Polynomial.X := rfl

/-- The raw finite chart certificate exists while the M04 pivot is not a unit. -/
theorem finite_chart_control_without_pivot_inverse :
    (∃ (N : ℕ) (s : chartData.localization.denominators),
      xTerm.degree ≤ N ∧
        HasDegreeAtMost chartData.chartFiltration N
          (chartData.localization.numerator xTerm.value) ∧
        ∃ a : ℤ[X],
          chartData.localization.numerator xTerm.value *
            chartData.localization.numerator (s : ℤ[X]) =
            chartData.localization.numerator a) ∧
      PolynomialNegativeDegree Polynomial.X ∧
      ¬ IsUnit (chartData.localization.numerator
        ((1 : ℤ[X]) - Polynomial.X)) := by
  constructor
  · rcases FullSymbolFilteredChart.Data.finite_symbol_chart_control
      chartData [xTerm] with ⟨N, s, hs⟩
    refine ⟨N, s, ?_⟩
    have hx := hs xTerm (by simp)
    exact hx
  constructor
  · exact polynomial_X_negativeDegree
  · exact FullSymbolWeightedBoundary.numerator_one_sub_X_not_isUnit

end FullSymbolFilteredWeightedBoundary

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FullSymbolFilteredWeightedBoundary.finite_chart_control_without_pivot_inverse
