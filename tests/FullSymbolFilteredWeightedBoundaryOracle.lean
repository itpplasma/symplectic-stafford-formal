module

public import SymplecticStafford.Filtered.FullSymbolFilteredWeightedBoundary

@[expose] public section

/- Independent oracle for the filtered/full-symbol M04 boundary. -/
namespace SymplecticStafford.Filtered.FullSymbolFilteredWeightedBoundaryOracle

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolFilteredWeightedBoundary
open scoped Polynomial

example :
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
        ((1 : ℤ[X]) - Polynomial.X)) :=
  finite_chart_control_without_pivot_inverse

end SymplecticStafford.Filtered.FullSymbolFilteredWeightedBoundaryOracle
