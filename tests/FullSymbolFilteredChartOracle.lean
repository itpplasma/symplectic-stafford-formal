module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Filtered.FullSymbolFilteredChart

@[expose] public section

/-!
Independent behavioral consumer for the finite full-symbol chart-control
theorem.  The chart is an actual right Ore localization of ℚ at powers of 2;
the common denominator and the filtration degree are obtained by the theorem,
while the final example checks the expected concrete right-clearing witness.
-/

namespace SymplecticStaffordTest.FullSymbolFilteredChart

open SymplecticStafford.Filtered

def rationalFiltration : FiltrationData ℚ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by intro i j a b ha hb; simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def powersData : FullSymbolRightLocalization.Data ℚ where
  denominators := Submonoid.powers (2 : ℚ)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore := inferInstance

def chartFiltration : FiltrationData powersData.Localization where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by intro i j a b ha hb; simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def chart : FullSymbolFilteredChart.Data ℚ where
  localization := powersData
  sourceFiltration := rationalFiltration
  chartFiltration := chartFiltration
  map_filtered := by
    intro n a ha
    change powersData.numerator a ∈ Set.univ
    exact Set.mem_univ _

def x3 : ReesTerm rationalFiltration :=
  { degree := 3, value := 3,
    bounded := by simp [HasDegreeAtMost, rationalFiltration] }

def x5 : ReesTerm rationalFiltration :=
  { degree := 5, value := 5,
    bounded := by simp [HasDegreeAtMost, rationalFiltration] }

example : ∃ (N : ℕ) (s : chart.localization.denominators),
    ∀ x ∈ [x3, x5], x.degree ≤ N ∧
      HasDegreeAtMost chart.chartFiltration N
        (chart.localization.numerator x.value) ∧
      ∃ a : ℚ,
        chart.localization.numerator x.value *
            chart.localization.numerator (s : ℚ) =
          chart.localization.numerator a := by
  exact chart.finite_symbol_chart_control [x3, x5]

example : ∃ s : chart.localization.denominators, ∀ x ∈ [x3, x5],
    ∃ a : ℚ,
      chart.localization.numerator x.value *
          chart.localization.numerator (s : ℚ) =
        chart.localization.numerator a := by
  refine ⟨⟨1, ?_⟩, ?_⟩
  · exact ⟨0, by simp⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨3, by
        simp [x3]
      ⟩
    · rcases List.mem_singleton.mp hx with rfl
      exact ⟨5, by
        simp [x5]
      ⟩

example : Function.Injective chart.localization.numerator :=
  chart.chart_map_injective

end SymplecticStaffordTest.FullSymbolFilteredChart

#print axioms SymplecticStaffordTest.FullSymbolFilteredChart.chart
#print axioms
  SymplecticStaffordTest.FullSymbolFilteredChart.x3
