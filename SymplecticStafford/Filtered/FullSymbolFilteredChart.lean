module

public import SymplecticStafford.Filtered.FullSymbolRightLocalization
public import SymplecticStafford.Filtered.ReesBasic

@[expose] public section

/-!
# Finite algebraic control for a full-symbol chart

This is the finite interface needed when a quantum chart has already been
algebraized.  A genuine right Ore localization of a submonoid of the
original ring is supplied explicitly; the theorem then combines its common
right-denominator operation with the elementary finite filtration bound for
Rees terms.

The result is deliberately conditional.  It does not construct the
denominator submonoid from a principal symbol, identify it with a completed
chart, or assert that a formal slice has an algebraic lift.
-/

namespace SymplecticStafford.Filtered

universe u

namespace FullSymbolFilteredChart

variable {R : Type u} [Ring R]

/- A full-symbol chart together with the two filtrations needed by the finite
   algebraic interface.  `map_filtered` is retained here so a consumer can
   carry bounded source terms into the chart without adding an implicit
   filtration hypothesis later. -/
structure Data (R : Type u) [Ring R] where
  localization : FullSymbolRightLocalization.Data R
  sourceFiltration : FiltrationData R
  chartFiltration : FiltrationData localization.Localization
  map_filtered : ∀ {n : ℕ} {a : R},
    HasDegreeAtMost sourceFiltration n a →
      HasDegreeAtMost chartFiltration n (localization.numerator a)

namespace Data

variable (C : Data R)

private theorem finite_degree_bound
    (xs : List (ReesTerm C.sourceFiltration)) :
    ∃ N : ℕ, ∀ x ∈ xs, x.degree ≤ N := by
  induction xs with
  | nil =>
      exact ⟨0, by simp⟩
  | cons x xs ih =>
      rcases ih with ⟨N, hN⟩
      refine ⟨max x.degree N, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact le_trans (hN y hy) (Nat.le_max_right _ _)

/-!
The finite chart-control statement is the precise algebraic transfer
available from the APIs above.  `s` is one element of the actual supplied
right-Ore denominator submonoid, and every bounded Rees symbol clears on the
right to an original-ring numerator.  The displayed multiplication order is
intentional.
-/
theorem finite_symbol_chart_control
    (xs : List (ReesTerm C.sourceFiltration)) :
    ∃ (N : ℕ) (s : C.localization.denominators),
      ∀ x ∈ xs, x.degree ≤ N ∧
        HasDegreeAtMost C.chartFiltration N
          (C.localization.numerator x.value) ∧
        ∃ a : R,
          C.localization.numerator x.value *
              C.localization.numerator (s : R) =
            C.localization.numerator a := by
  rcases finite_degree_bound C xs with ⟨N, hN⟩
  rcases C.localization.common_right_clear
      (xs.map (fun x => C.localization.numerator x.value)) with ⟨s, hs⟩
  refine ⟨N, s, ?_⟩
  intro x hx
  have hdegree := hN x hx
  have hchart : HasDegreeAtMost C.chartFiltration x.degree
      (C.localization.numerator x.value) :=
    C.map_filtered x.bounded
  refine ⟨hdegree, C.chartFiltration.monotone hdegree hchart, ?_⟩
  have hmem : C.localization.numerator x.value ∈
      xs.map (fun y => C.localization.numerator y.value) := by
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  exact hs _ hmem

/- The chart map remains injective, so an equality between the original
   numerators in the conclusion can be reflected whenever a later consumer
   has a second such equality. -/
theorem chart_map_injective :
    Function.Injective C.localization.numerator :=
  C.localization.numerator_injective

end Data

end FullSymbolFilteredChart

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.FullSymbolFilteredChart.Data.finite_symbol_chart_control
#print axioms
  SymplecticStafford.Filtered.FullSymbolFilteredChart.Data.chart_map_injective
