module

public import SymplecticStafford.Filtered.FullSymbolRightLocalization

@[expose] public section

/-!
# Finite source-value clearing from an actual Ore chart

The full-symbol algebraization step often needs denominator clearing only for
the finitely many original-ring values appearing in one finite Rees chart.
This theorem isolates exactly that transfer from an *already supplied* actual
right Ore localization.  It does not construct the denominator monoid from a
principal symbol, and it adds no completion or power-denominator hypothesis.
-/

namespace SymplecticStafford.Filtered.FullSymbolActualOreFinite

universe u

variable {R : Type u} [Ring R]

open FullSymbolRightLocalization

theorem finite_source_values_common_right_clear
    (C : FullSymbolRightLocalization.Data R) (xs : List R) :
    ∃ s : C.denominators, ∀ x ∈ xs, ∃ a : R,
      C.numerator x * C.numerator (s : R) = C.numerator a := by
  rcases C.common_right_clear (xs.map C.numerator) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro x hx
  have hmem : C.numerator x ∈ xs.map C.numerator := by
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  exact hs _ hmem

end SymplecticStafford.Filtered.FullSymbolActualOreFinite

#print axioms
  SymplecticStafford.Filtered.FullSymbolActualOreFinite.finite_source_values_common_right_clear
