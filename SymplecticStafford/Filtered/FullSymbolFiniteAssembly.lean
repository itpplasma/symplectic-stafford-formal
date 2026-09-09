import SymplecticStafford.Filtered.FullSymbolFilteredChart
import SymplecticStafford.Source.LocalizedDivisorAssembly

/-!
# Finite full-symbol identities with one original denominator

This is the finite composition layer between an algebraized filtered chart
and original-ring assembly.  Every list entry carries its two localized
coefficients, an explicit chart-filtration bound, and the localized
two-generator identity.  The supplied actual right Ore localization then
clears all coefficients with one denominator on the RIGHT.

The cleared equality is only an equality with that denominator in the
original ring.  The second theorem therefore takes the additional, explicit
right-inverse datum for chart denominators before returning original
cofactors.  No denominator is inferred from a principal symbol, completion,
or power-Ore presentation.
-/

namespace SymplecticStafford.Filtered.FullSymbolFiniteAssembly

universe u

open FullSymbolRightLocalization

variable {R : Type u} [Ring R]

structure BoundedLocalizedIdentity
    (C : FullSymbolFilteredChart.Data R) (d : R) where
  source : R
  q₁ : C.localization.Localization
  q₂ : C.localization.Localization
  bound : Nat
  q₁_bounded : HasDegreeAtMost C.chartFiltration bound q₁
  q₂_bounded : HasDegreeAtMost C.chartFiltration bound q₂
  identity : C.localization.numerator d * q₁ +
      (C.localization.numerator source * C.localization.numerator d) * q₂ = 1

private theorem finite_bound
    {C : FullSymbolFilteredChart.Data R} {d : R}
    (xs : List (BoundedLocalizedIdentity C d)) :
    ∃ N : Nat, ∀ x ∈ xs, x.bound ≤ N := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons x xs ih =>
      rcases ih with ⟨N, hN⟩
      refine ⟨max x.bound N, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact le_trans (hN y hy) (Nat.le_max_right _ _)

/- One common denominator clears every localized identity in the list. -/
theorem finite_common_denominator
    (C : FullSymbolFilteredChart.Data R) (d : R)
    (xs : List (BoundedLocalizedIdentity C d)) :
    ∃ (N : Nat) (s : C.localization.denominators),
      ∀ x ∈ xs, x.bound ≤ N ∧
        HasDegreeAtMost C.chartFiltration N x.q₁ ∧
        HasDegreeAtMost C.chartFiltration N x.q₂ ∧
        ∃ r t : R,
          (s : R) = d * r + (x.source * d) * t := by
  rcases finite_bound xs with ⟨N, hN⟩
  let qs : List C.localization.Localization :=
    xs.flatMap (fun x => [x.q₁, x.q₂])
  rcases C.localization.common_right_clear qs with ⟨s, hs⟩
  refine ⟨N, s, ?_⟩
  intro x hx
  have hbound := hN x hx
  have hq₁ : x.q₁ ∈ qs := by
    dsimp [qs]
    exact List.mem_flatMap.2 ⟨x, hx, by simp⟩
  have hq₂ : x.q₂ ∈ qs := by
    dsimp [qs]
    exact List.mem_flatMap.2 ⟨x, hx, by simp⟩
  rcases hs x.q₁ hq₁ with ⟨r, hr⟩
  rcases hs x.q₂ hq₂ with ⟨t, ht⟩
  have hlocalized :
      C.localization.numerator d * C.localization.numerator r +
          (C.localization.numerator x.source *
            C.localization.numerator d) * C.localization.numerator t =
        C.localization.numerator (s : R) := by
    have hmul := congrArg (fun q : C.localization.Localization =>
      q * C.localization.numerator (s : R)) x.identity
    calc
      C.localization.numerator d * C.localization.numerator r +
          (C.localization.numerator x.source *
            C.localization.numerator d) * C.localization.numerator t =
          (C.localization.numerator d * x.q₁ +
            (C.localization.numerator x.source *
              C.localization.numerator d) * x.q₂) *
              C.localization.numerator (s : R) := by
        rw [add_mul]
        calc
          C.localization.numerator d * C.localization.numerator r +
              (C.localization.numerator x.source *
                C.localization.numerator d) * C.localization.numerator t =
              C.localization.numerator d *
                  (x.q₁ * C.localization.numerator (s : R)) +
                (C.localization.numerator x.source *
                  C.localization.numerator d) *
                    (x.q₂ * C.localization.numerator (s : R)) := by
              rw [hr, ht]
          _ = C.localization.numerator d * x.q₁ *
                C.localization.numerator (s : R) +
              C.localization.numerator x.source *
                C.localization.numerator d * x.q₂ *
                  C.localization.numerator (s : R) := by
              simp only [mul_assoc]
      _ = 1 * C.localization.numerator (s : R) := hmul
      _ = C.localization.numerator (s : R) := one_mul _
  refine ⟨hbound, C.chartFiltration.monotone hbound x.q₁_bounded,
    C.chartFiltration.monotone hbound x.q₂_bounded, r, t, ?_⟩
  apply C.localization.numerator_injective
  simpa only [map_add, map_mul] using hlocalized.symm

/- A common denominator plus explicit original right inverses yields assembly
   witnesses for every identity in the finite family. -/
theorem finite_localized_assembly
    (C : FullSymbolFilteredChart.Data R) (d : R)
    (xs : List (BoundedLocalizedIdentity C d))
    (denominator_right_inverse :
      ∀ s : C.localization.denominators, ∃ u : R, (s : R) * u = 1) :
    ∃ (N : Nat) (s : C.localization.denominators),
      ∀ x ∈ xs, x.bound ≤ N ∧
        HasDegreeAtMost C.chartFiltration N x.q₁ ∧
        HasDegreeAtMost C.chartFiltration N x.q₂ ∧
        ∃ (R₁ R₂ : R),
          (1 : R) = d * R₁ + (x.source * d) * R₂ := by
  classical
  rcases finite_common_denominator C d xs with ⟨N, s, hs⟩
  let hu_exists := denominator_right_inverse s
  let u : R := Classical.choose hu_exists
  have hu : (s : R) * u = 1 := Classical.choose_spec hu_exists
  refine ⟨N, s, ?_⟩
  intro x hx
  rcases hs x hx with ⟨hbound, hq₁, hq₂, r, t, hst⟩
  refine ⟨hbound, hq₁, hq₂, r * u, t * u, ?_⟩
  calc
    (1 : R) = (s : R) * u := hu.symm
    _ = (d * r + (x.source * d) * t) * u := by rw [hst]
    _ = d * (r * u) + (x.source * d) * (t * u) := by
      noncomm_ring

end SymplecticStafford.Filtered.FullSymbolFiniteAssembly

#print axioms
  SymplecticStafford.Filtered.FullSymbolFiniteAssembly.finite_common_denominator
#print axioms
  SymplecticStafford.Filtered.FullSymbolFiniteAssembly.finite_localized_assembly
