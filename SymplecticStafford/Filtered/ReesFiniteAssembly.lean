module

public import SymplecticStafford.Filtered.ReesAlgebraicSpecialization
public import SymplecticStafford.Filtered.FullSymbolFiniteAssembly
public import SymplecticStafford.Filtered.FullSymbolOriginalCofactor

@[expose] public section

/-!
# Finite Rees-to-original assembly

This file composes two already explicit finite interfaces.  A bounded Rees
divisor/source pair is evaluated at the central value `1`, while an actual
right-Ore chart supplies finite denominator clearing and (when requested) a
right inverse for the common denominator.  The output is a literal
original-ring cofactor identity in the same multiplication order.

The chart, Ore equations, denominator inverses, localized identities, and
bounded coefficient terms are all hypotheses.  In particular, this module
does not identify a completion with an algebraic chart, construct an Ore set,
or infer a source from formal data.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

variable {R : Type u} [Ring R]

open ReesAlgebraicSpecialization
open FullSymbolRightLocalization

namespace ReesFiniteAssembly

/- A finite localized family with bounded original divisor/source terms.  The
   per-entry chart bounds are retained by `BoundedLocalizedIdentity`; the
   source equality is separate because the chart API permits a source per
   entry, while this consumer targets one finite source. -/
structure Data (F : NegFiltrationData R)
    (C : FullSymbolFilteredChart.Data R) where
  divisor : ReesTerm F.toFiltrationData
  source : ReesTerm F.toFiltrationData
  entries : List (FullSymbolFiniteAssembly.BoundedLocalizedIdentity C divisor.value)
  source_eq : ∀ x ∈ entries, x.source = source.value

theorem eval_singleton (F : NegFiltrationData R)
    (x : ReesTerm F.toFiltrationData) :
    finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => x) = x.value := by
  simp [finiteEvaluate_eq_sum]

/- One localized identity, with bounded divisor/source coefficients, descends
   through the original-cofactor theorem after the supplied denominator
   right inverse is used. -/
theorem one_identity_to_original
    (F : NegFiltrationData R)
    (C : FullSymbolFilteredChart.Data R)
    (divisor source : ReesTerm F.toFiltrationData)
    (q₁ q₂ : C.localization.Localization)
    (_hq₁ : ∃ n : Nat, HasDegreeAtMost C.chartFiltration n q₁)
    (_hq₂ : ∃ n : Nat, HasDegreeAtMost C.chartFiltration n q₂)
    (hidentity : C.localization.numerator
        (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor)) * q₁ +
        (C.localization.numerator
          (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => source)) *
          C.localization.numerator
            (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor))) * q₂ = 1)
    (denominator_right_inverse :
      ∀ _s : C.localization.denominators, ∃ u : R, (_s : R) * u = 1) :
    ∃ (R₁ R₂ : R),
      (1 : R) =
        finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor) * R₁ +
          (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => source) *
            finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor)) * R₂ := by
  have hidentity' : C.localization.numerator divisor.value * q₁ +
      (C.localization.numerator source.value *
        C.localization.numerator divisor.value) * q₂ = 1 := by
    simpa only [eval_singleton] using hidentity
  rcases FullSymbolOriginalCofactor.localized_two_generator_to_original
      C.localization divisor.value source.value q₁ q₂ hidentity' with
    ⟨s, r, t, hs, hst⟩
  rcases denominator_right_inverse ⟨s, hs⟩ with ⟨u, hu⟩
  refine ⟨r * u, t * u, ?_⟩
  calc
    (1 : R) = s * u := hu.symm
    _ = (divisor.value * r + (source.value * divisor.value) * t) * u := by
      rw [hst]
    _ = divisor.value * (r * u) +
        (source.value * divisor.value) * (t * u) := by
      noncomm_ring
    _ = finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor) * (r * u) +
        (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => source) *
          finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor)) * (t * u) := by
      simp only [eval_singleton]

/- Finite M03 denominator clearing followed by the M11 cofactor step.  The
   result retains the common denominator and chart bounds, not just the final
   identity. -/
theorem finite_family_to_original
    (F : NegFiltrationData R)
    (C : FullSymbolFilteredChart.Data R)
    (P : Data F C)
    (denominator_right_inverse :
      ∀ s : C.localization.denominators, ∃ u : R, (s : R) * u = 1) :
    ∃ (N : Nat) (s : C.localization.denominators),
      ∀ x ∈ P.entries, x.bound ≤ N ∧
        HasDegreeAtMost C.chartFiltration N x.q₁ ∧
        HasDegreeAtMost C.chartFiltration N x.q₂ ∧
        ∃ (R₁ R₂ : R),
          (1 : R) =
            finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => P.divisor) * R₁ +
              (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => P.source) *
                finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => P.divisor)) * R₂ := by
  rcases FullSymbolFiniteAssembly.finite_localized_assembly
      C P.divisor.value P.entries denominator_right_inverse with
    ⟨N, s, hs⟩
  refine ⟨N, s, ?_⟩
  intro x hx
  rcases hs x hx with ⟨hbound, hq₁, hq₂, R₁, R₂, hcof⟩
  refine ⟨hbound, hq₁, hq₂, R₁, R₂, ?_⟩
  simpa only [eval_singleton, P.source_eq x hx] using hcof

end ReesFiniteAssembly

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesFiniteAssembly.one_identity_to_original
#print axioms SymplecticStafford.Filtered.ReesFiniteAssembly.finite_family_to_original
