import SymplecticStafford.Filtered.ReesFiniteAssembly
import Mathlib.Tactic.NormNum

/- Independent concrete oracle for the finite Rees-to-original assembly. -/
namespace SymplecticStaffordTest.ReesFiniteAssembly

open Polynomial
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolRightLocalization
open SymplecticStafford.Filtered.FullSymbolFiniteAssembly
open SymplecticStafford.Filtered.ReesAlgebraicSpecialization

noncomputable section

def F : NegFiltrationData ℚ[X] where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩
  neg_mem := by simp

def sourceFiltration : FiltrationData ℚ[X] where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def identityLocalization : FullSymbolRightLocalization.Data ℚ[X] where
  denominators := Submonoid.powers (1 : ℚ[X])
  regular := by
    intro s hs a hzero
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simpa only [one_pow, mul_one] using hzero
  ore := inferInstance

def chartFiltration :
    FiltrationData identityLocalization.Localization where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def chart : FullSymbolFilteredChart.Data ℚ[X] where
  localization := identityLocalization
  sourceFiltration := sourceFiltration
  chartFiltration := chartFiltration
  map_filtered := by intro n a ha; simp [HasDegreeAtMost, chartFiltration]

def divisor : ReesTerm F.toFiltrationData :=
  ⟨2, 1, by simp [F, HasDegreeAtMost]⟩

def source : ReesTerm F.toFiltrationData :=
  ⟨4, X, by simp [F, HasDegreeAtMost]⟩

def q₁ : chart.localization.Localization :=
  chart.localization.numerator 1

def q₂ : chart.localization.Localization := 0

def localized : FullSymbolFiniteAssembly.BoundedLocalizedIdentity chart divisor.value where
  source := source.value
  q₁ := q₁
  q₂ := q₂
  bound := 6
  q₁_bounded := by
    change q₁ ∈ Set.univ
    trivial
  q₂_bounded := by
    change q₂ ∈ Set.univ
    trivial
  identity := by
    change chart.localization.numerator (1 : ℚ[X]) *
        chart.localization.numerator (1 : ℚ[X]) +
        (chart.localization.numerator source.value *
          chart.localization.numerator (1 : ℚ[X])) * 0 = 1
    rw [mul_zero, add_zero, ← map_mul, one_mul, map_one]

def family : ReesFiniteAssembly.Data F chart where
  divisor := divisor
  source := source
  entries := [localized]
  source_eq := by intro x hx; simp at hx; subst x; rfl

example :
    finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor) = 1 := by
  exact ReesFiniteAssembly.eval_singleton F divisor

example :
    finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => source) = X := by
  exact ReesFiniteAssembly.eval_singleton F source

example :
    ∃ (R₁ R₂ : ℚ[X]),
      (1 : ℚ[X]) =
        finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor) * R₁ +
          (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => source) *
            finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => divisor)) * R₂ := by
  exact ReesFiniteAssembly.one_identity_to_original F chart divisor source q₁ q₂
    ⟨0, by change q₁ ∈ Set.univ; trivial⟩
    ⟨0, by change q₂ ∈ Set.univ; trivial⟩
    (by
      simpa only [ReesFiniteAssembly.eval_singleton, localized, q₁, q₂]
        using localized.identity)
    (by
      intro s
      refine ⟨1, ?_⟩
      rcases (Submonoid.mem_powers_iff _ _).mp s.property with ⟨n, hn⟩
      simpa using hn.symm)

example :
    ∃ (N : Nat) (s : chart.localization.denominators),
      ∀ x ∈ family.entries, x.bound ≤ N ∧
        HasDegreeAtMost chart.chartFiltration N x.q₁ ∧
        HasDegreeAtMost chart.chartFiltration N x.q₂ ∧
        ∃ (R₁ R₂ : ℚ[X]),
          (1 : ℚ[X]) =
            finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => family.divisor) * R₁ +
              (finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => family.source) *
                finiteEvaluate F ({0} : Finset (Fin 1)) (fun _ => family.divisor)) * R₂ := by
  apply ReesFiniteAssembly.finite_family_to_original F chart family
  intro s
  refine ⟨1, ?_⟩
  rcases (Submonoid.mem_powers_iff _ _).mp s.property with ⟨n, hn⟩
  simpa using hn.symm

end

end SymplecticStaffordTest.ReesFiniteAssembly
