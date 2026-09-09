import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing
import SymplecticStafford.Filtered.FullSymbolFiniteAssembly

/- Independent trust-disabled oracle: two noncommutative matrix identities
   share one actual right-Ore chart denominator, retain chart bounds, and
   produce original assembly cofactors. -/
namespace SymplecticStaffordTest.FullSymbolFiniteAssemblyOracle

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolRightLocalization
open SymplecticStafford.Filtered.FullSymbolFiniteAssembly

noncomputable section

abbrev M := Matrix (Fin 2) (Fin 2) ℚ

def constantFiltrationFor : FiltrationData M where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; trivial
  exhaustive := by intro x; exact ⟨0, trivial⟩

noncomputable def matrixIdentityData : FullSymbolRightLocalization.Data M where
  denominators := Submonoid.powers (1 : M)
  regular := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    rcases hs with ⟨n, rfl⟩
    simp
  ore :=
    { ore_right_cancel := by
        intro r₁ r₂ s h
        have hs' : (s : Mᵐᵒᵖ).unop ∈ Submonoid.powers (1 : M) := s.property
        rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
        have hs1 : (s : Mᵐᵒᵖ) = 1 := by
          apply MulOpposite.op_injective
          simpa using hn.symm
        exact ⟨1, by simpa [hs1] using h⟩
      oreNum := fun r s => r
      oreDenom := fun r s => 1
      ore_eq := by
        intro r s
        have hs' : (s : Mᵐᵒᵖ).unop ∈ Submonoid.powers (1 : M) := s.property
        rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
        have hs1 : (s : Mᵐᵒᵖ) = 1 := by
          apply MulOpposite.op_injective
          simpa using hn.symm
        simpa [hs1] }

local instance matrixOreInstance : OreLocalization.OreSet
    (AlgebraicAnalysis.OreRightLocalization.oppositeSubmonoid
      matrixIdentityData.denominators) := matrixIdentityData.ore

def matrixChartFiltration :
    FiltrationData (FullSymbolRightLocalization.Data.Localization matrixIdentityData) where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; trivial
  exhaustive := by intro x; exact ⟨0, trivial⟩

noncomputable def chart : FullSymbolFilteredChart.Data M where
  localization := matrixIdentityData
  sourceFiltration := constantFiltrationFor
  chartFiltration := matrixChartFiltration
  map_filtered := by intro n a ha; trivial

example (u : Mˣ) (f g : M) :
    ∃ (N : Nat) (s : chart.localization.denominators),
      ∀ x ∈ ([
        { source := f, q₁ := chart.localization.numerator ((u⁻¹ : Mˣ) : M),
          q₂ := 0, bound := 3, q₁_bounded := by trivial,
          q₂_bounded := by trivial,
          identity := by
            rw [mul_zero, add_zero, ← map_mul, u.mul_inv, map_one] },
        { source := g, q₁ := chart.localization.numerator ((u⁻¹ : Mˣ) : M),
          q₂ := 0, bound := 5, q₁_bounded := by trivial,
          q₂_bounded := by trivial,
          identity := by
            rw [mul_zero, add_zero, ← map_mul, u.mul_inv, map_one] }
      ] : List (BoundedLocalizedIdentity chart (u : M))),
        x.bound ≤ N ∧
          HasDegreeAtMost chart.chartFiltration N x.q₁ ∧
          HasDegreeAtMost chart.chartFiltration N x.q₂ ∧
          ∃ r t : M, (s : M) = (u : M) * r + (x.source * (u : M)) * t := by
  exact finite_common_denominator chart (u : M) _

example (u : Mˣ) (f g : M) :
    ∃ (N : Nat) (s : chart.localization.denominators),
      ∀ x ∈ ([
        { source := f, q₁ := chart.localization.numerator ((u⁻¹ : Mˣ) : M),
          q₂ := 0, bound := 3, q₁_bounded := by trivial,
          q₂_bounded := by trivial,
          identity := by
            rw [mul_zero, add_zero, ← map_mul, u.mul_inv, map_one] },
        { source := g, q₁ := chart.localization.numerator ((u⁻¹ : Mˣ) : M),
          q₂ := 0, bound := 5, q₁_bounded := by trivial,
          q₂_bounded := by trivial,
          identity := by
            rw [mul_zero, add_zero, ← map_mul, u.mul_inv, map_one] }
      ] : List (BoundedLocalizedIdentity chart (u : M))),
        x.bound ≤ N ∧
          HasDegreeAtMost chart.chartFiltration N x.q₁ ∧
          HasDegreeAtMost chart.chartFiltration N x.q₂ ∧
          ∃ R₁ R₂ : M,
            (1 : M) = (u : M) * R₁ + (x.source * (u : M)) * R₂ := by
  apply finite_localized_assembly chart (u : M) _
  intro s
  refine ⟨1, ?_⟩
  have hs' : (s : M) ∈ Submonoid.powers (1 : M) := s.property
  rcases (Submonoid.mem_powers_iff _ _).mp hs' with ⟨n, hn⟩
  simpa using hn.symm

end
end SymplecticStaffordTest.FullSymbolFiniteAssemblyOracle

#print axioms
  SymplecticStafford.Filtered.FullSymbolFiniteAssembly.finite_common_denominator
#print axioms
  SymplecticStafford.Filtered.FullSymbolFiniteAssembly.finite_localized_assembly
