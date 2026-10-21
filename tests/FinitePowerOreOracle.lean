module

public import SymplecticStafford.Filtered.FinitePowerOre
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace SymplecticStaffordTest.FinitePowerOre

open SymplecticStafford
open SymplecticStafford.Filtered

def rationalFiltration : Filtered.FiltrationData ℚ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def rationalPowerOre : Filtered.PowerOreLocalizationCertificate ℚ ℚ where
  sourceFiltration := rationalFiltration
  chartFiltration := rationalFiltration
  map := RingHom.id ℚ
  map_filtered := by intro n a ha; exact ha
  denominator := 2
  denominator_mem := ⟨0, by simp [Filtered.HasDegreeAtMost, rationalFiltration]⟩
  right_clearable := by
    intro x
    exact ⟨0, x, by simp⟩
  inverse := (2 : ℚ)⁻¹
  denominator_mul_inverse := by norm_num
  inverse_mul_denominator := by norm_num
  right_ore := by
    intro a n
    refine ⟨n, a, ?_⟩
    simp [mul_comm]

example :
    rationalPowerOre.map 3 * rationalPowerOre.inverse ^ 1 =
      rationalPowerOre.map (3 * 2 ^ (3 - 1)) * rationalPowerOre.inverse ^ 3 := by
  exact rationalPowerOre.fractionEval_raise 3 (by norm_num)

example : ∃ N : Nat, ∀ p ∈ ([(3, 2), (5, 1), (7, 4)] : List (ℚ × Nat)),
    p.2 ≤ N ∧
      rationalPowerOre.map p.1 * rationalPowerOre.inverse ^ p.2 =
        rationalPowerOre.map (p.1 * rationalPowerOre.denominator ^ (N - p.2)) *
          rationalPowerOre.inverse ^ N := by
  refine ⟨4, ?_⟩
  intro p hp
  simp at hp
  rcases hp with rfl | rfl | rfl
  · norm_num [rationalPowerOre]
  · norm_num [rationalPowerOre]
  · norm_num [rationalPowerOre]

example :
    rationalPowerOre.map 3 * rationalPowerOre.inverse ^ 2 =
      rationalPowerOre.map 12 * rationalPowerOre.inverse ^ 4 ↔
      rationalPowerOre.fractionRel (3, 2) (12, 4) := by
  apply rationalPowerOre.fractionEval_eq_iff_fractionRel
    (p := (3, 2)) (q := (12, 4))
  intro x y h
  exact h

example : ∃ N : Nat, ∀ x ∈
    ([rationalPowerOre.map 3, rationalPowerOre.map 5,
      rationalPowerOre.map 7] : List ℚ),
    ∃ a : ℚ, x = rationalPowerOre.map a * rationalPowerOre.inverse ^ N := by
  exact rationalPowerOre.finite_fraction_normal_form _

example :
    rationalPowerOre.fractionProduct
        ([(3, 2), (5, 3), (7, 1)] : List (ℚ × Nat)) =
      rationalPowerOre.map 105 * rationalPowerOre.inverse ^ 6 := by
  norm_num [PowerOreLocalizationCertificate.fractionProduct,
    rationalPowerOre]

example : ∃ a : ℚ, ∃ n : Nat,
    rationalPowerOre.fractionProduct
        ([(3, 2), (5, 3), (7, 1)] : List (ℚ × Nat)) =
      rationalPowerOre.map a * rationalPowerOre.inverse ^ n := by
  exact rationalPowerOre.finite_fraction_product_normal_form _

def symbolOne : ReesTerm rationalFiltration :=
  { degree := 1, value := 3,
    bounded := by simp [Filtered.HasDegreeAtMost, rationalFiltration] }

def symbolTwo : ReesTerm rationalFiltration :=
  { degree := 3, value := 5,
    bounded := by simp [Filtered.HasDegreeAtMost, rationalFiltration] }

example : ∃ (degree denominator : Nat),
    (∀ x ∈ ([symbolOne, symbolTwo] : List (ReesTerm rationalFiltration)),
      x.degree ≤ degree ∧
        ∃ p : ReesAlgebra rationalFiltration,
          (p : ReesPolynomial ℚ) =
            SkewPolynomial.monomial degree x.value) ∧
    (∀ x ∈ ([symbolOne, symbolTwo] : List (ReesTerm rationalFiltration)),
      ∃ a : ℚ,
        rationalPowerOre.map x.value =
          rationalPowerOre.map a * rationalPowerOre.inverse ^ denominator) := by
  exact finite_rees_symbol_chart_normal_form rationalPowerOre _

end SymplecticStaffordTest.FinitePowerOre
