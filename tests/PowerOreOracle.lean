import SymplecticStafford.Filtered.PowerOre
import Mathlib.Tactic.NormNum

namespace SymplecticStaffordTest.PowerOre

open SymplecticStafford
open SymplecticStafford.Filtered

/- A concrete chart over the rational field.  The denominator is genuinely
nontrivial (`2`), while the chart is already its algebraic power localization
because every rational is allowed as an original numerator. -/
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

example : (1 : ℚ) ∈ rationalPowerOre.denominatorPowers := by
  exact rationalPowerOre.one_mem_denominatorPowers

example : (2 : ℚ) * 2 ∈ rationalPowerOre.denominatorPowers := by
  apply rationalPowerOre.mul_mem_denominatorPowers
  · exact ⟨1, by norm_num [PowerOreLocalizationCertificate.denominatorPowers,
      rationalPowerOre]⟩
  · exact ⟨1, by norm_num [PowerOreLocalizationCertificate.denominatorPowers,
      rationalPowerOre]⟩

example :
    rationalPowerOre.fractionEval
      (rationalPowerOre.fractionMk 3 2) = (3 : ℚ) / 4 := by
  rw [PowerOreLocalizationCertificate.fractionEval_fractionMk]
  norm_num [rationalPowerOre]

example : Function.Surjective rationalPowerOre.fractionEval := by
  exact rationalPowerOre.fractionEval_surjective

example :
    ((rationalPowerOre.map 3 * rationalPowerOre.inverse ^ 2) *
      (rationalPowerOre.map 5 * rationalPowerOre.inverse ^ 3)) =
      rationalPowerOre.map (3 * 5) * rationalPowerOre.inverse ^ (2 + 3) := by
  apply rationalPowerOre.fractionEval_mul_of_right_ore
    (a := 3) (b := 5) (c := 5) (n := 2) (m := 3) (k := 2)
  norm_num [rationalPowerOre]

end SymplecticStaffordTest.PowerOre
