import SymplecticStafford.Source.QuantizedSliceAlgebraization
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs

/- Independent oracle for the bounded formal-to-original reflection theorem. -/
namespace SymplecticStaffordTest.QuantizedSliceAlgebraization

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Source.DifferentialOre
open SymplecticStafford.Source.QuantizedSlice
open SymplecticStafford.Source.QuantizedSlice.ChartData

def rationalFiltration : FiltrationData ℚ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def rationalHypotheses : Hypotheses (U := ℚ) (A := ℚ) (S := ℚ) (K := ℚ) where
  coefficient := RingHom.id ℚ
  coefficient_injective := by intro x y h; exact h
  filtration := rationalFiltration
  coefficient_degree_zero := by intro a; simp [HasDegreeAtMost, rationalFiltration]
  commutator_lowers := by
    intro n P a hP
    simp [HasDegreeAtMost, rationalFiltration]
  cover := [(1, 0)]
  cover_nonzero := by
    intro p hp
    simp at hp
    subst p
    norm_num
  cover_unit := by
    refine ⟨[1], by simp, ?_⟩
    simp [poweredCoverSum]
  chartMap := RingHom.id ℚ
  parameterMap := RingHom.id ℚ
  parameter_central := by intros; exact mul_comm _ _
  localized_S1 := by
    intro d hd
    refine ⟨0, d⁻¹, 0, ?_⟩
    simp [hd]
  right_power_ore := by
    intro p hp x
    simp at hp
    subst p
    exact ⟨0, x, by simp⟩
  left_power_ore := by
    intro p hp x
    simp at hp
    subst p
    exact ⟨0, x, by simp⟩

def rationalChartData : ChartData rationalHypotheses ℚ where
  completionMap := RingHom.id ℚ
  completion_injective := by intro x y h; exact h
  chart_injective := by intro x y h; exact h

def rationalTerm (d : ℚ) (hd : d ≠ 0) :
    ChartData.Term rationalChartData d 0 where
  denominator := 1
  exponent := 0
  weight := 1
  in_cover := by simp [rationalHypotheses]
  bound := 0
  formal₁ := d⁻¹
  formal₂ := 0
  formal_identity := by
    simp [rationalHypotheses, rationalChartData, coefficientValue, hd]
  right₁ := d⁻¹
  right₂ := 0
  right₁_bounded := by simp [rationalHypotheses, rationalFiltration,
    HasDegreeAtMost]
  right₂_bounded := by simp [rationalHypotheses, rationalFiltration,
    HasDegreeAtMost]
  right₁_lift := by simp [rationalChartData]
  right₂_lift := by simp [rationalChartData]

def rationalClearance (d : ℚ) (hd : d ≠ 0) :
    ChartData.Clearance rationalChartData d 0 where
  terms := [rationalTerm d hd]
  formal_unit_identity := by
    simp [rationalTerm, rationalHypotheses, rationalChartData, coefficientValue]

def rationalBridge : ChartData.GlobalBridge rationalHypotheses ℚ where
  completionMap := RingHom.id ℚ
  completion_injective := by intro x y h; exact h
  chart_injective := by intro x y h; exact h
  clearance := by
    intro d hd
    exact ⟨0, ⟨rationalClearance d hd⟩⟩

example : OriginalSameDivisor ℚ := rationalBridge.consume

example (d : ℚ) (hd : d ≠ 0) :
    ∃ N : Nat, ∀ t ∈ (rationalClearance d hd).terms,
      t.bound ≤ N ∧
        HasDegreeAtMost rationalHypotheses.filtration N t.right₁ ∧
        HasDegreeAtMost rationalHypotheses.filtration N t.right₂ := by
  exact rationalChartData.common_bound (rationalClearance d hd)

#print axioms ChartData.to_original_clearance
#print axioms ChartData.GlobalBridge.consume

end SymplecticStaffordTest.QuantizedSliceAlgebraization
