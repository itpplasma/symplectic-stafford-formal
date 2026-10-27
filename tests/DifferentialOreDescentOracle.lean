module

public import SymplecticStafford.Source.DifferentialOreDescent
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-! Independent oracle for the original-ring finite-cover consumer. -/

namespace SymplecticStaffordTest.DifferentialOreDescent

open SymplecticStafford
open SymplecticStafford.Source.DifferentialOre

def rationalFiltration : Filtered.FiltrationData ℚ where
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
  coefficient_degree_zero := by intro a; simp [Filtered.HasDegreeAtMost, rationalFiltration]
  commutator_lowers := by
    intro n P a hP
    simp [Filtered.HasDegreeAtMost, rationalFiltration]
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

def rationalTerm (d F : ℚ) (hd : d ≠ 0) : CoverClearanceTerm rationalHypotheses d F where
  denominator := 1
  exponent := 0
  weight := 1
  cofactor₁ := d⁻¹
  cofactor₂ := 0
  in_cover := by simp [rationalHypotheses]
  clearance := by simp [rationalHypotheses, hd]

def rationalClearance (d : ℚ) (hd : d ≠ 0) :
    ∃ F : ℚ, Nonempty (FiniteCoverClearance rationalHypotheses d F) := by
  refine ⟨0, ⟨⟨[rationalTerm d 0 hd], ?_⟩⟩⟩
  simp [rationalTerm, rationalHypotheses]

def bridge : GlobalClearanceBridge rationalHypotheses where
  clearance := rationalClearance

example : OriginalSameDivisor ℚ :=
  consume_global_clearance rationalHypotheses bridge

example (d : ℚ) (hd : d ≠ 0) :
    ∃ F R S : ℚ, (1 : ℚ) = d * R + (F * d) * S := by
  exact (consume_global_clearance rationalHypotheses bridge) hd

#print axioms SymplecticStafford.Source.DifferentialOre.consume_global_clearance

end SymplecticStaffordTest.DifferentialOreDescent
