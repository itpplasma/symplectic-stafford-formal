import Mathlib.Tactic
import SymplecticStafford.Filtered.FiniteFilteredLengthFormula

/-!
# Independent oracle for exact finite-filtered length accounting

The module is `ℚ × ℚ` with the genuine chain
`ℚ² ⊃ ℚ × 0 ⊃ 0`.  The two adjacent quotients are both visibly nonzero;
the oracle then consumes the exact sum theorem on this concrete proper
intermediate carrier.
-/

namespace SymplecticStafford.Filtered.FiniteFilteredLengthFormulaOracle

noncomputable section

open SymplecticStafford.Filtered

def axis : Submodule ℚ (ℚ × ℚ) where
  carrier := {x | x.2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simp [hx, hy]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    simp [hx]

def planeFiltration : FiniteFilteredModule (R := ℚ) (M := ℚ × ℚ) where
  height := 2
  carrier := fun n => if n = 0 then ⊤ else if n = 1 then axis else ⊥
  exhaustive := by simp
  descending := by
    intro n
    by_cases hzero : n = 0
    · subst n
      simp [axis]
    · by_cases hone : n = 1
      · subst n
        simp [axis]
      · have hsucc_zero : n + 1 ≠ 0 := by omega
        have hsucc_one : n + 1 ≠ 1 := by omega
        simp [hzero, hone, hsucc_zero, hsucc_one]
  separated := by simp

example : axis < (⊤ : Submodule ℚ (ℚ × ℚ)) := by
  apply lt_of_le_of_ne le_top
  intro htop
  have hbad : ((0, 1) : ℚ × ℚ) ∈ axis := by
    rw [htop]
    trivial
  simpa [axis] using hbad

example : ∃ x : planeFiltration.carrier 0,
    (x : ℚ × ℚ) ∉ planeFiltration.carrier 1 := by
  refine ⟨⟨(0, 1), by simp [planeFiltration]⟩, ?_⟩
  simp [planeFiltration, axis]

example : ∃ x : planeFiltration.carrier 1,
    (x : ℚ × ℚ) ∉ planeFiltration.carrier 2 := by
  refine ⟨⟨(1, 0), by simp [planeFiltration, axis]⟩, ?_⟩
  simp [planeFiltration]

example :
    Submodule.mkQ (planeFiltration.carrier 1) ((0, 1) : ℚ × ℚ) ≠ 0 := by
  rw [planeFiltration.quotient_ne_zero_iff_not_mem]
  simp [planeFiltration, axis]

example :
    Submodule.mkQ (planeFiltration.carrier 2) ((1, 0) : ℚ × ℚ) ≠ 0 := by
  rw [planeFiltration.quotient_ne_zero_iff_not_mem]
  simp [planeFiltration]

theorem plane_length_formula :
    Module.length ℚ (ℚ × ℚ) =
      ∑ k ∈ Finset.Ico 0 planeFiltration.height,
        FiniteFilteredModule.layerLength planeFiltration k := by
  exact FiniteFilteredModule.length_eq_sum_layerLength planeFiltration

end

end SymplecticStafford.Filtered.FiniteFilteredLengthFormulaOracle

#print axioms
  SymplecticStafford.Filtered.FiniteFilteredLengthFormulaOracle.planeFiltration
#print axioms
  SymplecticStafford.Filtered.FiniteFilteredLengthFormulaOracle.axis
#print axioms
  SymplecticStafford.Filtered.FiniteFilteredLengthFormulaOracle.plane_length_formula
