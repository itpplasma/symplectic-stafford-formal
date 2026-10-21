module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic
public import SymplecticStafford.FiniteLength.ActualRadicalTop

@[expose] public section

/-! Independent oracle for the finite-length-to-radical-top extraction. -/

namespace SymplecticStafford.ActualRadicalTopOracle

open SymplecticStafford.FiniteLength

abbrev R := ℚ
abbrev M := Unit

instance unitAddCommGroup : AddCommGroup Unit where
  add := fun _ _ => ()
  zero := ()
  neg := fun _ => ()
  add_assoc := by intros; rfl
  zero_add := by intro; rfl
  add_zero := by intro; rfl
  neg_add_cancel := by intro; rfl
  add_comm := by intros; rfl

instance unitModule : Module Rᵐᵒᵖ M where
  smul := fun _ _ => ()
  one_smul := by intro; rfl
  mul_smul := by intros; rfl
  smul_zero := by intro; rfl
  smul_add := by intros; rfl
  add_smul := by intros; rfl
  zero_smul := by intro; rfl

def zeroFiltration : RightMinimalSupportFiltration
    (R := R) (M := M) (α := Unit) 0 where
  support := Set.univ
  minimalPoint := {
    point := ()
    mem_support := by simp
    minimal := by intro q hq hle; cases q; rfl }
  level := fun _ => ⊥
  head := by rfl
  last := by
    apply le_antisymm
    · exact bot_le
    · intro x hx
      cases x
      exact Submodule.zero_mem _
  step := by intro i; exact Fin.elim0 i
  quotient_finite := by intro i; exact Fin.elim0 i

theorem extracted_zero_module_facts :
    Module.Finite Rᵐᵒᵖ M ∧
      IsFiniteLength Rᵐᵒᵖ M ∧
      IsSemisimpleModule Rᵐᵒᵖ (M ⧸ Module.jacobson Rᵐᵒᵖ M) ∧
      (∀ v : M,
        RightCyclic (R := R) v ↔
          RightCyclic (R := R)
            ((Module.jacobson Rᵐᵒᵖ M).mkQ v)) := by
  exact actual_radical_top_of_right_filtration zeroFiltration

example (v : M) : RightCyclic (R := R) v := by
  obtain ⟨_, _, _, hcyclic⟩ := extracted_zero_module_facts
  rw [hcyclic]
  intro y
  refine Quotient.inductionOn y (fun y => ?_)
  cases y
  exact ⟨0, rfl⟩

end SymplecticStafford.ActualRadicalTopOracle

#print axioms
  SymplecticStafford.ActualRadicalTopOracle.extracted_zero_module_facts
