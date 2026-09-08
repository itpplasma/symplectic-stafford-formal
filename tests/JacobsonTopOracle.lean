import SymplecticStafford.FiniteLength.JacobsonTop
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
Independent behavioral oracles for actual radical lifting.  Multiplication
in `ZMod 4` determines the generators without using a top or filtration
certificate.  This tests a nonsimple module with nonzero radical.  A second
oracle uses a genuinely noncommutative matrix ring and catches scalar-side
errors.  All finite arithmetic uses kernel-reduced `decide`.
-/

namespace SymplecticStafford.FiniteLength.JacobsonTopOracle

abbrev Four := ZMod 4

/-- Direct multiplication, independent of module radicals: exactly the odd
residues generate the regular right module. -/
theorem four_generators : ∀ x : Four,
    (∀ y : Four, ∃ r : Four, x * r = y) ↔ x = 1 ∨ x = 3 := by
  decide

theorem four_rightCyclic (x : Four) :
    RightCyclic (R := Four) x ↔ x = 1 ∨ x = 3 := by
  rw [← four_generators x]
  constructor
  · intro h y
    obtain ⟨r, hr⟩ := h y
    exact ⟨r.unop, hr⟩
  · intro h y
    obtain ⟨r, hr⟩ := h y
    exact ⟨MulOpposite.op r, hr⟩

/-- The actual quotient has exactly the generating images independently
predicted by the residue multiplication table. -/
example (x : Four) :
    RightCyclic (R := Four) ((Module.jacobson Fourᵐᵒᵖ Four).mkQ x) ↔
      x = 1 ∨ x = 3 := by
  rw [← rightCyclic_iff_jacobson_quotient]
  exact four_rightCyclic x

/-- The radical used above is nonzero, so the quotient replay cannot collapse
to the identity comparison on a semisimple module. -/
theorem two_mem_actual_radical : (2 : Four) ∈ Module.jacobson Fourᵐᵒᵖ Four := by
  rw [Module.jacobson, Submodule.mem_sInf]
  intro N hN
  by_contra htwo
  have hstrict : N < N ⊔ Submodule.span Fourᵐᵒᵖ ({2} : Set Four) := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply htwo
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self 2)
  have htop := hN.2 _ hstrict
  have hone : (1 : Four) ∈ N ⊔ Submodule.span Fourᵐᵒᵖ ({2} : Set Four) := by
    rw [htop]
    trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hy
  have h2x : MulOpposite.op (2 : Four) • x = (2 : Four) := by
    change x * 2 = 2
    have htwo_sq : (2 : Four) * 2 = 0 := by decide
    have hy2 : y * 2 = 0 := by
      rw [← hr]
      change (2 * r.unop) * 2 = 0
      calc
        (2 * r.unop) * 2 = (2 * 2) * r.unop := by ring
        _ = 0 := by rw [htwo_sq, zero_mul]
    have hm := congrArg (fun z : Four => z * 2) hxy
    simpa only [add_mul, hy2, add_zero, one_mul] using hm
  exact htwo (h2x ▸ N.smul_mem (MulOpposite.op (2 : Four)) hx)

theorem four_radical_ne_bot : Module.jacobson Fourᵐᵒᵖ Four ≠ ⊥ := by
  intro h
  have hm := two_mem_actual_radical
  rw [h, Submodule.mem_bot] at hm
  exact (by decide : (2 : Four) ≠ 0) hm

example : ¬ IsSemisimpleModule Fourᵐᵒᵖ Four := by
  intro h
  let _ := h
  exact four_radical_ne_bot (IsSemisimpleModule.jacobson_eq_bot _ _)

example : IsSemisimpleModule Fourᵐᵒᵖ
    (Four ⧸ Module.jacobson Fourᵐᵒᵖ Four) :=
  jacobson_quotient_isSemisimple

example : ¬ RightCyclic (R := Four)
    ((Module.jacobson Fourᵐᵒᵖ Four).mkQ (2 : Four)) := by
  rw [← rightCyclic_iff_jacobson_quotient, four_rightCyclic]
  decide

example : ∃ N : Submodule Fourᵐᵒᵖ Four,
    IsSimpleModule Fourᵐᵒᵖ (Four ⧸ N) ∧ N.mkQ (2 : Four) = 0 := by
  apply exists_simple_quotient_killing_of_not_rightCyclic
  rw [four_rightCyclic]
  decide

example (N : Submodule Fourᵐᵒᵖ Four)
    (hsimple : IsSimpleModule Fourᵐᵒᵖ (Four ⧸ N)) : N.mkQ (3 : Four) ≠ 0 := by
  apply (rightCyclic_iff_nonzero_in_simple_quotients (3 : Four)).mp
    ((four_rightCyclic 3).mpr (Or.inr rfl)) N hsimple

abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 2)

def E01 : Mat := !![0, 1; 0, 0]
def E10 : Mat := !![0, 0; 1, 0]

/-- The multiplication table distinguishes both factor orders. -/
example : E01 * E10 ≠ E10 * E01 := by decide

/-- The singular matrix cannot generate the regular right module; this is
checked directly in the finite noncommutative multiplication table. -/
theorem E01_not_generator : ¬ ∀ y : Mat, ∃ r : Mat, E01 * r = y := by
  decide

example : ¬ RightCyclic (R := Mat)
    ((Module.jacobson Matᵐᵒᵖ Mat).mkQ E01) := by
  rw [← rightCyclic_iff_jacobson_quotient]
  intro h
  apply E01_not_generator
  intro y
  obtain ⟨r, hr⟩ := h y
  exact ⟨r.unop, hr⟩

example : RightCyclic (R := Mat)
    ((Module.jacobson Matᵐᵒᵖ Mat).mkQ (1 : Mat)) := by
  rw [← rightCyclic_iff_jacobson_quotient]
  intro y
  exact ⟨MulOpposite.op y, by change (1 : Mat) * y = y; exact one_mul y⟩

end SymplecticStafford.FiniteLength.JacobsonTopOracle

#print axioms SymplecticStafford.FiniteLength.JacobsonTopOracle.two_mem_actual_radical
#print axioms SymplecticStafford.FiniteLength.JacobsonTopOracle.E01_not_generator
