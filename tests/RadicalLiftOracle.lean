import SymplecticStafford.FiniteLength.RadicalLift
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic

/-! Independent checks for the finite top-lifting and activated-relation
interfaces.  These examples instantiate the abstract hypotheses over `ℚ`;
they do not assert finite length for an arbitrary quotient. -/

namespace SymplecticStafford.FiniteLength

section LiftReplay

abbrev R := ℚ
abbrev M := ℚ

noncomputable def oneLevel : FiniteTopLifting (R := R) (M := M) 1 1 where
  level := fun i => if i = 0 then Set.univ else ({0} : Set ℚ)
  top := by simp
  terminal := by simp
  step := by
    intro i hi x hx
    have hi0 : i = 0 := by omega
    subst i
    refine ⟨x, ?_, ?_⟩
    · exact ⟨MulOpposite.op x, by simp⟩
    · simp

example : RightCyclic (R := R) (1 : M) :=
  rightCyclic_of_finite_top_lifting oneLevel

example (x : M) : RightGenerated (R := R) (1 : M) x := by
  exact rightGenerated_of_finite_top_lifting oneLevel x

end LiftReplay

section ActivatedReplay

noncomputable def ratAction (r m : ℚ) : ℚ := m * r

theorem ratAction_add (r x y : ℚ) :
    ratAction r (x + y) = ratAction r x + ratAction r y := by
  dsimp [ratAction]
  ring

theorem ratCentral (k m r : ℚ) :
    ratAction r (k • m) = k • ratAction r m := by
  dsimp [ratAction]
  ring

example (k : ℚ) :
    ratAction 0 (1 + k • (2 : ℚ)) +
        k • ratAction 3 (1 : ℚ) = k • (3 : ℚ) := by
  exact pencil_right_action_add ratAction ratAction_add ratCentral
    1 2 3 3 0 (by norm_num [ratAction]) (by norm_num [ratAction]) k

example (k : ℚ) :
    ratAction 0 (1 + k • (2 : ℚ)) =
      k • (3 : ℚ) - k • ratAction 3 (1 : ℚ) := by
  exact pencil_right_action_eq ratAction ratAction_add ratCentral
    1 2 3 3 0 (by norm_num [ratAction]) (by norm_num [ratAction]) k

end ActivatedReplay

end SymplecticStafford.FiniteLength
