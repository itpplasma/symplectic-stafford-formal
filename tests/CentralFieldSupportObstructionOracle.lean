import Mathlib.Tactic
import SymplecticStafford.Induction.CentralFieldSupportObstruction

/-!
# Independent oracle for the central-field support obstruction

The scalar module is instantiated over the concrete central field `ℚ` and
ambient ring `ℚ`.  Its actual two-layer quotient support is nonempty, the
constant avoidance polynomial is good at every scalar, and source-independent
strict pencil removal is nevertheless impossible.
-/

namespace SymplecticStafford.Induction.CentralFieldSupportObstructionOracle

open SymplecticStafford.Induction

def parameters : CentralParameters ℚ ℚ where
  embed := id
  central := by intro z x; exact mul_comm _ _

example : (sourceIndependentActualSupport (K := ℚ) (U := ℚ) 0).Nonempty := by
  exact sourceIndependentActualSupport_nonempty

example : ∀ z : ℚ,
    (constantAvoidancePolynomial (K := ℚ) ()).eval z ≠ 0 := by
  intro z
  exact constantAvoidancePolynomial_good z

example : ∀ f g : ℚ,
    sourceIndependentActualSupport (K := ℚ) (U := ℚ) f =
      sourceIndependentActualSupport (K := ℚ) (U := ℚ) g := by
  intro f g
  exact sourceIndependentActualSupport_eq f g

example :
    ¬ SourceIndependentCentralPencilStrictRemoval
      (K := ℚ) (U := ℚ) parameters := by
  exact not_sourceIndependentCentralPencilStrictRemoval parameters

example :
    (sourceIndependentActualSupport (K := ℚ) (U := ℚ) 0).Nonempty ∧
      (∀ z : ℚ, (constantAvoidancePolynomial (K := ℚ) ()).eval z ≠ 0) ∧
      ¬ SourceIndependentCentralPencilStrictRemoval
        (K := ℚ) (U := ℚ) parameters := by
  exact actual_support_and_scalar_avoidance_do_not_supply_strict_removal
    parameters

end SymplecticStafford.Induction.CentralFieldSupportObstructionOracle

#print axioms SymplecticStafford.Induction.actual_support_and_scalar_avoidance_do_not_supply_strict_removal
