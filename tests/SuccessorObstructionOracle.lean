import SymplecticStafford.Induction.SuccessorObstruction
import Mathlib.Data.ZMod.Basic

/-!
# Independent oracle for the M10 obstruction

The oracle checks both directions of the boundary: the flat defect admits the
lower `P₁` contract, while no `P₂` or successor rule can exist.  This is a
behavioral mathematical countermodel to treating the lower-call interface as
if it already supplied the successor's defect decrease.
-/

namespace SymplecticStafford.SuccessorObstructionOracle

open SymplecticStafford.Induction

example : StrongPh 0 1 flatDefect := flatLower

example (h : StrongPh 0 1 baseFlatDefect) : False := base_impossible h

example (h : StrongPh 0 2 flatDefect) : False := flat_next_impossible h

def parameters : CentralParameters Nat (ZMod 1) where
  embed := fun _ => 0
  central := by intros; simp

example (h : SuccessorRule parameters Unit 0 1 flatDefect flatLower) : False := by
  exact flat_no_successor_rule parameters Unit h

example : defectBound 0 1 = -1 := by
  norm_num [defectBound]

example : defectBound 0 2 = -2 := by
  norm_num [defectBound]

end SymplecticStafford.SuccessorObstructionOracle
