import SymplecticStafford.Filtered.WeightedDetection
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic
import Mathlib.Tactic.NormNum

namespace SymplecticStafford.Filtered.WeightedDetectionOracle

open WeightedTriangularData

/-- A two-coordinate example with a negative weight and a strictly lower
weight term.  The latter is invisible at the top row, as required. -/
def exampleSystem : WeightedTriangularData (ι := Bool) (K := ℚ) where
  weight := fun i => if i then (4 : Int) else -3
  coefficient := fun i j =>
    if i then (if j then 3 else 0) else (if j then 7 else 2)
  lower_vanish := by
    intro i j hij
    cases i <;> cases j <;> simp_all
  same_weight_vanish := by
    intro i j hij heq
    cases i <;> cases j <;> simp_all
  diagonal_ne_zero := by
    intro i
    cases i <;> norm_num

def exampleVector : Bool → ℚ := fun i => if i then 0 else 1

example : exampleSystem.action exampleVector false = 2 := by
  norm_num [WeightedTriangularData.action, exampleSystem, exampleVector]

example : exampleSystem.action exampleVector false ≠ 0 := by
  apply exampleSystem.action_ne_zero_at_top
  constructor
  · norm_num [exampleVector]
  · intro j hj
    cases j
    · norm_num [exampleSystem, exampleVector]
    · exfalso
      exact hj (by simp [exampleVector])

example : ∃ i, exampleSystem.action exampleVector i ≠ 0 := by
  apply exampleSystem.action_ne_zero_of_nonzero
  exact ⟨false, by norm_num [exampleVector]⟩

end SymplecticStafford.Filtered.WeightedDetectionOracle
