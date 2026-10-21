module

public import SymplecticStafford.FiniteLength.ActivatedPencilBoundary
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Independent oracle for the unstructured M07 boundary

The oracle replays the concrete two-vector calculation at `0` and at a
nonzero scalar.  It then checks the resulting infinite bad set.  In
particular, the source theorem cannot be read as an unconditional
finite-length activated-pencil theorem: the missing affine/central action is
observable in this finite repeated block.
-/

namespace SymplecticStafford.FiniteLength.ActivatedPencilBoundaryOracle

open SymplecticStafford.FiniteLength

example :
    LinearIndependent ℚ (unstructuredPencil 0) := by
  exact unstructuredPencil_zero_independent

example {z : ℚ} (hz : z ≠ 0) :
    ¬ LinearIndependent ℚ (unstructuredPencil z) := by
  exact unstructuredPencil_nonzero_not_independent hz

example : ¬ unstructuredPencilBad.Finite := by
  exact unstructuredPencilBad_not_finite

example :
    LinearIndependent ℚ (unstructuredPencil 0) ∧
      ¬ unstructuredPencilBad.Finite := by
  exact finite_dimension_and_initial_generation_not_enough

end SymplecticStafford.FiniteLength.ActivatedPencilBoundaryOracle

#print axioms
  SymplecticStafford.FiniteLength.unstructuredPencilBad_not_finite
