import SymplecticStafford.FiniteLength.MinimalPrimeLength
import Mathlib.Algebra.Field.Rat

namespace SymplecticStafford.FiniteLength.Oracle

/- The one-point support order is a concrete check that the minimal-point
interface is not an unelaborated placeholder. -/
def support : Set Nat := {0}

def point : MinimalSupportPoint support where
  point := 0
  mem_support := by simp [support]
  minimal := by
    intro q hq _
    simpa [support] using hq

example : point.point = 0 := rfl
example : point.point ∈ support := point.mem_support

/- Over the rationals, the identity map supplies a concrete local model.  The
result still uses explicitly supplied Noetherian/Artinian model hypotheses. -/
def identityInput :
    MinimalPrimeLocalInput ℚ ℚ ℚ Nat where
  good_finite := inferInstance
  support := support
  minimalPoint := point
  source := LinearMap.id
  source_surjective := Function.surjective_id
  local_noetherian := inferInstance
  local_artinian := inferInstance

example : IsFiniteLength ℚ ℚ :=
  local_isFiniteLength_of_minimalPrime identityInput

example : Module.Finite ℚ ℚ :=
  local_module_finite_of_minimalPrime identityInput

example : Module.length ℚ ℚ ≠ ⊤ :=
  local_module_length_ne_top_of_minimalPrime identityInput

example (N : Submodule ℚ ℚ) (h : IsFiniteLength ℚ ℚ) :
    IsFiniteLength ℚ N :=
  isFiniteLength_submodule_of_isFiniteLength h N

example (N : Submodule ℚ ℚ) (h : IsFiniteLength ℚ ℚ) :
    IsFiniteLength ℚ (ℚ ⧸ N) :=
  isFiniteLength_quotient_of_isFiniteLength h N

end SymplecticStafford.FiniteLength.Oracle
