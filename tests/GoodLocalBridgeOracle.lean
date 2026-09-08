import SymplecticStafford.FiniteLength.GoodLocalBridge
import Mathlib.Algebra.Field.Rat

namespace SymplecticStafford.FiniteLength.GoodLocalBridgeOracle

def support : Set Nat := {0}

def point : MinimalSupportPoint support where
  point := 0
  mem_support := by simp [support]
  minimal := by
    intro q hq _
    simpa [support] using hq

def identityInput :
    GoodLocalMinimalPrimeInput (R := ℚ) (S := ℚ) (M := ℚ) (N := ℚ)
      (σ := RingHom.id ℚ) Nat where
  good_finite := inferInstance
  support := support
  minimalPoint := point
  source := LinearMap.id
  source_surjective := Function.surjective_id
  local_noetherian_ring := inferInstance
  local_artinian := inferInstance

example : Module.Finite ℚ ℚ :=
  local_module_finite_of_goodLocalMinimalPrime identityInput

example : IsNoetherian ℚ ℚ :=
  local_module_noetherian_of_goodLocalMinimalPrime identityInput

example : IsFiniteLength ℚ ℚ :=
  local_isFiniteLength_of_goodLocalMinimalPrime identityInput

example : Module.length ℚ ℚ ≠ ⊤ :=
  local_module_length_ne_top_of_goodLocalMinimalPrime identityInput

/- The oracle keeps the Artinian input visible: it is not inferred from a
   finite source alone in the general Noetherian setting. -/
example (h : IsArtinian ℚ ℚ) : IsFiniteLength ℚ ℚ := by
  letI : IsArtinian ℚ ℚ := h
  exact local_isFiniteLength_of_goodLocalMinimalPrime identityInput

end SymplecticStafford.FiniteLength.GoodLocalBridgeOracle
