import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Field
import SymplecticStafford.FiniteLength.FilteredMinimalPrimeBridge

namespace SymplecticStafford.FiniteLength.FilteredMinimalPrimeBridgeOracle


/- The concrete localization of ℚ at its unique prime is just a local
   Noetherian coefficient ring.  The proof uses the support-dimension input,
   not an explicit local-Noetherian or annihilator-minimality field. -/
example :
    IsFiniteLength (Localization.AtPrime (⊥ : Ideal ℚ))
      (Localization.AtPrime (⊥ : Ideal ℚ)) := by
  letI : IsField (Localization.AtPrime (⊥ : Ideal ℚ)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    simp
  apply isFiniteLength_of_atPrime_supportDim_zero (p := (⊥ : Ideal ℚ))
  rw [Module.supportDim_self_eq_ringKrullDim]
  letI : Field (Localization.AtPrime (⊥ : Ideal ℚ)) :=
    IsField.toField (by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq,
        ← Localization.AtPrime.map_eq_maximalIdeal]
      simp)
  exact ringKrullDim_eq_zero_of_field _

end SymplecticStafford.FiniteLength.FilteredMinimalPrimeBridgeOracle
