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

/- The stronger M05 endpoint uses the canonical module localization and
   simultaneously checks that the minimal-prime fiber is nonzero. -/
example :
    Nontrivial (LocalizedModule (⊥ : Ideal ℚ).primeCompl ℚ) ∧
      IsFiniteLength (Localization.AtPrime (⊥ : Ideal ℚ))
        (LocalizedModule (⊥ : Ideal ℚ).primeCompl ℚ) := by
  have hI : Module.annihilator ℚ ℚ = (⊥ : Ideal ℚ) :=
    Module.annihilator_eq_bot.mpr inferInstance
  apply SymplecticStafford.FiniteLength.localizedModule_nontrivial_and_isFiniteLength_of_mem_annihilator_minimalPrimes
    (P := (⊥ : Ideal ℚ))
  rw [hI, Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/- The support-oriented wrapper accepts a genuine minimal point of the
   module support, rather than an annihilator-minimality certificate. -/
example :
    Nontrivial (LocalizedModule (⊥ : Ideal ℚ).primeCompl ℚ) ∧
      IsFiniteLength (Localization.AtPrime (⊥ : Ideal ℚ))
        (LocalizedModule (⊥ : Ideal ℚ).primeCompl ℚ) := by
  let P : PrimeSpectrum ℚ := ⟨⊥, inferInstance⟩
  have hP : P ∈ Module.support ℚ ℚ := by
    apply Module.mem_support_iff_of_finite.mpr
    exact (Module.annihilator_eq_bot.mpr inferInstance).le
  have hmin : ∀ Q : PrimeSpectrum ℚ, Q ∈ Module.support ℚ ℚ →
      Q ≤ P → P ≤ Q := by
    intro Q _ _
    exact (Subsingleton.elim P Q).le
  simpa [P] using
    (SymplecticStafford.FiniteLength.localizedModule_nontrivial_and_isFiniteLength_of_minimal_support
      P hP hmin)

end SymplecticStafford.FiniteLength.FilteredMinimalPrimeBridgeOracle
