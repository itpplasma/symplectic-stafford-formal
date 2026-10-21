module

public import SymplecticStafford.FiniteLength.MinimalPrimeLocalTheorem

@[expose] public section

namespace SymplecticStafford.FiniteLength.MinimalPrimeLocalTheoremOracle

/- A concrete local endpoint: over the field ℚ, the zero maximal ideal is
   minimal over the annihilator of the finite one-dimensional module ℚ. -/
example : IsFiniteLength ℚ ℚ := by
  letI : IsLocalRing ℚ := inferInstance
  apply isFiniteLength_of_local_minimal_annihilator
  have hI : Module.annihilator ℚ ℚ = (⊥ : Ideal ℚ) :=
    Module.annihilator_eq_bot.mpr inferInstance
  rw [hI, IsLocalRing.maximalIdeal_eq_bot,
    Ideal.minimalPrimes_eq_subsingleton_self]
  simp

end SymplecticStafford.FiniteLength.MinimalPrimeLocalTheoremOracle
