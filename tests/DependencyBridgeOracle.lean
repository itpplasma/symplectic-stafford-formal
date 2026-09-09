import SymplecticStafford.Dependency.AlgebraicAnalysisStafford38Bridge

/-!
# Independent oracle for the pinned dependency bridge

The examples below exercise the bridge through concrete fields and the actual
canonical localized module.  They are intentionally independent of the
bridge's implementation: the first constructs a field-level identity and
right-unit clearing data, while the second supplies a genuine minimal
annihilator prime for the regular module over `ℚ`.
-/

namespace SymplecticStafford.DependencyOracle

open SymplecticStafford

example : AlgebraicAnalysis.TwoGeneratorIdentity ℚ := by
  intro d hd
  refine ⟨0, d⁻¹, 0, ?_⟩
  simp [hd]

example : AlgebraicAnalysis.TwoGeneratorIdentity ℚ := by
  apply SymplecticStafford.Dependency.twoGeneratorIdentity_of_rightUnitClearing
    (f := RingHom.id ℚ)
  · intro d hd
    refine ⟨0, d⁻¹, 0, ?_⟩
    simp [hd]
  · intro q hq
    refine ⟨q, 1, ?_, ?_⟩
    · simp
    · simp

example :
    Nontrivial (LocalizedModule (⊥ : Ideal ℚ).primeCompl ℚ) ∧
      IsFiniteLength (Localization (⊥ : Ideal ℚ).primeCompl)
        (LocalizedModule (⊥ : Ideal ℚ).primeCompl ℚ) := by
  have hI : Module.annihilator ℚ ℚ = (⊥ : Ideal ℚ) :=
    Module.annihilator_eq_bot.mpr inferInstance
  apply SymplecticStafford.Dependency.minimalPrime_nontrivial_and_finiteLength
    (P := (⊥ : Ideal ℚ))
  rw [hI, Ideal.minimalPrimes_eq_subsingleton_self]
  simp

end SymplecticStafford.DependencyOracle
