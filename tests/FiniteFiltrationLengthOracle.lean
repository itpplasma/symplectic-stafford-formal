import Mathlib.LinearAlgebra.Pi
import SymplecticStafford.Filtered.FiniteFiltrationLength

namespace SymplecticStafford.Filtered

theorem finiteFiltrationLength_Q2_oracle :
    IsFiniteLength ℚ (Fin 2 → ℚ) ∧
      ∃ F : FiniteFilteredModule (R := ℚ) (M := (Fin 2 → ℚ)),
        F.carrier 1 ≠ (⊥ : Submodule ℚ (Fin 2 → ℚ)) ∧
          F.carrier 1 < (⊤ : Submodule ℚ (Fin 2 → ℚ)) := by
  let eval1 : (Fin 2 → ℚ) →ₗ[ℚ] ℚ := LinearMap.proj 1
  let A : Submodule ℚ (Fin 2 → ℚ) := eval1.ker
  have hAnonzero : A ≠ (⊥ : Submodule ℚ (Fin 2 → ℚ)) := by
    intro hbot
    let e0 : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0
    have he0 : e0 ∈ A := by
      change eval1 e0 = 0
      simp [eval1, e0]
    have he0bot : e0 ∈ (⊥ : Submodule ℚ (Fin 2 → ℚ)) := by
      rw [← hbot]
      exact he0
    have he0zero : e0 = 0 := by
      simpa using he0bot
    have he0one : e0 0 = 1 := by
      simp [e0]
    rw [he0zero] at he0one
    simpa using he0one
  have hAproper : A < (⊤ : Submodule ℚ (Fin 2 → ℚ)) := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    let e1 : Fin 2 → ℚ := fun i => if i = 1 then 1 else 0
    have he1 : e1 ∈ A := by
      rw [htop]
      trivial
    have heval : eval1 e1 = 0 := he1
    have heval' : eval1 e1 = 1 := by
      simp [eval1, e1]
    rw [heval'] at heval
    exact one_ne_zero heval
  let F : FiniteFilteredModule (R := ℚ) (M := (Fin 2 → ℚ)) :=
    { height := 2
      carrier := fun n => if n = 0 then ⊤ else if n = 1 then A else ⊥
      exhaustive := by simp
      descending := by
        intro n
        by_cases hn : n = 0
        · subst n
          simp
        · by_cases hn1 : n = 1
          · subst n
            exact bot_le
          · simp [hn, hn1]
      separated := by simp }
  have hFproper : F.carrier 1 < (⊤ : Submodule ℚ (Fin 2 → ℚ)) := by
    simpa [F] using hAproper
  have hFnonzero : F.carrier 1 ≠ (⊥ : Submodule ℚ (Fin 2 → ℚ)) := by
    simpa [F] using hAnonzero
  refine ⟨?_, ⟨F, hFnonzero, hFproper⟩⟩
  apply F.isFiniteLength_of_layers
  intro k
  fin_cases k
  · rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, inferInstance⟩
  · rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨inferInstance, inferInstance⟩

#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.isFiniteLength_of_layers
#print axioms finiteFiltrationLength_Q2_oracle

end SymplecticStafford.Filtered
