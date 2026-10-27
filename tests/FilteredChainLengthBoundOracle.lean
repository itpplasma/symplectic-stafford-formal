module

public import SymplecticStafford.FiniteLength.FilteredChainLengthBound

@[expose] public section

/-! Independent trust-disabled consumers for the quantitative M05 bound. -/

namespace SymplecticStaffordTest.FilteredChainLengthBound

open SymplecticStafford.Filtered
open SymplecticStafford.FiniteLength
open SymplecticStafford.FiniteLength.RightModuleFiltrationData

def oneStepFiltration :
    RightModuleFiltrationData (R := ℚ) (M := ℚᵐᵒᵖ) where
  carrier n := if n = 0 then ⊥ else ⊤
  mono := by
    intro i j hij x hx
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simpa [hi, hj] using hx
      · simp [hj]
    · have hj : j ≠ 0 := by
        intro hj0
        exact hi (Nat.eq_zero_of_le_zero (hj0 ▸ hij))
      simp [hj]
  exhaustive := by intro x; exact ⟨1, by simp⟩
  bottom := by simp

def oneStepTarget :
    StrictLocalizedGradedChain (R := ℚ) (L := ℚᵐᵒᵖ) 1 where
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp [Fin.last]
  step := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    have hspan : (ℚᵐᵒᵖ ∙ (1 : ℚᵐᵒᵖ)) =
        (⊤ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)) := by
      apply le_antisymm le_top
      intro y hy
      have hy' : y = y • (1 : ℚᵐᵒᵖ) := by simp
      rw [hy']
      exact Submodule.smul_mem _ y (Submodule.subset_span (by simp))
    simpa [hspan] using
      (Submodule.covBy_span_singleton_sup
        (K := ℚᵐᵒᵖ) (x := (1 : ℚᵐᵒᵖ))
        (s := (⊥ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ))) (by simp))

def oneStepSource : StrictFilteredChain oneStepFiltration 1 where
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp [Fin.last]
  contained := by intro i; simp [oneStepFiltration]
  strict := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp

def boundedBelow : NatFiltration (R := ℚᵐᵒᵖ) (M := ℚᵐᵒᵖ) where
  carrier n := if n = 0 then ⊥ else ⊤
  mono := by
    intro i j hij x hx
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simpa [hi, hj] using hx
      · simp [hj]
    · have hj : j ≠ 0 := by
        intro hj0
        exact hi (Nat.eq_zero_of_le_zero (hj0 ▸ hij))
      simp [hj]
  exhaustive := by intro x; exact ⟨1, by simp⟩
  bottom := by simp

example : ∃ k : ℕ, ¬ (∀ x : ℚᵐᵒᵖ, x ∈ (⊤ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)) →
    x ∈ boundedBelow.carrier k →
      ∃ y : ℚᵐᵒᵖ, y ∈ (⊥ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)) ∧
        y ∈ boundedBelow.carrier k ∧ x - y ∈ previousLayer boundedBelow k) := by
  have hnot := strict_inclusion_has_strict_layer boundedBelow
    (A := (⊥ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)))
    (B := (⊤ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ))) bot_le (by simp)
  classical
  by_contra h
  push_neg at h
  exact hnot h

example (E : ExactAssociatedGraded oneStepFiltration (⊥ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)))
    (hfactor : Nontrivial (chainQuotient oneStepSource (⟨0, by decide⟩ : Fin 1)))
    (extension : GradedFilteredExtension
      (R := ℚᵐᵒᵖ) (M := ℚᵐᵒᵖ) (G := ℚᵐᵒᵖ)) :
    (1 : ℕ∞) ≤ Module.length ℚᵐᵒᵖ (ℚᵐᵒᵖ) := by
  let Q : FilteredChainLengthCertificate oneStepFiltration 1 := {
    transfer := {
      source := oneStepSource
      target := oneStepTarget
      strict_survival := by
        intro i hi
        exact (oneStepTarget.step i).lt }
    boundedBelow := boundedBelow
    exactGr := fun i => by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [oneStepSource] using E
    nonzeroFactor := fun i => by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [oneStepSource] using hfactor }
  exact (quantitative_length_bound Q extension).1

example
    (F : SymplecticStafford.Filtered.FiniteFilteredModule
      (R := ℚᵐᵒᵖ) (M := ℚᵐᵒᵖ))
    (A : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)) (hA : A < (⊤ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ))) :
    ∃ k : Fin F.height, ¬ Function.Surjective
      (SymplecticStafford.Filtered.StrictFiniteGradedChain.layerMap F A k) :=
  finite_filtered_layer_exists F A hA

end SymplecticStaffordTest.FilteredChainLengthBound

#print axioms SymplecticStaffordTest.FilteredChainLengthBound.oneStepTarget
