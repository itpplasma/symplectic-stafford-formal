module

public import SymplecticStafford.FiniteLength.FilteredLocalizedGradedBridge

@[expose] public section

/-!
Independent trust-disabled checks for the conditional Part I.5 bridge.
These examples instantiate only elementary identity/local one-step data; they
are not an instance of the universal filtered localization theorem.
-/

namespace SymplecticStaffordTest.FilteredLocalizedGradedBridge

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.FiniteLength
open SymplecticStafford.FiniteLength.RightModuleFiltrationData

def topRingFiltration : RingFiltrationData (R := ℚ) where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

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
  exhaustive := by
    intro x
    exact ⟨1, by simp⟩
  bottom := by simp

def ringIdentity :
    RingAssociatedGradedLocalization topRingFiltration topRingFiltration where
  layerEquiv := fun n => AddEquiv.refl _
  map_compatible := True
  multiplication_compatible := True

def moduleIdentity :
    ModuleAssociatedGradedLocalization oneStepFiltration oneStepFiltration where
  layerEquiv := fun n => LinearEquiv.refl (ℚᵐᵒᵖ) _
  scalar_action_compatible := True

example (n : ℕ) :
    ringIdentity.layerEquiv n
        (SymplecticStafford.Filtered.RingFiltrationData.associatedClass
          topRingFiltration n 1 (by simp [topRingFiltration])) =
      SymplecticStafford.Filtered.RingFiltrationData.associatedClass
        topRingFiltration n 1 (by simp [topRingFiltration]) := by
  rfl

example (n : ℕ) :
    moduleIdentity.layerEquiv n
      (associatedClass oneStepFiltration n 0 (by simp)) =
      associatedClass oneStepFiltration n 0 (by simp) := by
  simp [moduleIdentity]

example {N : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)} {x : (ℚᵐᵒᵖ) ⧸ N} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ hnx : x ∈ (oneStepFiltration.inducedQuotient N).carrier n,
      (oneStepFiltration.inducedQuotient N).associatedClass n x hnx ≠ 0 :=
  oneStepFiltration.nonzero_quotient_has_nonzero_associatedClass N hx

example {F : RightModuleFiltrationData (R := ℚ) (M := ℚᵐᵒᵖ)}
    {N : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)} (E : ExactAssociatedGraded F N) :
    Function.Exact (E.inclusion 0) (E.projection 0) :=
  exact_at E 0

def oneStepLocalizedChain :
    StrictLocalizedGradedChain (R := ℚ) (L := ℚᵐᵒᵖ) 1 where
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp [Fin.last]
  step := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    have hspan : (ℚᵐᵒᵖ ∙ (1 : ℚᵐᵒᵖ)) = (⊤ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)) := by
      apply le_antisymm le_top
      intro y hy
      have hy' : y = y • (1 : ℚᵐᵒᵖ) := by simp
      rw [hy']
      exact Submodule.smul_mem _ y (Submodule.subset_span (by simp))
    simpa [hspan] using
      (Submodule.covBy_span_singleton_sup
        (K := ℚᵐᵒᵖ) (x := (1 : ℚᵐᵒᵖ)) (s := (⊥ : Submodule ℚᵐᵒᵖ (ℚᵐᵒᵖ)))
          (by simp))

def oneStepSourceChain :
    StrictFilteredChain oneStepFiltration 1 where
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp [Fin.last]
  contained := by intro i; simp [oneStepFiltration]
  strict := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp

def oneStepTransfer :
    FilteredChainTransfer (R := ℚ) (M := ℚᵐᵒᵖ) (L := ℚᵐᵒᵖ)
      oneStepFiltration 1 where
  source := oneStepSourceChain
  target := oneStepLocalizedChain
  strict_survival := by
    intro i hi
    exact (oneStepLocalizedChain.step i).lt

example : IsFiniteLength ℚᵐᵒᵖ (ℚᵐᵒᵖ) ∧
    Module.length ℚᵐᵒᵖ (ℚᵐᵒᵖ) = 1 :=
  transfer_finite_length_bound oneStepTransfer

example (p : Ideal ℚ) [p.IsPrime]
    (w : HomogeneousAtPrimeWitness p (fun _ => Set.univ)) :
    (LocalizedModule.mkLinearMap p.primeCompl ℚ) w.value ≠ 0 :=
  w.survives_atPrime

end SymplecticStaffordTest.FilteredLocalizedGradedBridge

#print axioms SymplecticStaffordTest.FilteredLocalizedGradedBridge.oneStepTransfer
