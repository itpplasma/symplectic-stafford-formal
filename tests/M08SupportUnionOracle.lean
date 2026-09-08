import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import SymplecticStafford.Ordered.M08SupportUnion

/-!
Independent oracle for the finite-generator characteristic-support union.
The empty support is only a concrete support model for the interface; the
finite-generator cover, branch exclusion, auxiliary relation, and ordered
pencil identity are all supplied and checked independently here.
-/

namespace SymplecticStaffordTest.M08SupportUnion

open SymplecticStafford
open SymplecticStafford.Ordered
open scoped BigOperators

def integerCommonGeneration : FiniteRightGeneration (R := ℤ)
    (commonRightIdeal 2 5 3) where
  generators := {2}
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases hx with ⟨r, k, hk, h⟩
      rcases hk with ⟨c, hc⟩
      refine ⟨fun _ => r + 5 * k, ?_⟩
      simp only [Finset.sum_singleton]
      calc
        x = 2 * r + (5 * 2) * k := h
        _ = 2 * (r + 5 * k) := by omega
    · intro hx
      rcases hx with ⟨c, hc⟩
      refine ⟨c 2, 0, ?_, ?_⟩
      · exact ⟨0, by simp⟩
      · simpa [Finset.sum_singleton] using hc

def emptySupport : RightIdeal (R := ℤ) → Set Unit := fun _ => ∅

def integerSupportHypothesis :
    CharacteristicSupportBranchHypothesis emptySupport 2 5 3 1
      integerCommonGeneration where
  generator_cover := by
    intro x hx
    exact hx.elim
  outside_branches_excludes_generator := by
    intro x g hg ha hrel h₁ h₂
    exact h₁.elim

def integerAuxiliaryRelation : AuxiliaryDivisorRelation (R := ℤ) 2 5 3 1 :=
  ⟨5, by norm_num⟩

example : emptySupport (commonRightIdeal 2 5 3) ⊆
    emptySupport (twoGeneratedRightIdeal 2 5) ∪
      emptySupport (twoGeneratedRightIdeal (2 * 1) 3) := by
  exact support_union_of_finite_generators emptySupport 2 5 3 1
    integerCommonGeneration integerAuxiliaryRelation integerSupportHypothesis
    (by intro t y; ring)

example : ∃ c : ℤ,
    (3 : ℤ) * 2 * 4 = 2 * c ∧
      5 * 2 * 4 = 2 * (-7 * c) + (5 + 7 * 3) * 2 * 4 := by
  exact common_colon_pencil_certificate 2 5 3 4 7
    (⟨12, by norm_num⟩) (by intro y; omega)

example :
    (emptySupport (commonRightIdeal 2 5 3) ⊆
      emptySupport (twoGeneratedRightIdeal 2 5) ∪
        emptySupport (twoGeneratedRightIdeal (2 * 1) 3)) ∧
      ∀ k : ℤ, k ∈ commonColon 2 3 →
        ∀ t : ℤ, (∀ y : ℤ, t * y = y * t) →
          ∃ c : ℤ,
            3 * 2 * k = 2 * c ∧
              5 * 2 * k = 2 * (-t * c) + (5 + t * 3) * 2 * k := by
  constructor
  · exact support_union_of_finite_generators emptySupport 2 5 3 1
      integerCommonGeneration integerAuxiliaryRelation integerSupportHypothesis
      (by intro t y; ring)
  · intro k hk t ht
    exact common_colon_pencil_certificate 2 5 3 k t hk ht

end SymplecticStaffordTest.M08SupportUnion
