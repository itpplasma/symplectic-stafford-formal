import Mathlib.Tactic.NormNum
import SymplecticStafford.Ordered.SupportUnion

/-!
Independent consumers for the M08 finite-generator/support-union interface.
The integer instance checks the ordered common-colon construction concretely;
the support statement is intentionally consumed only from an explicit
hypothesis.
-/

namespace SymplecticStaffordTest.SupportUnion

open SymplecticStafford
open SymplecticStafford.Ordered
open scoped BigOperators

def integerCommonGenerators : FiniteRightGeneration
    (R := ℤ) (commonRightIdeal 2 5 3) where
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

example : finiteRightSpan integerCommonGenerators.generators ⊆
    (twoGeneratedRightIdeal 2 (5 + 7 * 3)).carrier := by
  exact finite_commonIdeal_subset_affine 2 5 3 7 integerCommonGenerators
    (by intro x; omega)

example : FiniteRightClearance (MonoidHom.id ℤ) 2 ({2, 3} : Finset ℤ) := by
  apply finiteRightClearance_of_pointwise
  intro x hx
  refine ⟨0, x, ?_⟩
  simp

def emptySupport : RightIdeal (R := ℤ) → Set Unit := fun _ => ∅

example : supportUnionInput emptySupport 2 5 3 1 := by
  apply supportUnionInput_of_relation_and_support emptySupport 2 5 3 1
  · exact ⟨5, by norm_num⟩
  · intro z hz
    exact hz.elim

example : emptySupport (commonRightIdeal 2 5 3) ⊆
    emptySupport (twoGeneratedRightIdeal 2 5) ∪
      emptySupport (twoGeneratedRightIdeal (2 * 1) 3) := by
  apply support_union_of_input emptySupport 2 5 3 1
  apply supportUnionInput_of_relation_and_support emptySupport 2 5 3 1
  · exact ⟨5, by norm_num⟩
  · intro z hz
    exact hz.elim

end SymplecticStaffordTest.SupportUnion
