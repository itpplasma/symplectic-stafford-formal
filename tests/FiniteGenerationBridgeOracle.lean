import Mathlib.Tactic.NormNum
import SymplecticStafford.Ordered.FiniteGenerationBridge

/-!
Independent oracle for the finite-generation bridge.  The integer instance
supplies an actual finite generator datum for the ordered common-colon ideal;
all support claims remain absent, as required by the interface boundary.
-/

namespace SymplecticStaffordTest.FiniteGenerationBridge

open SymplecticStafford
open SymplecticStafford.Ordered
open scoped BigOperators

theorem integerCommonGenerators_mem :
    ∀ g ∈ ({2} : Finset ℤ), g ∈ commonRightIdeal 2 5 3 := by
  intro g hg
  simp only [Finset.mem_singleton] at hg
  subst g
  refine ⟨1, 0, ?_, ?_⟩
  · exact ⟨0, by simp⟩
  · norm_num

theorem integerCommonSpan_cover :
    (commonRightIdeal 2 5 3).carrier ⊆ finiteRightSpan ({2} : Finset ℤ) := by
  intro x hx
  rcases hx with ⟨r, k, hk, h⟩
  rcases hk with ⟨c, hc⟩
  refine ⟨fun _ => r + 5 * k, ?_⟩
  simp only [Finset.sum_singleton]
  calc
    x = 2 * r + (5 * 2) * k := h
    _ = 2 * (r + 5 * k) := by omega

theorem integerCommonData : FiniteGeneratorData
    (R := ℤ) (commonRightIdeal 2 5 3) :=
  ⟨{2}, integerCommonGenerators_mem, integerCommonSpan_cover⟩

def integerCommonGeneration :
    FiniteRightGeneration (R := ℤ) (commonRightIdeal 2 5 3) where
  generators := {2}
  mem_iff := by
    intro x
    constructor
    · intro hx
      exact integerCommonSpan_cover hx
    · intro hx
      exact finiteRightSpan_subset_of_mem integerCommonGenerators_mem hx

example : Nonempty (FiniteRightGeneration (R := ℤ) (commonRightIdeal 2 5 3)) :=
  ⟨integerCommonGeneration⟩

example : (2 * 7 : ℤ) ∈ commonRightIdeal 2 5 3 := by
  have h := finite_span_mem_of_generator_mem
    (I := commonRightIdeal 2 5 3)
    (gs := ({2} : Finset ℤ)) integerCommonGenerators_mem
    (c := fun _ => 7)
  simpa using h

example : finiteRightSpan ({2} : Finset ℤ) ⊆
    (twoGeneratedRightIdeal 2 (5 + 7 * 3)).carrier := by
  exact common_generator_data_affine_span 2 5 3 7 integerCommonGeneration
    (by intro x; omega)

end SymplecticStaffordTest.FiniteGenerationBridge
