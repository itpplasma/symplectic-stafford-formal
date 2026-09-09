import SymplecticStafford.Ordered.ActualM08Producer
import Mathlib.Tactic

/-!
Independent executable consumers for the actual M08 finite-generation
construction.  The first example asks Mathlib's right-Noetherian instance for
an automatically constructed witness; the remaining examples check the
literal original-ring pencil certificates on an explicit integer instance.
-/

namespace SymplecticStaffordTest.ActualM08Producer

open SymplecticStafford
open SymplecticStafford.Ordered

noncomputable section

local instance finiteZMod5 : Finite (ZMod 5) := Finite.of_fintype _
local instance noetherianZMod5 : IsNoetherian (ZMod 5)ᵐᵒᵖ (ZMod 5) :=
  isNoetherian_of_finite (ZMod 5)ᵐᵒᵖ (ZMod 5)

example : Nonempty (FiniteRightGeneration (R := ZMod 5)
    (commonRightIdeal 2 1 3)) := by
  exact finiteCommonRightGeneration_of_rightNoetherian 2 1 3

noncomputable def witness : FiniteRightGeneration (R := ZMod 5)
    (commonRightIdeal 2 1 3) :=
  Classical.choice
    (finiteCommonRightGeneration_of_rightNoetherian 2 1 3)

example : ∀ x : ZMod 5, x ∈ commonRightIdeal 2 1 3 ↔
    x ∈ finiteRightSpan witness.generators := by
  intro x
  exact (witness.mem_iff x)

/- An explicit colon witness lets the oracle exercise the paper's indexed
   expansion of J, rather than only the abstract Noetherian generator. -/
def integerColonGeneration : FiniteRightGeneration (R := ℤ)
    (commonColonRightIdeal 2 3) where
  generators := {1}
  mem_iff := by
    intro x
    constructor
    · intro hx
      refine ⟨fun _ => x, ?_⟩
      simp [Finset.sum_singleton]
    · intro hx
      rcases hx with ⟨c, hc⟩
      refine ⟨3 * x, ?_⟩
      rw [hc]
      ring

example (x : ℤ) : x ∈ commonIdeal 2 5 3 ↔
    ∃ r : ℤ, ∃ c : ℤ → ℤ,
      x = 2 * r + ∑ k ∈ integerColonGeneration.generators,
        (5 * 2) * k * c k := by
  constructor
  · exact commonIdeal_mem_from_colon_generators 2 5 3
      integerColonGeneration
  · exact commonIdeal_of_colon_generator_expansion 2 5 3
      integerColonGeneration

example : ∀ k ∈ integerColonGeneration.generators, ∃ c : ℤ,
    3 * 2 * k = 2 * c ∧
      5 * 2 * k = 2 * (-7 * c) + (5 + 7 * 3) * 2 * k := by
  intro k hk
  exact finite_colon_generators_have_pencil_certificates 2 5 3 7
    integerColonGeneration (by intro t; omega) k hk

example : commonIdeal (2 : ZMod 5) 1 3 ⊆
    (twoGeneratedRightIdeal 2 (1 + 4 * 3)).carrier := by
  exact finite_commonIdeal_is_contained_in_every_affine_ideal 2 1 3 4
    witness (by intro t; ring)

example (g : ZMod 5) (hg : g ∈ witness.generators) :
    ∃ r s : ZMod 5, g = 2 * r + (1 + 4 * 3) * 2 * s := by
  exact finite_commonIdeal_generators_have_affine_certificates 2 1 3 4
    witness (by intro t; ring) g hg

example :
    (2 : ZMod 5) * 4 + (1 + 4 * 3) * 2 * 1 = 4 := by decide

end

end SymplecticStaffordTest.ActualM08Producer

#print axioms SymplecticStaffordTest.ActualM08Producer.witness
