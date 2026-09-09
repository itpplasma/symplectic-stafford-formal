import Mathlib.Tactic
import Stafford38.Weyl.EulerRemainder
import SymplecticStafford.Source.WeylHigherDimensionalArbitraryMonic

/-!
# Independent oracle for arbitrary outer-monic division

This test does not call the source wrapper.  It invokes the upstream generic
Ore division theorem on a concrete rank-two Weyl tower, then transports its
identity through the checked presentation equivalence and checks the original
ring cofactors and the finite remainder bound.
-/

namespace SymplecticStafford.WeylHigherDimensionalArbitraryMonicOracle

noncomputable section

open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightQuotient
open Stafford38.OreCoordinateStage
open Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage
open Stafford38.WeylIteratedEquivalence

abbrev W := PresentedWeyl ℚ 2
abbrev C := CoordinateStage (B := IteratedPairStage ℚ 1)
abbrev D : OreDivisionDerivation C := coordinateDerivation

private theorem stage_one_nontrivial : Nontrivial (IteratedPairStage ℚ 1) := by
  letI : Nontrivial (IteratedPairStage ℚ 0) := by
    change Nontrivial ℚ
    exact Rat.nontrivial
  exact normalOreNontrivial (coordinateDerivation (B := IteratedPairStage ℚ 0))

private theorem outer_monic :
    (Polynomial.X ^ 2 + Polynomial.C (1 : C)).Monic := by
  exact Polynomial.monic_X_pow_add_C (n := 2) (a := (1 : C)) (by norm_num)

theorem oracle_original_ring_division (d : W) :
    ∃ q r : W,
      d =
          iteratedToPresented ℚ 2 (normalForm D
            (Polynomial.X ^ 2 + Polynomial.C (1 : C))) * q + r ∧
        (r = 0 ∨ ∃ r₀ : Polynomial C,
          r = iteratedToPresented ℚ 2 (normalForm D r₀) ∧
          r₀.natDegree < (Polynomial.X ^ 2 + Polynomial.C (1 : C)).natDegree) := by
  letI : Nontrivial (IteratedPairStage ℚ 1) := stage_one_nontrivial
  obtain ⟨p, hp⟩ := normalForm_surjective D (presentedToIterated ℚ 2 d)
  obtain ⟨q₀, r₀, hdiv, hrem⟩ :=
    right_division_exists D (Polynomial.X ^ 2 + Polynomial.C (1 : C)) p
      outer_monic
  let q : W := iteratedToPresented ℚ 2 (normalForm D q₀)
  let r : W := iteratedToPresented ℚ 2 (normalForm D r₀)
  refine ⟨q, r, ?_, ?_⟩
  · have hdivN : presentedToIterated ℚ 2 d =
        normalForm D (rightMul D
          (Polynomial.X ^ 2 + Polynomial.C (1 : C)) q₀) +
          normalForm D r₀ := by
      rw [← hp, hdiv, normalForm_add]
    have hdiv' := congrArg (iteratedToPresented ℚ 2) hdivN
    have hleft : iteratedToPresented ℚ 2 (presentedToIterated ℚ 2 d) = d := by
      exact DFunLike.congr_fun
        (iteratedToPresented_comp_presentedToIterated ℚ 2) d
    have hsum := (iteratedToPresented ℚ 2).map_add
      (normalForm D (rightMul D
        (Polynomial.X ^ 2 + Polynomial.C (1 : C)) q₀)) (normalForm D r₀)
    have hdiv'' : d =
        iteratedToPresented ℚ 2 (normalForm D (rightMul D
          (Polynomial.X ^ 2 + Polynomial.C (1 : C)) q₀)) +
          iteratedToPresented ℚ 2 (normalForm D r₀) := by
      calc
        d = iteratedToPresented ℚ 2 (presentedToIterated ℚ 2 d) := hleft.symm
        _ = iteratedToPresented ℚ 2 (normalForm D (rightMul D
              (Polynomial.X ^ 2 + Polynomial.C (1 : C)) q₀) +
              normalForm D r₀) := hdiv'
        _ = _ := hsum
    have hprod : iteratedToPresented ℚ 2 (normalForm D (rightMul D
          (Polynomial.X ^ 2 + Polynomial.C (1 : C)) q₀)) =
        iteratedToPresented ℚ 2 (normalForm D
          (Polynomial.X ^ 2 + Polynomial.C (1 : C))) *
          iteratedToPresented ℚ 2 (normalForm D q₀) := by
      rw [normalForm_mul]
      exact (iteratedToPresented ℚ 2).map_mul _ _
    rw [hprod] at hdiv''
    simpa [q, r] using hdiv''
  · rcases hrem with hzero | hsmall
    · apply Or.inl
      dsimp [r]
      rw [hzero, normalForm_zero]
      exact RingHom.map_zero (iteratedToPresented ℚ 2).toRingHom
    · exact Or.inr ⟨r₀, rfl, hsmall⟩

#print axioms outer_monic
#print axioms oracle_original_ring_division

end
end SymplecticStafford.WeylHigherDimensionalArbitraryMonicOracle
