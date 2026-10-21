module

public import Mathlib.Tactic
public import Stafford38.Weyl.EulerRemainder
public import SymplecticStafford.Source.WeylHigherDimensionalMonicization

@[expose] public section

/-! Independent oracle for the higher-dimensional Weyl monicization adapter.

The non-scalar test uses the upstream scalar/symplectic dichotomy directly,
rules out its scalar branch from the Weyl commutator, and then reconstructs
the outer monic conclusion.  Thus it does not invoke the adapter theorem
under test.  The final assertion separately checks the original-U scalar
branch; neither assertion claims the unresolved support-vanishing step.
-/

namespace SymplecticStafford.WeylHigherDimensionalMonicizationOracle

open Stafford38.OreIteratedPairStage
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylOuterOreMonic
open Stafford38.WeylPBW
open Stafford38.WeylEulerRemainder
open Stafford38.WeylFiltration
open SymplecticStafford.Source
open Stafford38.OreCoordinateStage
open AlgebraicAnalysis.OreRightQuotient

abbrev W := PresentedWeyl ℚ 2

private theorem momentum_ne_zero :
    presentedMomentum ℚ 1 ≠ 0 := by
  letI : Nontrivial (IteratedPairStage ℚ 0) := by
    change Nontrivial ℚ
    exact Rat.nontrivial
  letI : Nontrivial (IteratedPairStage ℚ 1) := by
    exact normalOreNontrivial (coordinateDerivation (B := IteratedPairStage ℚ 0))
  letI : Nontrivial (IteratedPairStage ℚ 2) := by
    exact normalOreNontrivial (coordinateDerivation (B := IteratedPairStage ℚ 1))
  intro hp
  have hmap : presentedToIterated ℚ 2 (presentedMomentum ℚ 1) = 0 := by
    rw [hp, map_zero]
  have hstage : stageMomentum ℚ 1 = 0 := by
    rw [← presentedToIterated_momentum ℚ 1]
    exact hmap
  have hw := stageMomentum_mul_coordinate ℚ 1
  rw [hstage] at hw
  have h01 : (0 : IteratedPairStage ℚ 2) = 1 := by
    simpa using hw
  exact (zero_ne_one : (0 : IteratedPairStage ℚ 2) ≠ 1) h01

private theorem momentum_not_scalar :
    ¬ ∃ c : ℚ, c ≠ 0 ∧
      presentedMomentum ℚ 1 = algebraMap ℚ W c := by
  letI : Nontrivial (IteratedPairStage ℚ 0) := by
    change Nontrivial ℚ
    exact Rat.nontrivial
  letI : Nontrivial (IteratedPairStage ℚ 1) := by
    exact normalOreNontrivial (coordinateDerivation (B := IteratedPairStage ℚ 0))
  letI : Nontrivial (IteratedPairStage ℚ 2) := by
    exact normalOreNontrivial (coordinateDerivation (B := IteratedPairStage ℚ 1))
  letI : Nontrivial W :=
    Equiv.nontrivial (presentedIteratedEquiv ℚ 2).toEquiv
  rintro ⟨c, -, hc⟩
  have hw := presentedMomentum_mul_coordinate ℚ 1
  rw [hc] at hw
  have hcomm : algebraMap ℚ W c * presentedCoordinate ℚ 1 =
      presentedCoordinate ℚ 1 * algebraMap ℚ W c :=
    Algebra.commutes c _
  rw [hcomm] at hw
  have hzero := congrArg
    (fun z : W => z - presentedCoordinate ℚ 1 * algebraMap ℚ W c) hw
  simpa using hzero

example :
    ∃ (N : ℕ) (d' : W),
      0 < N ∧
        IsPBWMonicAt ℚ (.inr (0 : Fin 2)) N d' ∧
        (presentedOuterPolynomial ℚ 1 d').Monic := by
  rcases scalar_or_normalized_symplectic_image ℚ (Nat.succ_pos 1)
      momentum_ne_zero with hscalar | ⟨N, hN, hchart⟩
  · exact False.elim (momentum_not_scalar hscalar)
  · rcases HasNormalizedSymplecticChart.purePBWCoefficient ℚ hchart with
      ⟨d', hd'⟩
    exact ⟨N, d', hN, hd', presentedOuterPolynomial_monic ℚ 1 N hd'⟩

set_option maxHeartbeats 1000000 in
private theorem newest_momentum_is_degree_one_monic :
    IsPBWMonicAt ℚ (.inr (0 : Fin 2)) 1 (presentedMomentum ℚ 1) := by
  have hpiece : presentedMomentum ℚ 1 ∈ bernsteinPiece ℚ 2 1 := by
    rw [bernsteinPiece, mem_presentedWeightPiece,
      presentedMomentum, presentedNormalFormLinearEquiv_generator]
    intro m hm
    simp only [MvPolynomial.coeff_X', ne_eq, ite_eq_right_iff] at hm
    by_contra hweight
    exact hm (by
      intro h
      subst m
      simp [monomialWeight, bernsteinWeight] at hweight)
  refine ⟨hpiece, ?_⟩
  simp [presentedMomentum, presentedNormalFormLinearEquiv_generator]

example :
    (∃ sigma,
      presentedToIterated ℚ 2 (presentedMomentum ℚ 1) =
          stageMomentum ℚ 1 ^ 1 + sigma ∧
        HasPositiveCoordinateFactor (IteratedPairStage ℚ 1) 1 sigma) ∧
      Nonempty (AssemblyWitness (presentedMomentum ℚ 1)
        (presentedCoordinate ℚ 1)) := by
  exact degree_one_monic_remainder_and_assembly ℚ
    newest_momentum_is_degree_one_monic

example :
    ∃ c : ℚ, c ≠ 0 ∧
      (1 : PresentedWeyl ℚ 2) = algebraMap ℚ (PresentedWeyl ℚ 2) c := by
  exact ⟨1, one_ne_zero, by simp⟩

#print axioms momentum_ne_zero
#print axioms momentum_not_scalar
#print axioms newest_momentum_is_degree_one_monic

end SymplecticStafford.WeylHigherDimensionalMonicizationOracle
