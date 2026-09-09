import Stafford38.Weyl.EulerRemainder

/-!
# Higher-dimensional Weyl monicization

The iterated Weyl/Ore tower gives a concrete, original-ring monicization
interface in every positive rank.  The scalar/symplectic dichotomy is applied
to an arbitrary nonzero presented Weyl element; the normalized image is then
monic for the newest outer Ore variable.

This is deliberately only the division input.  The outer remainder theorem
does not by itself prove that the canonical two-generator right ideal is the
whole ring: that last implication is the separate support-vanishing step.
-/

namespace SymplecticStafford.Source

open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylMonicNormalization
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylOuterOreMonic
open Stafford38.WeylEulerRemainder
open Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage

noncomputable section

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- Every nonzero positive-rank Weyl element is either scalar or has a
symplectically normalized representative that is monic in the newest outer
momentum.  All objects remain in the presented original Weyl ring. -/
theorem exists_scalar_or_outer_monicization
    {n : ℕ} (d : PresentedWeyl k (n + 1)) (hd : d ≠ 0) :
    (∃ c : k, c ≠ 0 ∧ d = algebraMap k (PresentedWeyl k (n + 1)) c) ∨
      ∃ (N : ℕ) (d' : PresentedWeyl k (n + 1)),
        0 < N ∧
          IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d' ∧
          (presentedOuterPolynomial k n d').Monic := by
  rcases scalar_or_normalized_symplectic_image k (Nat.succ_pos n) hd with
    hscalar | hchart
  · exact Or.inl hscalar
  · rcases hchart with ⟨N, hN, hchart⟩
    rcases HasNormalizedSymplecticChart.purePBWCoefficient k hchart with
      ⟨d', hd'⟩
    exact Or.inr ⟨N, d', hN, hd', presentedOuterPolynomial_monic k n N hd'⟩

/-- The monic representative has the exact positive-coordinate remainder
factorization supplied by the iterated noncommutative division algorithm. -/
theorem outer_monicization_remainder_factor
    {n N : ℕ} {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ∃ sigma,
      presentedToIterated k (n + 1) d = stageMomentum k n ^ N + sigma ∧
        HasPositiveCoordinateFactor (IteratedPairStage k n) N sigma := by
  let sigma :=
    presentedToIterated k (n + 1) d - stageMomentum k n ^ N
  have hdecomp : presentedToIterated k (n + 1) d =
      stageMomentum k n ^ N + sigma := by
    simp [sigma]
  refine ⟨sigma, hdecomp, ?_⟩
  exact presentedRemainder_hasPositiveCoordinateFactor k n N hd

#print axioms exists_scalar_or_outer_monicization
#print axioms outer_monicization_remainder_factor

end
end SymplecticStafford.Source
