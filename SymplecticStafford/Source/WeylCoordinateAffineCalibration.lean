import Stafford38.EvolutionaryCorollary
import Stafford38.Weyl.MonicNormalization
import SymplecticStafford.Source.WeylA1Calibration
import SymplecticStafford.Source.WeylHigherDimensionalEvolutionary
import SymplecticStafford.Source.WeylHigherDimensionalMonicization

/-!
# Coordinate-affine higher-rank Weyl calibration

Let `x₀,p₀` denote the newest presented Weyl pair in `A_(n+1)`.  If the
displayed coefficients come from the recursively embedded old `A_n`, then

    d = x₀ - ∑ aⱼ p₀^j

has the literal original-ring certificate with source `p₀`.  The coefficients
need only commute with the newest momentum; they may be mutually
noncommuting.  This is the degree-one opposite-coordinate branch, kept
separate from the evolutionary `p₀^r - ∑ aⱼ x₀^j` adapter and from arbitrary
monicization.  No localization, tensor identification, or universal S1
claim is made.
-/

namespace SymplecticStafford.Source

open Stafford38
open Stafford38.Evolution
open Stafford38.WeylIteratedEquivalence

universe u

variable (k : Type u) [Field k]

/-- Every displayed coordinate-affine divisor in the original presented
`A_(n+1)` has a literal same-divisor certificate with source `p₀`. -/
theorem presentedWeyl_coordinate_affine
    (n : ℕ) (terms : List (PresentedWeyl k n × ℕ))
    {d : PresentedWeyl k (n + 1)}
    (hd : d = presentedCoordinate k n -
      potentialSum (presentedMomentum k n)
        (terms.map fun t =>
          (previousWeylEmbedding k n t.1, t.2))) :
    ∃ R S : PresentedWeyl k (n + 1),
      1 = d * R + presentedMomentum k n * d * S := by
  let lifted : List (PresentedWeyl k (n + 1) × ℕ) :=
    terms.map fun t => (previousWeylEmbedding k n t.1, t.2)
  have hcoeff : ∀ t ∈ lifted,
      t.1 * presentedMomentum k n = presentedMomentum k n * t.1 := by
    rintro t ht
    rcases List.mem_map.mp ht with ⟨⟨b, j⟩, _, rfl⟩
    exact (presentedMomentum_commutes_previous k n b).symm
  have htail : potentialSum (presentedMomentum k n) lifted *
      presentedMomentum k n = presentedMomentum k n *
      potentialSum (presentedMomentum k n) lifted := by
    simpa using (commute_potentialSum_x_pow hcoeff 1)
  let A := potentialSum (presentedMomentum k n) lifted
  have htail' : A * presentedMomentum k n = presentedMomentum k n * A := by
    simpa [A] using htail
  have hw : presentedMomentum k n * presentedCoordinate k n =
      presentedCoordinate k n * presentedMomentum k n + 1 :=
    presentedMomentum_mul_coordinate k n
  refine ⟨0 - presentedMomentum k n, 1, ?_⟩
  rw [hd]
  change 1 = (presentedCoordinate k n - A) *
      (0 - presentedMomentum k n) +
      presentedMomentum k n * (presentedCoordinate k n - A) * 1
  simp only [sub_mul, mul_sub, zero_mul, mul_zero, one_mul, mul_one]
  rw [htail', hw]
  noncomm_ring

#print axioms presentedWeyl_coordinate_affine

end SymplecticStafford.Source
