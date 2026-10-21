module

public import Mathlib.Tactic
public import Stafford38.Weyl.IteratedEquivalence
public import SymplecticStafford.Source.WeylA1Calibration

@[expose] public section

/-! Independent literal oracle for the A1 calibration.

The oracle proves the same certificate directly from the Weyl commutator; it
does not invoke the adapter theorem under test.  Thus the check exercises the
original ring, the source `x`, and the right-factor order independently.
-/

namespace SymplecticStafford.WeylA1CalibrationOracle

open SymplecticStafford.Source
open Stafford38.WeylIteratedEquivalence

universe u

variable (k : Type u) [Field k]

local notation "W" => PresentedWeyl k 1

theorem literal_A1_certificate :
    ∃ R S : W, (1 : W) = presentedMomentum k 0 * R +
      (presentedCoordinate k 0 * presentedMomentum k 0) * S := by
  refine ⟨presentedCoordinate k 0, -(1 : W), ?_⟩
  have hcomm := presentedMomentum_mul_coordinate k 0
  have hdiff : presentedMomentum k 0 * presentedCoordinate k 0 -
      presentedCoordinate k 0 * presentedMomentum k 0 = (1 : W) := by
    rw [hcomm]
    noncomm_ring
  have hneg : presentedCoordinate k 0 * presentedMomentum k 0 *
      (-(1 : W)) = -(presentedCoordinate k 0 * presentedMomentum k 0) := by
    exact mul_neg_one (presentedCoordinate k 0 * presentedMomentum k 0)
  rw [hneg]
  simpa [sub_eq_add_neg] using hdiff.symm

example : Nonempty (AssemblyWitness
    (presentedMomentum k 0) (presentedCoordinate k 0)) := by
  obtain ⟨R, S, h⟩ := literal_A1_certificate k
  exact ⟨⟨R, S, h⟩⟩

#print axioms literal_A1_certificate

end SymplecticStafford.WeylA1CalibrationOracle
