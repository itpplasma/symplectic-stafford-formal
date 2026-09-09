import Stafford38.EvolutionaryCorollary
import SymplecticStafford.Source.Assembly

/-!
# A concrete original-ring calibration for M06

The Stafford38 Weyl presentation is an actual original ring, rather than a
completion or a localization.  This file records the exact same-divisor
certificate shape used by `SymplecticStafford.Source.Assembly`: the source is
the displayed coordinate power and the factors stay in the presented Weyl
ring.  The first theorem is a literal A1 calculation; the second is an
adapter for the finite-potential certificate already proved in Stafford38.
-/

namespace SymplecticStafford.Source

open Stafford38.WeylIteratedEquivalence

universe u

section A1

variable (k : Type u) [Field k]

local notation "W" => PresentedWeyl k 1

/-- The Weyl generators give a nontrivial original-ring certificate for the
divisor `p`: its source is `x`, with the displayed right-factor order. -/
theorem presentedWeyl_A1_source_certificate :
    ∃ R S : W, (1 : W) = presentedMomentum k 0 * R +
      (presentedCoordinate k 0 * presentedMomentum k 0) * S := by
  let x : W := presentedCoordinate k 0
  let p : W := presentedMomentum k 0
  have hw : p * x - x * p = (1 : W) := by
    dsimp [p, x]
    rw [presentedMomentum_mul_coordinate]
    noncomm_ring
  refine ⟨x, -(1 : W), ?_⟩
  dsimp [p, x]
  have hneg : presentedCoordinate k 0 * presentedMomentum k 0 *
      (-(1 : W)) = -(presentedCoordinate k 0 * presentedMomentum k 0) := by
    exact mul_neg_one (presentedCoordinate k 0 * presentedMomentum k 0)
  rw [hneg]
  simpa [p, x, sub_eq_add_neg] using hw.symm

end A1

section FinitePotential

variable (k B : Type*) [Field k] [CharZero k] [Ring B] [Algebra k B]

open scoped TensorProduct

local notation "W" => PresentedWeyl k 1
local notation "D" => B ⊗[k] W
local notation "x" => (Algebra.TensorProduct.includeRight : W →ₐ[k] D)
  (presentedCoordinate k 0)

/-- Adapter from the Stafford38 finite-potential theorem to the exact
original-ring assembly witness consumed by M06.  The divisor equality is
retained as an explicit hypothesis, and the source/cofactor order is literal.
-/
theorem tensorWeyl_original_assembly
    {r : ℕ} (hr : 0 < r) (terms : List (B × ℕ))
    {d : D}
    (hd : d = (Algebra.TensorProduct.includeRight : W →ₐ[k] D)
      (presentedMomentum k 0) ^ r -
      Stafford38.Evolution.potentialSum x
        (terms.map fun t =>
          ((Algebra.TensorProduct.includeLeft : B →ₐ[k] D) t.1, t.2))) :
    Nonempty (AssemblyWitness d (x ^ r)) := by
  obtain ⟨R, S, h⟩ := Stafford38.Evolution.tensorEvolutionaryCorollary
    k B hr terms hd
  exact ⟨⟨R, S, h⟩⟩

end FinitePotential

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.presentedWeyl_A1_source_certificate
#print axioms SymplecticStafford.Source.tensorWeyl_original_assembly
