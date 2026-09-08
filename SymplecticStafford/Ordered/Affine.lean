import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-! Ordered affine identities, with all noncommutative factor order explicit. -/

namespace SymplecticStafford.Ordered

variable {R : Type*} [Ring R]

/-- Expansion of an affine source; the parameter is not moved through the
operator, divisor, or cofactor. -/
theorem affine_source_expand (d F G r s t : R) :
    d * r + (F + t * G) * d * s =
      d * r + F * d * s + t * (G * d * s) := by
  noncomm_ring

/-- The expanded affine identity implies the same ordered certificate. -/
theorem affine_certificate_contract (d F G r s t : R)
    (h : (1 : R) = d * r + F * d * s + t * (G * d * s)) :
    (1 : R) = d * r + (F + t * G) * d * s := by
  rw [← affine_source_expand d F G r s t] at h
  exact h

/-- The source expansion in the opposite-handed display convention. -/
theorem affine_opposite_expand (d F G r s t : R) :
    d * r + (F + t * G) * d * s =
      d * r + F * d * s + t * G * d * s := by
  noncomm_ring

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.affine_source_expand
#print axioms SymplecticStafford.Ordered.affine_certificate_contract
#print axioms SymplecticStafford.Ordered.affine_opposite_expand
