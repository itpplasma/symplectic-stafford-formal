module

public import AlgebraicAnalysis.RingTheory.TwoGeneratorIdentity

@[expose] public section

/-!
# Same-divisor statement

The target identity is kept in the exact noncommutative order used by the
paper: `d` is the first factor of the first product and the middle factor of
the second product.
-/

namespace SymplecticStafford

universe u

/-- The ordered same-divisor identity targeted by this project. -/
abbrev SameDivisorIdentity (R : Type u) [Ring R] : Prop :=
  AlgebraicAnalysis.TwoGeneratorIdentity R

/-- A unit divisor has the target certificate, as a basic sanity check. -/
theorem certificate_of_unit {R : Type u} [Ring R] {d : R} (hd : IsUnit d) :
    ∃ F r s : R, (1 : R) = d * r + F * d * s := by
  refine ⟨0, (↑(hd.unit⁻¹) : R), 0, ?_⟩
  have h : d * (↑(hd.unit⁻¹) : R) = 1 := by
    simpa [hd.unit_spec] using hd.unit.val_inv
  simp [h]

#print axioms certificate_of_unit

end SymplecticStafford
