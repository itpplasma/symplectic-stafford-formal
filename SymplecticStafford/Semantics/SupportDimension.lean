import SymplecticStafford.Semantics.Contract
import Mathlib.Order.WithBot

/-!
# Support-dimension boundary for original right quotients

This file gives the small M01 interface needed when the paper's support
argument reaches its terminal boundary.  A dimension is `WithBot Nat`: the
bottom value is the formal `-1` assigned to zero support.  The two links from
dimension to support and from support to the zero object are explicit fields
of a datum.  They are not consequences of a characteristic-support theorem,
and this file does not provide such a theorem.

The quotient API below remains in the original ring and keeps right-sided
factor order.  In particular, zero quotient means `a ∈ I` for the displayed
right ideal; no localization, opposite identification, or same-divisor
existence is smuggled into the boundary.
-/

namespace SymplecticStafford

universe u v

/- The bottom-extended natural numbers are the support-dimension codomain. -/
abbrev SupportDimension := WithBot Nat

section GenericBoundary

variable {X : Type u} {ι : Type v} [Zero X]

/--
An explicit support/dimension boundary for an object `X`.

`dimension = ⊥` is the bottom, or `-1`, case.  The fields deliberately state
the exact hypotheses needed by the terminal argument: no support construction
or zero-detection result is asserted universally here.
-/
structure SupportDimensionBoundary (X : Type u) [Zero X] (ι : Type v) where
  support : Set ι
  dimension : SupportDimension
  dimension_bot_iff_support_empty : dimension = ⊥ ↔ support = ∅
  support_empty_iff_zero : support = ∅ ↔ ∀ x : X, x = 0

/-- Bottom support dimension produces the empty-support conclusion. -/
theorem support_empty_of_dimension_bot
    (D : SupportDimensionBoundary X ι) (hD : D.dimension = ⊥) :
    D.support = ∅ :=
  D.dimension_bot_iff_support_empty.mp hD

/-- Empty support produces the zero-object conclusion under the explicit
support/zero boundary carried by `D`. -/
theorem zero_object_of_support_empty
    (D : SupportDimensionBoundary X ι) (hD : D.support = ∅) :
    ∀ x : X, x = 0 :=
  D.support_empty_iff_zero.mp hD

/-- The terminal support-dimension extraction, with both links visible. -/
theorem zero_object_of_dimension_bot
    (D : SupportDimensionBoundary X ι) (hD : D.dimension = ⊥) :
    ∀ x : X, x = 0 :=
  zero_object_of_support_empty D (support_empty_of_dimension_bot D hD)

/-- A nonzero object cannot have bottom support dimension. -/
theorem dimension_ne_bot_of_exists_ne_zero
    (D : SupportDimensionBoundary X ι)
    (hX : ∃ x : X, x ≠ 0) :
    D.dimension ≠ ⊥ := by
  intro hD
  rcases hX with ⟨x, hx⟩
  exact hx (zero_object_of_dimension_bot D hD x)

end GenericBoundary

section QuotientBoundary

variable {R : Type u} [Ring R]

/- The canonical zero representative of the original right quotient. -/
instance rightQuotientZero (I : RingRightIdeal (R := R)) :
    Zero (RightQuotient I) where
  zero := Quotient.mk (rightIdealSetoid I) 0

/-- A right quotient is zero when every quotient class is its canonical zero
class.  This is intentionally a predicate, not a field on a ring class. -/
def QuotientIsZero (I : RingRightIdeal (R := R)) : Prop :=
  ∀ q : RightQuotient I, q = 0

/-- The quotient class of `a` is zero exactly when `a` belongs to the original
right ideal. -/
theorem rightQuotient_mk_eq_zero_iff_mem
    (I : RingRightIdeal (R := R)) (a : R) :
    Quotient.mk (rightIdealSetoid I) a = (0 : RightQuotient I) ↔ a ∈ I := by
  change Quotient.mk (rightIdealSetoid I) a = Quotient.mk (rightIdealSetoid I) 0 ↔ a ∈ I
  rw [Quotient.eq]
  change a - 0 ∈ I.carrier ↔ a ∈ I.carrier
  simp

/-- The whole quotient is zero exactly when the right ideal contains `1`. -/
theorem quotientIsZero_iff_one_mem
    (I : RingRightIdeal (R := R)) :
    QuotientIsZero I ↔ (1 : R) ∈ I := by
  constructor
  · intro h
    exact (rightQuotient_mk_eq_zero_iff_mem I 1).mp
      (h (Quotient.mk (rightIdealSetoid I) 1))
  · intro h q
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    apply (rightQuotient_mk_eq_zero_iff_mem I a).mpr
    change a ∈ I.carrier
    simpa using I.right_mul_mem (show (1 : R) ∈ I.carrier from h) a

/-- A quotient support datum is the generic boundary specialized to the
original right quotient.  Its zero object is the canonical quotient class. -/
abbrev QuotientSupportDimensionBoundary
    (I : RingRightIdeal (R := R)) (ι : Type v) :=
  SupportDimensionBoundary (RightQuotient I) ι

/-- Bottom support dimension of the quotient forces the quotient to vanish. -/
theorem quotientIsZero_of_dimension_bot
    (I : RingRightIdeal (R := R))
    (D : QuotientSupportDimensionBoundary I ι)
    (hD : D.dimension = ⊥) :
    QuotientIsZero I :=
  zero_object_of_dimension_bot D hD

/-- The quotient's bottom support boundary reaches the concrete original-ring
right-ideal endpoint, while preserving right-sided order. -/
theorem one_mem_of_quotient_dimension_bot
    (I : RingRightIdeal (R := R))
    (D : QuotientSupportDimensionBoundary I ι)
    (hD : D.dimension = ⊥) :
    (1 : R) ∈ I :=
  quotientIsZero_iff_one_mem I |>.mp (quotientIsZero_of_dimension_bot I D hD)

end QuotientBoundary

end SymplecticStafford

#print axioms SymplecticStafford.support_empty_of_dimension_bot
#print axioms SymplecticStafford.zero_object_of_support_empty
#print axioms SymplecticStafford.zero_object_of_dimension_bot
#print axioms SymplecticStafford.rightQuotient_mk_eq_zero_iff_mem
#print axioms SymplecticStafford.quotientIsZero_iff_one_mem
#print axioms SymplecticStafford.one_mem_of_quotient_dimension_bot
