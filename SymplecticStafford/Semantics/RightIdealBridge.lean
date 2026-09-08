import SymplecticStafford.Semantics.SupportDimension

/-!
# Bridge from the displayed semiring generator to the ring quotient

The paper writes the two-generator object as the set of expressions
`d * r + (f * d) * s`.  `S1Consequences` packages that set as a right ideal
over a semiring, while the quotient API in `Contract` needs additive inverse
closure.  This file records the exact bridge: a semiring right ideal can be
viewed as a ring right ideal only when its carrier is explicitly closed under
negation.  The displayed two-generator carrier has that closure, and its
ring wrapper is definitionally the same carrier as the canonical constructor.

All quotient statements below stay in the original ring and retain the order
`d * r + (f * d) * s`.  In particular, no left ideal or opposite-ring
identification is used.
-/

namespace SymplecticStafford

universe u

section RingBridge

variable {R : Type u} [Ring R]

/-- A semiring right ideal becomes a ring right ideal once negation closure is
supplied.  The closure is a premise, not an inferred property of arbitrary
semiring right ideals. -/
def RightIdeal.toRingRightIdeal (I : RightIdeal (R := R))
    (neg_mem : ∀ {a : R}, a ∈ I → -a ∈ I) :
    RingRightIdeal (R := R) where
  carrier := I.carrier
  zero_mem := I.zero_mem
  add_mem := I.add_mem
  neg_mem := neg_mem
  right_mul_mem := I.right_mul_mem

theorem RightIdeal.mem_toRingRightIdeal_iff
    (I : RightIdeal (R := R))
    (neg_mem : ∀ {a : R}, a ∈ I → -a ∈ I)
    (a : R) :
    a ∈ I.toRingRightIdeal neg_mem ↔ a ∈ I := Iff.rfl

theorem ringRightIdeal_ext_carrier {I J : RingRightIdeal (R := R)}
    (h : I.carrier = J.carrier) : I = J := by
  cases I with
  | mk I hI0 hIadd hIneg hImul =>
    cases J with
    | mk J hJ0 hJadd hJneg hJmul =>
      cases h
      rfl

/-- Negation closure for the displayed two-generator right ideal. -/
theorem twoGeneratedRightIdeal_neg_mem {d f a : R}
    (ha : a ∈ twoGeneratedRightIdeal d f) :
    -a ∈ twoGeneratedRightIdeal d f := by
  rcases ha with ⟨r, s, h⟩
  refine ⟨-r, -s, ?_⟩
  rw [h]
  simp only [mul_neg, neg_add]

/-- The displayed semiring generator viewed through the ring quotient API. -/
def twoGeneratedRightIdealRingBridge (d f : R) :
    RingRightIdeal (R := R) :=
  (twoGeneratedRightIdeal d f).toRingRightIdeal
    (fun {a} ha => twoGeneratedRightIdeal_neg_mem ha)

theorem twoGeneratedRightIdealRingBridge_carrier_eq (d f : R) :
    (twoGeneratedRightIdealRingBridge d f).carrier =
      (twoGeneratedRingRightIdeal d f).carrier := rfl

theorem twoGeneratedRightIdealRingBridge_eq (d f : R) :
    twoGeneratedRightIdealRingBridge d f = twoGeneratedRingRightIdeal d f := by
  apply ringRightIdeal_ext_carrier
  rfl

theorem twoGeneratedRightIdealRingBridge_mem_iff (d f a : R) :
    a ∈ twoGeneratedRightIdealRingBridge d f ↔
      a ∈ twoGeneratedRightIdeal d f := Iff.rfl

theorem twoGeneratedRightIdealRingBridge_mem_iff_coefficients (d f a : R) :
    a ∈ twoGeneratedRightIdealRingBridge d f ↔
      ∃ r s : R, a = d * r + (f * d) * s := by
  exact mem_twoGeneratedRightIdeal_iff d f a

end RingBridge

section QuotientBridge

variable {R : Type u} [Ring R]

/-- The original-ring quotient associated with the displayed generator. -/
abbrev TwoGeneratedRightQuotient (d f : R) :=
  RightQuotient (twoGeneratedRightIdealRingBridge d f)

theorem twoGeneratedRightQuotient_mk_eq_zero_iff_mem (d f a : R) :
    Quotient.mk (rightIdealSetoid (twoGeneratedRightIdealRingBridge d f)) a =
        (0 : TwoGeneratedRightQuotient d f) ↔
      a ∈ twoGeneratedRightIdeal d f := by
  rw [rightQuotient_mk_eq_zero_iff_mem]
  rfl

theorem twoGeneratedRightQuotient_mk_eq_zero_iff_coefficients (d f a : R) :
    Quotient.mk (rightIdealSetoid (twoGeneratedRightIdealRingBridge d f)) a =
        (0 : TwoGeneratedRightQuotient d f) ↔
      ∃ r s : R, a = d * r + (f * d) * s := by
  rw [twoGeneratedRightQuotient_mk_eq_zero_iff_mem]
  exact mem_twoGeneratedRightIdeal_iff d f a

theorem twoGeneratedRightQuotient_isZero_iff_mem_one (d f : R) :
    QuotientIsZero (twoGeneratedRightIdealRingBridge d f) ↔
      (1 : R) ∈ twoGeneratedRightIdeal d f := by
  rw [quotientIsZero_iff_one_mem]
  rfl

theorem twoGeneratedRightQuotient_isZero_iff_certificate (d f : R) :
    QuotientIsZero (twoGeneratedRightIdealRingBridge d f) ↔
      ∃ r s : R, (1 : R) = d * r + (f * d) * s := by
  rw [twoGeneratedRightQuotient_isZero_iff_mem_one]
  exact mem_twoGeneratedRightIdeal_iff d f 1

/-- Right multiplication is well-defined on the displayed quotient, with
the relation written in the original ring. -/
theorem twoGeneratedRightQuotient_action_respects
    {d f a b r : R}
    (h : a - b ∈ twoGeneratedRightIdeal d f) :
    quotientRightAction (twoGeneratedRightIdealRingBridge d f)
        (Quotient.mk (rightIdealSetoid (twoGeneratedRightIdealRingBridge d f)) a) r =
      quotientRightAction (twoGeneratedRightIdealRingBridge d f)
        (Quotient.mk (rightIdealSetoid (twoGeneratedRightIdealRingBridge d f)) b) r := by
  apply quotientRightAction_respects (twoGeneratedRightIdealRingBridge d f)
  exact h

theorem twoGeneratedRightQuotient_action_one
    (d f : R) (q : TwoGeneratedRightQuotient d f) :
    quotientRightAction (twoGeneratedRightIdealRingBridge d f) q 1 = q :=
  quotientRightAction_one (twoGeneratedRightIdealRingBridge d f) q

theorem twoGeneratedRightQuotient_action_mul
    (d f : R) (q : TwoGeneratedRightQuotient d f) (r s : R) :
    quotientRightAction (twoGeneratedRightIdealRingBridge d f)
        (quotientRightAction (twoGeneratedRightIdealRingBridge d f) q r) s =
      quotientRightAction (twoGeneratedRightIdealRingBridge d f) q (r * s) :=
  quotientRightAction_mul (twoGeneratedRightIdealRingBridge d f) q r s

theorem twoGeneratedRightQuotient_action_zero
    (d f : R) (q : TwoGeneratedRightQuotient d f) :
    quotientRightAction (twoGeneratedRightIdealRingBridge d f) q 0 =
      Quotient.mk (rightIdealSetoid (twoGeneratedRightIdealRingBridge d f)) 0 :=
  quotientRightAction_zero (twoGeneratedRightIdealRingBridge d f) q

/-- A certificate is exactly the assertion that the whole displayed quotient
vanishes.  The direction is useful at the terminal boundary; the converse
extracts the original-ring right cofactors. -/
theorem twoGeneratedRightQuotient_certificate_iff_isZero
    (d f : R) :
    (∃ r s : R, (1 : R) = d * r + (f * d) * s) ↔
      QuotientIsZero (twoGeneratedRightIdealRingBridge d f) :=
  (twoGeneratedRightQuotient_isZero_iff_certificate d f).symm

end QuotientBridge

end SymplecticStafford

#print axioms SymplecticStafford.RightIdeal.toRingRightIdeal
#print axioms SymplecticStafford.twoGeneratedRightIdealRingBridge_eq
#print axioms SymplecticStafford.twoGeneratedRightQuotient_action_respects
#print axioms SymplecticStafford.twoGeneratedRightQuotient_certificate_iff_isZero
