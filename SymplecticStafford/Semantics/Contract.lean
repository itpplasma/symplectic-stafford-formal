import SymplecticStafford.Semantics.S1Consequences
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Phase-I semantic contract

This module fixes the endpoint semantics used by the paper.  In particular,
the divisor lives in the original ring `R`; no localization, completion, or
matrix enlargement occurs in these definitions.  Right ideals are closed
under multiplication on the right, and opposite transport reverses every
factor in a certificate.

The filtered/symplectic class below records hypotheses only.  It deliberately
contains no source-existence or same-divisor field: those are conclusions of
the proof, not assumptions of the semantic contract.
-/

namespace SymplecticStafford

universe u

section Quotient

variable {R : Type u} [Ring R]

/- A ring right ideal has the additive inverse closure needed to form the
   ordinary additive quotient.  The earlier `RightIdeal` interface is kept
   semiring-general; this ring-specific interface is the quotient API. -/
structure RingRightIdeal (R : Type u) [Ring R] where
  carrier : Set R
  zero_mem : 0 ∈ carrier
  add_mem : ∀ {a b : R}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  neg_mem : ∀ {a : R}, a ∈ carrier → -a ∈ carrier
  right_mul_mem : ∀ {a : R}, a ∈ carrier → ∀ r : R, a * r ∈ carrier

instance : Membership R (RingRightIdeal (R := R)) :=
  ⟨fun I a => a ∈ I.carrier⟩

/- The ring-specific constructor is intentionally separate from the semiring
   interface: it adds additive inverses, while retaining exactly the same
   ordered carrier `d * r + (f * d) * s`. -/
def twoGeneratedRingRightIdeal (d f : R) : RingRightIdeal (R := R) where
  carrier := {a | ∃ r s : R, a = d * r + (f * d) * s}
  zero_mem := by
    exact ⟨0, 0, by simp⟩
  add_mem := by
    rintro a b ⟨r₁, s₁, ha⟩ ⟨r₂, s₂, hb⟩
    refine ⟨r₁ + r₂, s₁ + s₂, ?_⟩
    rw [ha, hb]
    simp only [mul_add, add_assoc, add_left_comm]
  neg_mem := by
    rintro a ⟨r, s, ha⟩
    refine ⟨-r, -s, ?_⟩
    rw [ha]
    simp only [mul_neg, neg_add]
  right_mul_mem := by
    rintro a ⟨r, s, ha⟩ q
    refine ⟨r * q, s * q, ?_⟩
    rw [ha]
    simp only [add_mul, mul_assoc]

theorem mem_twoGeneratedRingRightIdeal_iff (d f a : R) :
    a ∈ twoGeneratedRingRightIdeal d f ↔
      ∃ r s : R, a = d * r + (f * d) * s := Iff.rfl

theorem twoGeneratedRingRightIdeal_carrier_eq (d f : R) :
    (twoGeneratedRingRightIdeal d f).carrier =
      (twoGeneratedRightIdeal d f).carrier := rfl

def rightIdealRelation (I : RingRightIdeal (R := R)) (a b : R) : Prop := a - b ∈ I

theorem rightIdealRelation_refl (I : RingRightIdeal (R := R)) (a : R) :
    rightIdealRelation I a a := by
  change a - a ∈ I.carrier
  simpa using I.zero_mem

theorem rightIdealRelation_symm (I : RingRightIdeal (R := R)) {a b : R}
    (h : rightIdealRelation I a b) : rightIdealRelation I b a := by
  change a - b ∈ I.carrier at h
  change b - a ∈ I.carrier
  simpa [neg_sub] using I.neg_mem h

theorem rightIdealRelation_trans (I : RingRightIdeal (R := R)) {a b c : R}
    (hab : rightIdealRelation I a b) (hbc : rightIdealRelation I b c) :
    rightIdealRelation I a c := by
  change a - c ∈ I.carrier
  change a - b ∈ I.carrier at hab
  change b - c ∈ I.carrier at hbc
  rw [show a - c = (a - b) + (b - c) by
    simp [sub_eq_add_neg, add_assoc]]
  exact I.add_mem hab hbc

def rightIdealSetoid (I : RingRightIdeal (R := R)) : Setoid R where
  r := rightIdealRelation I
  iseqv := ⟨rightIdealRelation_refl I, rightIdealRelation_symm I,
    rightIdealRelation_trans I⟩

/-- The additive quotient by a right ideal, with representatives retained
    only through the displayed relation. -/
abbrev RightQuotient (I : RingRightIdeal (R := R)) := Quotient (rightIdealSetoid I)

theorem rightIdealRelation_mul_right (I : RingRightIdeal (R := R))
    {a b : R} (h : rightIdealRelation I a b) (r : R) :
    rightIdealRelation I (a * r) (b * r) := by
  change a * r - b * r ∈ I.carrier
  change a - b ∈ I.carrier at h
  rw [show a * r - b * r = (a - b) * r by
    simp [sub_eq_add_neg, add_mul]]
  exact I.right_mul_mem h r

/- The quotient right action is exposed as a function rather than silently
   using a left-module quotient.  `Quotient.lift` is justified by the right
   ideal closure theorem immediately above. -/
def quotientRightAction (I : RingRightIdeal (R := R))
    (q : RightQuotient I) (r : R) : RightQuotient I :=
  Quotient.lift (fun a : R => Quotient.mk (rightIdealSetoid I) (a * r))
    (by
      intro a b h
      apply Quotient.sound
      exact rightIdealRelation_mul_right I h r) q

theorem quotientRightAction_mk (I : RingRightIdeal (R := R)) (a r : R) :
    quotientRightAction I (Quotient.mk (rightIdealSetoid I) a) r =
      Quotient.mk (rightIdealSetoid I) (a * r) := rfl

theorem quotientRightAction_respects (I : RingRightIdeal (R := R))
    {a b : R} (h : rightIdealRelation I a b) (r : R) :
    quotientRightAction I (Quotient.mk (rightIdealSetoid I) a) r =
      quotientRightAction I (Quotient.mk (rightIdealSetoid I) b) r := by
  rw [quotientRightAction_mk, quotientRightAction_mk]
  exact Quotient.sound (rightIdealRelation_mul_right I h r)

theorem quotientRightAction_one (I : RingRightIdeal (R := R))
    (q : RightQuotient I) :
    quotientRightAction I q 1 = q := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change Quotient.mk (rightIdealSetoid I) (a * 1) =
      Quotient.mk (rightIdealSetoid I) a
    simp

theorem quotientRightAction_mul (I : RingRightIdeal (R := R))
    (q : RightQuotient I) (r s : R) :
    quotientRightAction I (quotientRightAction I q r) s =
      quotientRightAction I q (r * s) := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change Quotient.mk (rightIdealSetoid I) ((a * r) * s) =
      Quotient.mk (rightIdealSetoid I) (a * (r * s))
    rw [mul_assoc]

theorem quotientRightAction_zero (I : RingRightIdeal (R := R))
    (q : RightQuotient I) :
    quotientRightAction I q 0 = Quotient.mk (rightIdealSetoid I) 0 := by
  induction q using Quotient.inductionOn with
  | _ a =>
    change Quotient.mk (rightIdealSetoid I) (a * 0) =
      Quotient.mk (rightIdealSetoid I) 0
    simp

end Quotient

section Admissible

variable {R : Type u} [Ring R]

/- Characteristic dimension is supplied as data because its construction is
   route-dependent.  The B2 field quantifies over actual finitely generated
   right modules and is not a disguised S1 assumption. -/
structure CharacteristicDimensionData (R : Type u) [Ring R] where
  charDim : ∀ (M : Type u) [AddCommMonoid M] [Module Rᵐᵒᵖ M], Nat

def B2 (D : CharacteristicDimensionData R) : Prop :=
  ∀ (M : Type u) [AddCommMonoid M] [Module Rᵐᵒᵖ M],
    Module.Finite Rᵐᵒᵖ M → 2 ≤ D.charDim M

/- These are the exact structural labels needed by the fourfold target.  The
   fields remain explicit so a later wrapper must derive them from geometry;
   no field states the terminal certificate. -/
structure AdmissibleSymplecticClass (R : Type u) [Ring R] where
  noetherian : Prop
  simple : Prop
  infiniteDimensional : Prop
  nonnegativeSeparatedLocallyFiniteFiltration : Prop
  associatedGradedCommAffineDomain : Prop
  /- The semantic contract is dimension-parametric.  Fourfold hypotheses,
     when needed, belong to a separate target wrapper rather than this class. -/
  associatedGradedDimension : Nat
  rightCharacteristicDimension : CharacteristicDimensionData R
  leftCharacteristicDimension : CharacteristicDimensionData Rᵐᵒᵖ
  right_B2 : B2 rightCharacteristicDimension
  left_B2 : B2 leftCharacteristicDimension

end Admissible

section SameDivisor

variable {R : Type u} [Ring R]

/- A named endpoint proposition makes the original carrier explicit while
   preserving the canonical right-certificate proposition. -/
def OriginalSameDivisor (R : Type u) [Ring R] : Prop :=
  ∀ ⦃d : R⦄, d ≠ 0 → ∃ F r s : R, (1 : R) = d * r + (F * d) * s

theorem originalSameDivisor_iff (R : Type u) [Ring R] :
    OriginalSameDivisor R ↔ SameDivisorS1 (R := R) := Iff.rfl

theorem original_membership_extraction (d f a : R) :
    a ∈ twoGeneratedRightIdeal d f ↔
      ∃ r s : R, a = d * r + (f * d) * s :=
  mem_twoGeneratedRightIdeal_iff d f a

theorem original_one_generation (d f : R) :
    (1 : R) ∈ twoGeneratedRightIdeal d f ↔
      ∀ a : R, a ∈ twoGeneratedRightIdeal d f :=
  one_mem_iff_generates_right_ideal d f

end SameDivisor

end SymplecticStafford

#print axioms SymplecticStafford.rightIdealRelation_mul_right
#print axioms SymplecticStafford.quotientRightAction_respects
#print axioms SymplecticStafford.original_membership_extraction
#print axioms SymplecticStafford.original_one_generation
