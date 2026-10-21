module

public import SymplecticStafford.Semantics.Contract
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

/-! Independent concrete checks for the literal certificate API. -/

namespace SymplecticStaffordTest

open SymplecticStafford

example : (2 : ℕ) ∈ twoGeneratedRightIdeal 1 5 := by
  exact ⟨2, 0, by simp⟩

example : ∀ a : ℕ, a ∈ twoGeneratedRightIdeal 1 5 := by
  apply one_certificate_mem_generates_quotient (d := 1) (f := 5) (r := 1) (s := 0)
  simp

example {R : Type} [Ring R] {d f r s : R}
    (h : (1 : R) = d * r + (f * d) * s) (a : R) :
    a = d * (r * a) + (f * d) * (s * a) :=
  certificate_rewrite h a

example {R : Type} [Ring R] {d f r s : R}
    (h : (1 : R) = d * r + (f * d) * s) :
    LeftOppositeCertificate (R := R) (MulOpposite.op d) (MulOpposite.op f)
      (MulOpposite.op (1 : R)) :=
  rightCertificate_opposite h

example : (2 : ℤ) ∈ twoGeneratedRingRightIdeal 1 5 := by
  exact ⟨2, 0, by simp⟩

example (d f : ℤ) :
    (twoGeneratedRingRightIdeal d f).carrier =
      (twoGeneratedRightIdeal d f).carrier :=
  twoGeneratedRingRightIdeal_carrier_eq d f

example {R : Type} [Ring R] (I : RingRightIdeal R) (q : RightQuotient I) :
    quotientRightAction I q 1 = q :=
  quotientRightAction_one I q

example {R : Type} [Ring R] (I : RingRightIdeal R) (q : RightQuotient I)
    (r s : R) :
    quotientRightAction I (quotientRightAction I q r) s =
      quotientRightAction I q (r * s) :=
  quotientRightAction_mul I q r s

example {R : Type} [Ring R] (I : RingRightIdeal R) (q : RightQuotient I) :
    quotientRightAction I q 0 = Quotient.mk (rightIdealSetoid I) 0 :=
  quotientRightAction_zero I q

def sixDimensionalSemanticClass : AdmissibleSymplecticClass ℤ := by
  let Dr : CharacteristicDimensionData ℤ := { charDim := fun _ => 6 }
  let Dl : CharacteristicDimensionData ℤᵐᵒᵖ := { charDim := fun _ => 6 }
  refine
    { noetherian := True
      simple := True
      infiniteDimensional := True
      nonnegativeSeparatedLocallyFiniteFiltration := True
      associatedGradedCommAffineDomain := True
      associatedGradedDimension := 6
      rightCharacteristicDimension := Dr
      leftCharacteristicDimension := Dl
      right_B2 := ?_
      left_B2 := ?_ }
  · intro M _ _ _
    change 2 ≤ 6
    decide
  · intro M _ _ _
    change 2 ≤ 6
    decide

example : sixDimensionalSemanticClass.associatedGradedDimension = 6 := rfl

end SymplecticStaffordTest
