import SymplecticStafford.Semantics.S1Consequences

/-!
# Opposite-ring package boundary

The right-sided certificate in an algebra becomes a left-sided certificate in
the opposite algebra.  A right S1 statement alone therefore does not imply
right S1 for the opposite ring; the latter needs the corresponding left
certificate in the original ring.  This file proves that exact transport and
keeps the handed hypotheses explicit.
-/

namespace SymplecticStafford

universe u

variable {R : Type u} [Semiring R]

/-- Left-sided same-divisor certificates in the original ring. -/
def LeftSameDivisorS1 (R : Type u) [Semiring R] : Prop :=
  ∀ ⦃d : R⦄, d ≠ 0 → ∃ f r s : R, 1 = r * d + s * (d * f)

theorem leftSameDivisorS1_opposite
    (h : LeftSameDivisorS1 (R := R)) :
    SameDivisorS1 (R := Rᵐᵒᵖ) := by
  intro d hd
  have hd' : (MulOpposite.unop d : R) ≠ 0 := by
    intro hzero
    apply hd
    simpa using congrArg MulOpposite.op hzero
  rcases h hd' with ⟨f, r, s, hs⟩
  refine ⟨MulOpposite.op f, MulOpposite.op r, MulOpposite.op s, ?_⟩
  simpa only [MulOpposite.op_one, MulOpposite.op_add, MulOpposite.op_mul,
    MulOpposite.op_unop] using congrArg MulOpposite.op hs

theorem rightSameDivisorS1_opposite
    (h : SameDivisorS1 (R := R)) :
    LeftSameDivisorS1 (R := Rᵐᵒᵖ) := by
  intro d hd
  have hd' : (MulOpposite.unop d : R) ≠ 0 := by
    intro hzero
    apply hd
    simpa using congrArg MulOpposite.op hzero
  rcases h hd' with ⟨f, r, s, hs⟩
  refine ⟨MulOpposite.op f, MulOpposite.op r, MulOpposite.op s, ?_⟩
  simpa only [MulOpposite.op_one, MulOpposite.op_add, MulOpposite.op_mul,
    MulOpposite.op_unop] using congrArg MulOpposite.op hs

theorem rightSameDivisorS1_opposite_left
    (h : SameDivisorS1 (R := Rᵐᵒᵖ)) :
    LeftSameDivisorS1 (R := R) := by
  intro d hd
  have hd' : (MulOpposite.op d : Rᵐᵒᵖ) ≠ 0 := by
    intro hzero
    apply hd
    simpa using congrArg MulOpposite.unop hzero
  rcases h hd' with ⟨f, r, s, hs⟩
  refine ⟨MulOpposite.unop f, MulOpposite.unop r, MulOpposite.unop s, ?_⟩
  simpa only [MulOpposite.unop_one, MulOpposite.unop_add,
    MulOpposite.unop_mul, MulOpposite.unop_op] using
    congrArg MulOpposite.unop hs

theorem leftSameDivisorS1_opposite_left
    (h : LeftSameDivisorS1 (R := Rᵐᵒᵖ)) :
    SameDivisorS1 (R := R) := by
  intro d hd
  have hd' : (MulOpposite.op d : Rᵐᵒᵖ) ≠ 0 := by
    intro hzero
    apply hd
    simpa using congrArg MulOpposite.unop hzero
  rcases h hd' with ⟨f, r, s, hs⟩
  refine ⟨MulOpposite.unop f, MulOpposite.unop r, MulOpposite.unop s, ?_⟩
  simpa only [MulOpposite.unop_one, MulOpposite.unop_add,
    MulOpposite.unop_mul, MulOpposite.unop_op] using
    congrArg MulOpposite.unop hs

theorem leftSameDivisorS1_iff_rightSameDivisorS1_opposite :
    LeftSameDivisorS1 (R := R) ↔
      SameDivisorS1 (R := Rᵐᵒᵖ) := by
  constructor
  · exact leftSameDivisorS1_opposite
  · exact rightSameDivisorS1_opposite_left

theorem rightSameDivisorS1_iff_leftSameDivisorS1_opposite :
    SameDivisorS1 (R := R) ↔
      LeftSameDivisorS1 (R := Rᵐᵒᵖ) := by
  constructor
  · exact rightSameDivisorS1_opposite
  · exact leftSameDivisorS1_opposite_left

end SymplecticStafford

#print axioms SymplecticStafford.leftSameDivisorS1_opposite
#print axioms SymplecticStafford.rightSameDivisorS1_opposite
#print axioms SymplecticStafford.rightSameDivisorS1_opposite_left
#print axioms SymplecticStafford.leftSameDivisorS1_opposite_left
