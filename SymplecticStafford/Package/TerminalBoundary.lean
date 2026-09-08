import SymplecticStafford.Package.Opposite
import SymplecticStafford.Semantics.SupportDimension
import SymplecticStafford.Induction.StrongPh

/-!
# M11 terminal boundary

This module records the last algebraic extraction separately from the
construction of a source.  A supplied zero quotient (or, equivalently, a
supplied membership witness for the displayed original right ideal) produces
literal cofactors in the original ring.  The module also packages explicitly
handed right/left hypotheses and their opposite-ring transports.

No source producer, filtered-class theorem, or universal same-divisor theorem
is asserted here.  In particular, every terminal witness below is an input.
-/

namespace SymplecticStafford

universe u

open SymplecticStafford.Induction

section TerminalExtraction

variable {R : Type u} [Ring R]

/-- A direct witness that `1` belongs to the original ordered two-generator
right ideal.  The fields retain the factor order `d * R + (f * d) * S`. -/
structure TerminalMembershipWitness (d f : R) where
  right₁ : R
  right₂ : R
  identity : (1 : R) = d * right₁ + (f * d) * right₂

/-- A terminal witness stated at the quotient boundary.  The ideal is the
canonical original-ring right ideal, not a localization or an opposite. -/
structure TerminalZeroQuotientWitness (d f : R) where
  quotient_zero : QuotientIsZero (twoGeneratedRingRightIdeal d f)

theorem TerminalMembershipWitness.mem
    {d f : R} (w : TerminalMembershipWitness d f) :
    (1 : R) ∈ twoGeneratedRingRightIdeal d f :=
  ⟨w.right₁, w.right₂, w.identity⟩

def TerminalMembershipWitness.toOriginalCofactors
    {d f : R} (w : TerminalMembershipWitness d f) :
    OriginalCofactors d f :=
  ⟨w.right₁, w.right₂, w.identity⟩

theorem TerminalZeroQuotientWitness.one_mem
    {d f : R} (w : TerminalZeroQuotientWitness d f) :
    (1 : R) ∈ twoGeneratedRingRightIdeal d f :=
  (quotientIsZero_iff_one_mem (twoGeneratedRingRightIdeal d f)).mp
    w.quotient_zero

noncomputable def TerminalZeroQuotientWitness.toMembership
    {d f : R} (w : TerminalZeroQuotientWitness d f) :
    TerminalMembershipWitness d f := by
  have hm : ∃ r s : R, (1 : R) = d * r + (f * d) * s := w.one_mem
  let r : R := Classical.choose hm
  have hm' : ∃ s : R, (1 : R) = d * r + (f * d) * s := by
    simpa [r] using Classical.choose_spec hm
  let s : R := Classical.choose hm'
  exact ⟨r, s, Classical.choose_spec hm'⟩

noncomputable def TerminalZeroQuotientWitness.toOriginalCofactors
    {d f : R} (w : TerminalZeroQuotientWitness d f) :
    OriginalCofactors d f :=
  w.toMembership.toOriginalCofactors

/-- The zero-quotient and direct-membership formulations have exactly the
same terminal output, with no hidden existential source. -/
theorem terminal_zero_quotient_iff_membership (d f : R) :
    Nonempty (TerminalZeroQuotientWitness d f) ↔
      Nonempty (TerminalMembershipWitness d f) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.toMembership⟩
  · rintro ⟨w⟩
    exact ⟨⟨(quotientIsZero_iff_one_mem
      (twoGeneratedRingRightIdeal d f)).mpr w.mem⟩⟩

end TerminalExtraction

section HandedPackage

variable {R : Type u} [Ring R]

/-- Explicitly handed terminal hypotheses.  The opposite fields are stored,
rather than inferred by an untracked convention, so package consumers can
inspect the exact direction used. -/
structure TerminalPackage (R : Type u) [Ring R] where
  right : OriginalSameDivisor R
  left : LeftSameDivisorS1 R
  right_opposite : OriginalSameDivisor Rᵐᵒᵖ
  left_opposite : LeftSameDivisorS1 Rᵐᵒᵖ

/-- Compose supplied right and left terminal hypotheses with their explicit
opposite transports. -/
def TerminalPackage.of_handed
    (right : OriginalSameDivisor R)
    (left : LeftSameDivisorS1 R) :
    TerminalPackage R :=
  { right := right
    left := left
    right_opposite := by
      apply (originalSameDivisor_iff (Rᵐᵒᵖ)).mpr
      exact leftSameDivisorS1_opposite (R := R) left
    left_opposite := by
      exact rightSameDivisorS1_opposite (R := R)
        ((originalSameDivisor_iff R).mp right) }

/-- Compose two supplied right-sided terminal hypotheses, one in each ring,
and obtain the two left-sided hypotheses by explicit opposite transport. -/
def TerminalPackage.of_rights
    (right : OriginalSameDivisor R)
    (right_opposite : OriginalSameDivisor Rᵐᵒᵖ) :
    TerminalPackage R :=
  { right := right
    left := by
      exact rightSameDivisorS1_opposite_left (R := R)
        ((originalSameDivisor_iff (Rᵐᵒᵖ)).mp right_opposite)
    right_opposite := right_opposite
    left_opposite := by
      exact rightSameDivisorS1_opposite (R := R)
        ((originalSameDivisor_iff R).mp right) }

theorem TerminalPackage.opposite_right
    (p : TerminalPackage R) :
    OriginalSameDivisor Rᵐᵒᵖ :=
  p.right_opposite

theorem TerminalPackage.opposite_left
    (p : TerminalPackage R) :
    LeftSameDivisorS1 Rᵐᵒᵖ :=
  p.left_opposite

end HandedPackage

end SymplecticStafford

#print axioms SymplecticStafford.TerminalMembershipWitness.toOriginalCofactors
#print axioms SymplecticStafford.TerminalZeroQuotientWitness.toOriginalCofactors
#print axioms SymplecticStafford.TerminalPackage.of_handed
#print axioms SymplecticStafford.TerminalPackage.of_rights
