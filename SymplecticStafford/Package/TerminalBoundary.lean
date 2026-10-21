module

public import SymplecticStafford.Package.Opposite
public import SymplecticStafford.Semantics.SupportDimension
public import SymplecticStafford.Induction.StrongPh

@[expose] public section

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

universe u v w v₂ w₂

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

section TerminalAssembly

variable {U : Type u} [Ring U]

/- The terminal extraction theorem is useful only after its output is
   assembled into the endpoint proposition.  Choosing the homogeneous affine
   source space with tail `1` is legal because the empty test list is
   admissible; the actual source may still depend on `d`.  In particular this
   theorem does not assert that the source is fixed, localized, or nonzero. -/
theorem terminal_sameDivisor
    {D : Nat} {T : Type v} {V : Type w}
    {defect : U → U → List (LocalTest U T V) → Int}
    (termination : TerminationInterface D defect)
    (terminal : StrongPh D (D + 1) defect) :
    OriginalSameDivisor U := by
  intro d hd
  let A : AffineSource U := homogeneousAffine d hd
  let Ω : List (LocalTest U T V) := []
  have hΩ : AdmissibleTestList d Ω := by
    exact admissibleTestList_nil d
  have c : OriginalCofactors d
      (terminal d hd A Ω hΩ).source :=
    terminal_extraction termination terminal d hd A Ω hΩ
  exact ⟨(terminal d hd A Ω hΩ).source, c.R, c.S, c.identity⟩

end TerminalAssembly

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

/- Build the two-sided package directly from endpoint data on the original
   ring and on its opposite.  The two endpoint contracts are intentionally
   independent: automatic transport supplies only the corresponding left
   statements, not the missing right statement on the opposite ring. -/
theorem TerminalPackage.of_terminal_endpoints
    {T : Type v} {V : Type w}
    {T' : Type v₂} {V' : Type w₂}
    {D D' : Nat}
    {defect : R → R → List (LocalTest R T V) → Int}
    {defect' : Rᵐᵒᵖ → Rᵐᵒᵖ → List (LocalTest Rᵐᵒᵖ T' V') → Int}
    (termination : TerminationInterface (U := R) D defect)
    (terminal : StrongPh (U := R) D (D + 1) defect)
    (termination' : TerminationInterface (U := Rᵐᵒᵖ) D' defect')
    (terminal' : StrongPh (U := Rᵐᵒᵖ) D' (D' + 1) defect') :
    TerminalPackage R := by
  apply TerminalPackage.of_rights
  · exact terminal_sameDivisor termination terminal
  · exact terminal_sameDivisor termination' terminal'

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
#print axioms SymplecticStafford.terminal_sameDivisor
#print axioms SymplecticStafford.TerminalPackage.of_handed
#print axioms SymplecticStafford.TerminalPackage.of_rights
#print axioms SymplecticStafford.TerminalPackage.of_terminal_endpoints
