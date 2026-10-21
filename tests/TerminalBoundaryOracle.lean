module

public import SymplecticStafford.Package.TerminalBoundary
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Independent checks for the M11 terminal boundary. -/

namespace SymplecticStafford.TerminalBoundaryOracle

open SymplecticStafford.Induction

noncomputable section

def direct : TerminalMembershipWitness (1 : ℤ) 0 where
  right₁ := 1
  right₂ := 0
  identity := by norm_num

example : (1 : ℤ) ∈ twoGeneratedRingRightIdeal 1 0 :=
  direct.mem

example : OriginalCofactors (1 : ℤ) 0 :=
  direct.toOriginalCofactors

def quotient : TerminalZeroQuotientWitness (1 : ℤ) 0 where
  quotient_zero :=
    (quotientIsZero_iff_one_mem (twoGeneratedRingRightIdeal 1 0)).mpr
      direct.mem

example : TerminalMembershipWitness (1 : ℤ) 0 :=
  quotient.toMembership

example : OriginalCofactors (1 : ℤ) 0 :=
  quotient.toOriginalCofactors

def vacuousRight : OriginalSameDivisor (ZMod 1) := by
  intro d hd
  exact False.elim (hd (Subsingleton.elim d 0))

def vacuousLeft : LeftSameDivisorS1 (ZMod 1) := by
  intro d hd
  exact False.elim (hd (Subsingleton.elim d 0))

def handed : TerminalPackage (ZMod 1) :=
  TerminalPackage.of_handed vacuousRight vacuousLeft

example : OriginalSameDivisor ((ZMod 1)ᵐᵒᵖ) :=
  handed.opposite_right

example : LeftSameDivisorS1 ((ZMod 1)ᵐᵒᵖ) :=
  handed.opposite_left

def rightBoth : TerminalPackage (ZMod 1) :=
  TerminalPackage.of_rights vacuousRight
    (by
      intro d hd
      exact False.elim (hd (Subsingleton.elim d 0)))

example : LeftSameDivisorS1 (ZMod 1) :=
  rightBoth.left

#print axioms SymplecticStafford.TerminalMembershipWitness.toOriginalCofactors
#print axioms SymplecticStafford.TerminalZeroQuotientWitness.toOriginalCofactors
#print axioms SymplecticStafford.TerminalPackage.of_handed
#print axioms SymplecticStafford.TerminalPackage.of_rights

end
end SymplecticStafford.TerminalBoundaryOracle
