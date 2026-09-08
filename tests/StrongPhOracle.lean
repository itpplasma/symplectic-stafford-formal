import SymplecticStafford.Induction.StrongPh
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Independent oracle checks for the M09--M10 contract

These checks instantiate the data types and consume the conditional
interfaces.  The PUnit model makes the producer calls vacuous (there is no
nonzero divisor), so it cannot be mistaken for evidence of the paper's
universal theorem.
-/

namespace SymplecticStafford.StrongPhOracle

open SymplecticStafford.Induction

def natTest : LocalTest Nat Unit Unit where
  targetDivisor := 1
  localization := ()
  cyclicModule := ()
  canonicalGenerator := ()
  rightTail := 1
  offset := 0
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := by decide
  generation := fun _ => True

example : natTest.Admissible 1 := by
  exact LocalTest.admissible_of_fields 1 natTest rfl

example : AdmissibleTestList 1 [natTest] := by
  exact admissibleTestList_cons (LocalTest.admissible_of_fields 1 natTest rfl)
    (admissibleTestList_nil 1)

example (a : Nat) (ha : a ≠ 0) (H : Nat) :
    (homogeneousAffine a ha).member (H * a) :=
  homogeneousAffine_member a ha H

example (D : Nat) : defectBound D (D + 1) = -1 :=
  defectBound_terminal D

/- A subsingleton semiring is used only to replay the plumbing of the
   successor and termination interfaces. -/
abbrev U := ZMod 1

def defect : U → U → List (LocalTest U U U) → Int :=
  fun _ _ _ => 0

def lower : StrongPh 1 0 defect := by
  intro d hd
  exact False.elim (hd (Subsingleton.elim d 0))

def parameters : CentralParameters U U where
  embed := fun scalar => scalar
  central := by intros; exact mul_comm _ _

def successorRule : SuccessorRule parameters Unit 1 0 defect lower := by
  intro d hd A Ω hΩ
  exact False.elim (hd (Subsingleton.elim d 0))

example : StrongPh 1 1 defect :=
  strongPh_succ parameters Unit successorRule

def terminalDefect : U → U → List (LocalTest U U U) → Int :=
  fun _ _ _ => 0

def terminalStrong : StrongPh 1 2 terminalDefect := by
  intro d hd A Ω hΩ
  exact False.elim (hd (Subsingleton.elim d 0))

def termination : TerminationInterface 1 terminalDefect where
  zero_extraction := by
    intro d f Ω h
    simp [terminalDefect] at h

example (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U U U))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d (terminalStrong d hd A Ω hΩ).source :=
  terminal_extraction termination terminalStrong d hd A Ω hΩ

end SymplecticStafford.StrongPhOracle
