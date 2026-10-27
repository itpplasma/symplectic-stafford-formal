module

public import SymplecticStafford.Package.TerminalBoundary
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Independent `--trust=0` checks for the M11 terminal assembly bridge. -/

namespace SymplecticStafford.M11PackageTerminalAssemblyOracle

open SymplecticStafford.Induction

def defect : (ZMod 1) → (ZMod 1) →
    List (LocalTest (ZMod 1) Unit Empty) → Int :=
  fun _ _ _ => -2

def terminal : StrongPh (U := ZMod 1) 0 1 defect := by
  intro d hd A Ω hΩ
  refine {
    H := 0
    source := A.B
    source_eq := by simp
    defect_bound := by norm_num [defect, defectBound]
    tests_pass := ?_ }
  intro t ht
  exact nomatch t.cyclicModule

def termination : TerminationInterface (U := ZMod 1) 0 defect := by
  refine { zero_extraction := ?_ }
  intro d f Ω h
  refine ⟨0, 0, ?_⟩
  exact Subsingleton.elim _ _

def defect' : (ZMod 1)ᵐᵒᵖ → (ZMod 1)ᵐᵒᵖ →
    List (LocalTest (ZMod 1)ᵐᵒᵖ Unit Empty) → Int :=
  fun _ _ _ => -2

def terminal' : StrongPh (U := (ZMod 1)ᵐᵒᵖ) 0 1 defect' := by
  intro d hd A Ω hΩ
  refine {
    H := 0
    source := A.B
    source_eq := by simp
    defect_bound := by norm_num [defect', defectBound]
    tests_pass := ?_ }
  intro t ht
  exact nomatch t.cyclicModule

def termination' : TerminationInterface (U := (ZMod 1)ᵐᵒᵖ) 0 defect' := by
  refine { zero_extraction := ?_ }
  intro d f Ω h
  refine ⟨0, 0, ?_⟩
  exact Subsingleton.elim _ _

example : OriginalSameDivisor (ZMod 1) :=
  SymplecticStafford.terminal_sameDivisor termination terminal

example : TerminalPackage (ZMod 1) :=
  TerminalPackage.of_terminal_endpoints termination terminal termination' terminal'

example : SameDivisorS1 (R := (ZMod 1)) ↔
    LeftSameDivisorS1 (R := (ZMod 1)ᵐᵒᵖ) :=
  SymplecticStafford.rightSameDivisorS1_iff_leftSameDivisorS1_opposite

example : LeftSameDivisorS1 (R := (ZMod 1)) ↔
    SameDivisorS1 (R := (ZMod 1)ᵐᵒᵖ) :=
  SymplecticStafford.leftSameDivisorS1_iff_rightSameDivisorS1_opposite

#print axioms SymplecticStafford.terminal_sameDivisor
#print axioms SymplecticStafford.rightSameDivisorS1_iff_leftSameDivisorS1_opposite

end SymplecticStafford.M11PackageTerminalAssemblyOracle
