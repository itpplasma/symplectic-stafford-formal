import SymplecticStafford.Package.TerminalObstruction

/- Independent oracle for the M11 boundary: terminal arithmetic can hold while
   the original-U cofactor is false. -/

open SymplecticStafford.Induction

example : StrongPh 0 1 terminalFlatDefect := terminalStrong

example : ∀ f : Nat, ¬ Nonempty (OriginalCofactors (U := Nat) 2 f) :=
  no_original_cofactor_for_two

example :
    ¬ (∀ {d f : Nat} {Ω : List (LocalTest Nat Unit Empty)},
      terminalFlatDefect d f Ω ≤ -1 → Nonempty (OriginalCofactors d f)) :=
  no_zero_extraction_for_terminal_flat_defect

#print axioms terminalStrong
