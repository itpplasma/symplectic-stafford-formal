module

public import SymplecticStafford.Induction.SupportRemovalArithmetic

@[expose] public section

open SymplecticStafford.Induction

abbrev OracleSupport := Fin 3

def oracleRemoval : SupportRemovalArithmetic (α := OracleSupport) 3 1 where
  oldSupport := {0, 1, 2}
  newSupport := {1, 2}
  outputSupport := {1}
  output_subset_old := by decide
  output_subset_new := by decide
  output_strict_old := by decide
  output_strict_new := by decide
  old_bound := by
    norm_num [finiteSupportDefect, defectBound]
    decide
  new_bound := by
    norm_num [finiteSupportDefect, defectBound]
    decide

example :
    finiteSupportDefect oracleRemoval.outputSupport ≤ defectBound 3 (1 + 1) := by
  exact oracleRemoval.output_bound

example : finiteSupportDefect ({1} : Finset OracleSupport) = 0 := by
  norm_num [finiteSupportDefect]

#print axioms oracleRemoval
