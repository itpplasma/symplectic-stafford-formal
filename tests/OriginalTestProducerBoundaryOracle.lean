module

public import Mathlib.Tactic
public import SymplecticStafford.Source.OriginalTestProducerBoundary

@[expose] public section

/-!
# Independent oracle for the M06 producer boundary

The oracle checks both halves of the boundary: the concrete test is
admissible with a nonzero tail, and no affine source witness or universal
producer exists for it.  It therefore guards against accidentally reading
admissibility as a hidden generation theorem.
-/

namespace SymplecticStafford.OriginalTestProducerBoundaryOracle

open SymplecticStafford.Source

example : impossibleOriginalTest.rightTail = (1 : ℕ) := by rfl

example : impossibleOriginalTest.rightTail ≠ 0 :=
  impossibleOriginalTest.rightTail_nonzero

example : impossibleOriginalTest.offset = 17 := by rfl

example : impossibleOriginalTest.Admissible (1 : ℕ) :=
  impossibleOriginalTest_admissible

example : AdmissibleOriginalTestList (1 : ℕ)
    [impossibleOriginalTest] :=
  impossibleOriginalTest_list_admissible

example : ¬ Nonempty (OriginalAffineSourceWitness
    (LocalizationData := Unit) (CyclicModuleData := Unit)
    (1 : ℕ) 1 2 [impossibleOriginalTest]) :=
  no_impossible_affine_source

example : ¬ Nonempty (OriginalFiniteTestProducer ℕ Unit Unit) :=
  no_originalFiniteTestProducer_of_current_contract

end SymplecticStafford.OriginalTestProducerBoundaryOracle

#print axioms SymplecticStafford.Source.no_impossible_affine_source
