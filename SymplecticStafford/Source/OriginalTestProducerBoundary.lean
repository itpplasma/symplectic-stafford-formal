module

public import Mathlib.Tactic
public import SymplecticStafford.Source.OriginalTestContract

@[expose] public section

/-!
# Exact boundary of the abstract original-test producer

`OriginalLocalTest` deliberately leaves `generation` as a proposition supplied
by the caller.  Its admissibility predicate checks the localization/module
labels, divisor, offset, and nonzero tail, but it does not require any source
to pass that proposition.  Consequently the unconditional
`OriginalFiniteTestProducer` cannot be proved from the current contract.

This file records that obstruction with a concrete model over `ℕ`.  All
metadata fields are inhabited and the right tail is nonzero, while the local
generation predicate is nonempty (it accepts exactly zero), but the selected
affine coset `1 + ℤ * 2` contains no zero.  The result is a negative boundary
theorem, not a replacement source theorem: a future M06 producer must add an
actual finite-length/LLD bridge relating its generation predicate to the source
pencil.
-/

namespace SymplecticStafford.Source

abbrev BoundaryU := ℕ

/-- An admissible local test whose generation assertion misses one affine coset.

The `Unit` fields show that the obstruction is not caused by an empty
localization or cyclic-module carrier. -/
def impossibleOriginalTest :
    OriginalLocalTest BoundaryU Unit Unit where
  targetDivisor := 1
  localization := ()
  cyclicFiniteModule := ()
  canonicalGenerator := ()
  rightTail := 1
  offset := 17
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := by decide
  generation := fun source _ _ => source = 0

theorem impossibleOriginalTest_admissible :
    impossibleOriginalTest.Admissible (1 : BoundaryU) := by
  exact OriginalLocalTest.admissible_of_fields
    (1 : BoundaryU) impossibleOriginalTest rfl

theorem impossibleOriginalTest_list_admissible :
    AdmissibleOriginalTestList (1 : BoundaryU)
      [impossibleOriginalTest] := by
  exact admissibleOriginalTestList_cons
    impossibleOriginalTest_admissible
    (admissibleOriginalTestList_nil (1 : BoundaryU))

theorem no_impossible_affine_source :
    ¬ Nonempty (OriginalAffineSourceWitness
      (LocalizationData := Unit) (CyclicModuleData := Unit)
      (1 : BoundaryU) 1 2 [impossibleOriginalTest]) := by
  rintro ⟨w⟩
  have hpass := w.tests_pass impossibleOriginalTest (by simp)
  have hzero : w.source = 0 := hpass
  have hEq := w.source_eq
  rw [hzero] at hEq
  have hne : 1 + w.H * 2 ≠ (0 : BoundaryU) := by simp
  exact hne hEq.symm

/-!
The contradiction already occurs at one nonzero divisor, one nonzero affine
tail, and one admissible test.  Thus the current universal producer type is
strictly stronger than the fields of `OriginalLocalTest`; no choice of an
original-ring multiplier can be extracted without an additional bridge.
-/
theorem no_originalFiniteTestProducer_of_current_contract :
    ¬ Nonempty (OriginalFiniteTestProducer BoundaryU Unit Unit) := by
  rintro ⟨producer⟩
  have witness := producer
    (1 : BoundaryU) one_ne_zero
    1 2 (by norm_num)
    [impossibleOriginalTest] impossibleOriginalTest_list_admissible
  exact no_impossible_affine_source ⟨witness⟩

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.impossibleOriginalTest_admissible
#print axioms SymplecticStafford.Source.no_impossible_affine_source
#print axioms SymplecticStafford.Source.no_originalFiniteTestProducer_of_current_contract
