import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import SymplecticStafford.Source.OriginalTestContract

/-!
# Independent oracle for the original-`U` local-test contract

The concrete `ZMod 2` example checks that offsets and nonzero right tails are
actually consumed by the generation predicate, and that a supplied tested
source extracts to the existing assembly certificate.  It does not instantiate
the universally quantified producer contract.
-/

namespace SymplecticStafford.OriginalTestContractOracle

open SymplecticStafford.Source

abbrev U := ZMod 2

def localTest : OriginalLocalTest U Unit Unit where
  targetDivisor := 1
  localization := ()
  cyclicFiniteModule := ()
  canonicalGenerator := ()
  rightTail := 1
  offset := 3
  localization_spec := True
  localization_spec_proof := True.intro
  finite_length_cyclic_spec := True
  finite_length_cyclic_proof := True.intro
  canonical_generator_spec := True
  canonical_generator_spec_proof := True.intro
  rightTail_nonzero := one_ne_zero
  generation := fun source offset tail =>
    source = 1 ∧ offset = 3 ∧ tail = 1

example : localTest.Admissible 1 :=
  OriginalLocalTest.admissible_of_fields 1 localTest rfl

example : AdmissibleOriginalTestList 1 [localTest] :=
  admissibleOriginalTestList_cons
    (OriginalLocalTest.admissible_of_fields 1 localTest rfl)
    (admissibleOriginalTestList_nil 1)

def localSource : OriginalAffineSourceWitness
    (LocalizationData := Unit) (CyclicModuleData := Unit)
    (1 : U) 0 1 [localTest] where
  H := 1
  source := 1
  source_eq := by simp
  tests_pass := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact ⟨rfl, rfl, rfl⟩

example : localTest.generation localSource.source
    localTest.offset localTest.rightTail :=
  localSource.test_passes (by simp)

example : ∃ H : U, localSource.source = 0 + H * 1 :=
  localSource.affine_membership

def testedAssembly : TestedAssemblyWitness
    (LocalizationData := Unit) (CyclicModuleData := Unit)
    (1 : U) 0 1 [localTest] where
  localSource := localSource
  assembly := ⟨1, 0, by simp⟩

example : AssemblyWitness (1 : U) testedAssembly.localSource.source :=
  testedAssembly.toAssemblyWitness

example : SymplecticStafford.RightCertificate
    (R := U) 1 testedAssembly.localSource.source 1 :=
  testedAssembly.toCertificate

/- The bridge is checked parametrically: it consumes a producer supplied by a
caller and therefore gives no inhabitant of the producer contract. -/
example (producer : OriginalTestAssemblyProducer U Unit Unit) :
    DivisorIndexedAssembly U :=
  producer.toDivisorIndexedAssembly

end SymplecticStafford.OriginalTestContractOracle

#print axioms SymplecticStafford.OriginalTestContractOracle.localSource
#print axioms SymplecticStafford.OriginalTestContractOracle.testedAssembly
