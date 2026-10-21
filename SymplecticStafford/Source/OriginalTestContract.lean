module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.List.Basic
public import SymplecticStafford.Source.Assembly

@[expose] public section

/-!
# Original-`U` finite local-test contract

This module records the paper-shaped boundary at M06.  A local test names its
localization, finite cyclic module, canonical generator, nonzero right tail,
and integer offset.  A witness then supplies one source in the *original*
semiring which lies in the requested affine family and passes every test in a
finite list.

The structures below are conditional interfaces.  They neither construct the
localizations nor prove that a witness exists for the admissible symplectic
class.  In particular, `OriginalAffineSourceWitness` contains no Stafford
identity.  `TestedAssemblyWitness` is a separate composition point at which a
later argument may attach an explicitly supplied `AssemblyWitness`.
-/

namespace SymplecticStafford.Source

universe u v w

variable {U : Type u} [Semiring U]

/-- One M06 local test, with all data which must remain tied to the original
divisor.  The three specification propositions are explicit proof-carrying
fields because this checkpoint does not yet formalize the corresponding
localization and finite-length module theories.

`generation source offset rightTail` is the exact local assertion tested for a
chosen original-`U` source; hence neither the offset nor the nonzero tail can
silently disappear from the interface. -/
structure OriginalLocalTest (U : Type u) [Semiring U]
    (LocalizationData : Type v) (CyclicModuleData : Type w) where
  targetDivisor : U
  localization : LocalizationData
  cyclicFiniteModule : CyclicModuleData
  canonicalGenerator : CyclicModuleData
  rightTail : U
  offset : Int
  localization_spec : Prop
  localization_spec_proof : localization_spec
  finite_length_cyclic_spec : Prop
  finite_length_cyclic_proof : finite_length_cyclic_spec
  canonical_generator_spec : Prop
  canonical_generator_spec_proof : canonical_generator_spec
  rightTail_nonzero : rightTail ≠ 0
  generation : U → Int → U → Prop

def OriginalLocalTest.Passes
    (t : OriginalLocalTest U LocalizationData CyclicModuleData)
    (source : U) : Prop :=
  t.generation source t.offset t.rightTail

/-- All static fields of a test are valid for the displayed original
divisor. -/
def OriginalLocalTest.Admissible (d : U)
    (t : OriginalLocalTest U LocalizationData CyclicModuleData) : Prop :=
  t.targetDivisor = d ∧
    t.localization_spec ∧
    t.finite_length_cyclic_spec ∧
    t.canonical_generator_spec ∧
    t.rightTail ≠ 0

theorem OriginalLocalTest.admissible_of_fields (d : U)
    (t : OriginalLocalTest U LocalizationData CyclicModuleData)
    (target_eq : t.targetDivisor = d) :
    t.Admissible d := by
  exact ⟨target_eq, t.localization_spec_proof,
    t.finite_length_cyclic_proof, t.canonical_generator_spec_proof,
    t.rightTail_nonzero⟩

/-- A list is the finite test family itself; this predicate ties every member
to the same original divisor. -/
def AdmissibleOriginalTestList (d : U)
    (tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)) :
    Prop :=
  ∀ t, t ∈ tests → t.Admissible d

theorem admissibleOriginalTestList_nil (d : U) :
    AdmissibleOriginalTestList d
      ([] : List (OriginalLocalTest U LocalizationData CyclicModuleData)) := by
  intro t ht
  simp at ht

theorem admissibleOriginalTestList_cons
    {d : U}
    {t : OriginalLocalTest U LocalizationData CyclicModuleData}
    {tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)}
    (ht : t.Admissible d)
    (htests : AdmissibleOriginalTestList d tests) :
    AdmissibleOriginalTestList d (t :: tests) := by
  intro t' ht'
  simp only [List.mem_cons] at ht'
  rcases ht' with rfl | ht'
  · exact ht
  · exact htests t' ht'

/-- The exact M06 output shape: one literal original-`U` source in `B + U a`
which simultaneously passes a supplied finite local-test list.  The nonzero
tail `a` and the admissibility proof are inputs, not conclusions. -/
structure OriginalAffineSourceWitness
    (d B a : U)
    (tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)) where
  H : U
  source : U
  source_eq : source = B + H * a
  tests_pass : ∀ t, t ∈ tests → t.Passes source

theorem OriginalAffineSourceWitness.affine_membership
    {d B a : U}
    {tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)}
    (w : OriginalAffineSourceWitness d B a tests) :
    ∃ H : U, w.source = B + H * a :=
  ⟨w.H, w.source_eq⟩

theorem OriginalAffineSourceWitness.test_passes
    {d B a : U}
    {tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)}
    (w : OriginalAffineSourceWitness d B a tests)
    {t : OriginalLocalTest U LocalizationData CyclicModuleData}
    (ht : t ∈ tests) :
    t.generation w.source t.offset t.rightTail :=
  w.tests_pass t ht

/-- Conditional producer type for M06.  It quantifies over the original
divisor, affine background and nonzero tail, and every finite admissible test
list.  No inhabitant is postulated in this module. -/
def OriginalFiniteTestProducer
    (U : Type u) [Semiring U]
    (LocalizationData : Type v) (CyclicModuleData : Type w) : Type _ :=
  ∀ (d : U), d ≠ 0 → ∀ (B a : U), a ≠ 0 →
    ∀ (tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)),
      AdmissibleOriginalTestList d tests →
        OriginalAffineSourceWitness d B a tests

/-- A composition point for M06 and the later original-ring assembly step.
The exact Stafford identity is stored as supplied data rather than inferred
from the local tests. -/
structure TestedAssemblyWitness
    (d B a : U)
    (tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)) where
  localSource : OriginalAffineSourceWitness d B a tests
  assembly : AssemblyWitness d localSource.source

def TestedAssemblyWitness.toAssemblyWitness
    {d B a : U}
    {tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)}
    (w : TestedAssemblyWitness d B a tests) :
    AssemblyWitness d w.localSource.source :=
  w.assembly

def TestedAssemblyWitness.toCertificate
    {d B a : U}
    {tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)}
    (w : TestedAssemblyWitness d B a tests) :
    SymplecticStafford.RightCertificate (R := U)
      d w.localSource.source 1 :=
  w.assembly.certificate

/-- Conditional composite producer.  This is deliberately stronger than M06:
it additionally asks the caller to supply the later original-`U` assembly
witness.  The definition is useful for wiring that evidence into
`Source.Assembly`, but no instance is asserted here. -/
def OriginalTestAssemblyProducer
    (U : Type u) [Semiring U]
    (LocalizationData : Type v) (CyclicModuleData : Type w) : Type _ :=
  ∀ (d : U), d ≠ 0 → ∀ (B a : U), a ≠ 0 →
    ∀ (tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)),
      AdmissibleOriginalTestList d tests →
        TestedAssemblyWitness d B a tests

/-- A supplied composite producer can be consumed by the existing
divisor-indexed assembly API.  Choosing `B = 0`, `a = 1`, and no extra tests is
only an extraction from the producer argument; it is not an existence proof
for that argument. -/
def OriginalTestAssemblyProducer.toDivisorIndexedAssembly
    [Nontrivial U]
    (producer : OriginalTestAssemblyProducer U LocalizationData CyclicModuleData) :
    DivisorIndexedAssembly U where
  source := fun {d} hd =>
    (producer d hd 0 1 one_ne_zero []
      (admissibleOriginalTestList_nil d)).localSource.source
  assemble := fun {d} hd =>
    (producer d hd 0 1 one_ne_zero []
      (admissibleOriginalTestList_nil d)).assembly

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.OriginalLocalTest.admissible_of_fields
#print axioms SymplecticStafford.Source.OriginalAffineSourceWitness.test_passes
#print axioms SymplecticStafford.Source.TestedAssemblyWitness.toCertificate
#print axioms SymplecticStafford.Source.OriginalTestAssemblyProducer.toDivisorIndexedAssembly
