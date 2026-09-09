import SymplecticStafford.Source.FiniteDimensionalAssembly

/-!
# Retained finite-test assembly

`FiniteDimensionalAssembly` already packages the finite-dimensional selector
into a divisor-indexed assembly.  This companion keeps the source-selection
evidence visible as well: one original multiplier per divisor, the affine
equation, nonzeroness, admissibility, and every test's generation assertion
with its literal offset and right tail.  It is a strengthening of the output
interface, not a second source-selection argument.
-/

namespace SymplecticStafford.Source

universe u v w x y z

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

structure RetainedFiniteTestAssembly
    (LocalizationData : Type w) (CyclicModuleData : Type x)
    (P V : Type y) (J : Type z)
    [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    [AddCommGroup V] [Module K V]
    [Fintype J] [DecidableEq J]
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J) where
  assembly : DivisorIndexedAssembly U
  multiplier : ∀ (d : U) (hd : d ≠ 0), U
  affine_source : ∀ (d : U) (hd : d ≠ 0),
    assembly.source hd = C.background d + multiplier d hd * C.affineTail d
  source_nonzero : ∀ (d : U) (hd : d ≠ 0), assembly.source hd ≠ 0
  retained_tests : ∀ (d : U) (hd : d ≠ 0) t, t ∈ C.tests d →
    t.localTest.Admissible d ∧
      t.localTest.generation (assembly.source hd)
        t.localTest.offset t.localTest.rightTail ∧
      t.localTest.rightTail ≠ 0

namespace RetainedFiniteTestAssembly

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {P V : Type y} {J : Type z}
variable [AddCommGroup P] [Module K P] [FiniteDimensional K P]
variable [AddCommGroup V] [Module K V]
variable [Fintype J] [DecidableEq J]

/-- Construct the retained wrapper by choosing exactly the witnesses used by
the existing finite-dimensional divisor assembly. -/
noncomputable def of_certificate
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J) : RetainedFiniteTestAssembly
      LocalizationData CyclicModuleData P V J C := by
  classical
  have hselect : ∀ (d : U), d ≠ 0 →
      ∃ (H source : U),
        source = C.background d + H * C.affineTail d ∧ source ≠ 0 ∧
        (∀ t, t ∈ C.tests d → t.localTest.Admissible d) ∧
        (∀ t, t ∈ C.tests d → t.localTest.Passes source) ∧
        (∀ t, t ∈ C.tests d → t.localTest.rightTail ≠ 0) := by
    intro d hd
    exact C.select_source hd
  choose H source hsource hne hadmiss hpass htail using hselect
  let A : DivisorIndexedAssembly U := {
    source := source
    assemble := fun {d} hd => C.assemble hd (H d hd) (source d hd)
      (hsource d hd) (hne d hd) (hpass d hd) }
  refine {
    assembly := A
    multiplier := H
    affine_source := ?_
    source_nonzero := ?_
    retained_tests := ?_ }
  · intro d hd
    exact hsource d hd
  · intro d hd
    exact hne d hd
  · intro d hd t ht
    refine ⟨hadmiss d hd t ht, ?_, htail d hd t ht⟩
    exact hpass d hd t ht

theorem same_divisor
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J)
    (A : RetainedFiniteTestAssembly LocalizationData CyclicModuleData
      P V J C) :
    SymplecticStafford.SameDivisorS1 (R := U) :=
  DivisorIndexedAssembly.sameDivisor A.assembly

theorem certificate_same_divisor
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J) :
    SymplecticStafford.SameDivisorS1 (R := U) :=
  same_divisor C (of_certificate C)

end RetainedFiniteTestAssembly

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.RetainedFiniteTestAssembly.of_certificate
#print axioms SymplecticStafford.Source.RetainedFiniteTestAssembly.same_divisor
#print axioms
  SymplecticStafford.Source.RetainedFiniteTestAssembly.certificate_same_divisor
