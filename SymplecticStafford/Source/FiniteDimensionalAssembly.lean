module

public import SymplecticStafford.Source.FiniteDimensionalProducer
public import SymplecticStafford.Source.Assembly

@[expose] public section

/-!
# Divisor-indexed assembly from finite-dimensional source tests

This module is the M06-to-M11 composition boundary.  A
`FiniteDimensionalDivisorCertificate` supplies, for each nonzero divisor, a
finite list of split finite-dimensional tests, the affine background and
nonzero tail, the local pass/injectivity bridges, and an explicit assembly
callback.  The preceding selector chooses one source for that divisor; the
callback then supplies literal original-ring cofactors for exactly that
source.

The output is an actual `DivisorIndexedAssembly`, and hence a same-divisor
certificate.  The only nonconstructive step is ordinary choice of the
selector's existential witnesses.  No source in a completion or localization
is identified with an original element, and the order
`d * right₁ + (source * d) * right₂` is retained verbatim.
-/

namespace SymplecticStafford.Source

universe u v w x y z

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

structure FiniteDimensionalDivisorCertificate
    (U : Type u) (K : Type v) (LocalizationData : Type w)
    (CyclicModuleData : Type x) (P V : Type y) (J : Type z)
    [DivisionRing U] [Field K]
    [AddCommGroup P] [Module K P] [FiniteDimensional K P]
    [AddCommGroup V] [Module K V]
    [Fintype J] [DecidableEq J] where
  scalarEmbedding : K →+* U
  scalarEmbedding_injective : Function.Injective scalarEmbedding
  tests : U → List (FiniteDimensionalDivisionTest U K LocalizationData
    CyclicModuleData P V J)
  background : U → U
  affineTail : U → U
  affineTail_nonzero : ∀ ⦃d : U⦄, d ≠ 0 → affineTail d ≠ 0
  admissible : ∀ ⦃d : U⦄, d ≠ 0 → ∀ t, t ∈ tests d →
    t.localTest.Admissible d
  pass_iff_injective : ∀ ⦃d : U⦄, d ≠ 0 → ∀ t, t ∈ tests d → ∀ z : K,
    t.localTest.Passes
        (background d + scalarEmbedding z * affineTail d) ↔
      Function.Injective
        (t.base (background d) (affineTail d) + z •
          t.direction (background d) (affineTail d))
  assemble : ∀ ⦃d : U⦄, (hd : d ≠ 0) → ∀ (H source : U),
    source = background d + H * affineTail d → source ≠ 0 →
    (∀ t, t ∈ tests d → t.localTest.Passes source) →
    AssemblyWitness d source

namespace FiniteDimensionalDivisorCertificate

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {P V : Type y} {J : Type z}
variable [AddCommGroup P] [Module K P] [FiniteDimensional K P]
variable [AddCommGroup V] [Module K V]
variable [Fintype J] [DecidableEq J]

/-- The per-divisor finite-dimensional selector, with all its fields named so
the assembly theorem below can consume the same witnesses. -/
theorem select_source
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J)
    {d : U} (hd : d ≠ 0) :
    ∃ (H source : U),
      source = C.background d + H * C.affineTail d ∧ source ≠ 0 ∧
      (∀ t, t ∈ C.tests d → t.localTest.Admissible d) ∧
      (∀ t, t ∈ C.tests d → t.localTest.Passes source) ∧
      (∀ t, t ∈ C.tests d → t.localTest.rightTail ≠ 0) := by
  exact exists_original_affine_source_of_finite_dimensional_list
    C.scalarEmbedding C.scalarEmbedding_injective d (C.tests d)
    (C.background d) (C.affineTail d) (C.affineTail_nonzero hd)
    (C.admissible hd) (C.pass_iff_injective hd)

/-- Choice packages one selected source per nonzero divisor and the supplied
literal assembly callback into the existing original-ring API. -/
noncomputable def toDivisorIndexedAssembly
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J) : DivisorIndexedAssembly U := by
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
  exact {
    source := source
    assemble := fun {d} hd => C.assemble hd (H d hd) (source d hd)
      (hsource d hd) (hne d hd) (hpass d hd) }

theorem same_divisor
    (C : FiniteDimensionalDivisorCertificate U K LocalizationData
      CyclicModuleData P V J) :
    SymplecticStafford.SameDivisorS1 (R := U) :=
  DivisorIndexedAssembly.sameDivisor (C.toDivisorIndexedAssembly)

end FiniteDimensionalDivisorCertificate

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.FiniteDimensionalDivisorCertificate.select_source
#print axioms
  SymplecticStafford.Source.FiniteDimensionalDivisorCertificate.toDivisorIndexedAssembly
#print axioms SymplecticStafford.Source.FiniteDimensionalDivisorCertificate.same_divisor
