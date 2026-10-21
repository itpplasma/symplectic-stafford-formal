module

public import Mathlib.Algebra.Ring.Subring.Basic
public import SymplecticStafford.Source.OriginalDivisionProducer

@[expose] public section

/-!
# Finite original-coefficient source packages

This file is the composition boundary between finite-direction source
selection and an actual original-ring recombination.  A
`FiniteCoefficientAlgebra` is a supplied subring of the original `U`; its
scalar image is supplied explicitly, and every finite direction and selected
coefficient is tracked by a membership proof.  `OriginalFiniteCoefficientSource`
then records one source for one finite list of local tests, including every
offset and right tail, together with literal original-ring cofactors.

The constructors below consume the existing actual finite-top selector.  They
do not construct a localization, a finite top, a source map, or a universal
producer.  In particular, the assembly callback and all algebra-membership
facts remain hypotheses rather than hidden assumptions.
-/

namespace SymplecticStafford.Source

universe u v w x

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

/- A finite coefficient algebra is a concrete subring of the original ring.
   Requiring the scalar image explicitly prevents a completed or localized
   coefficient from being silently treated as an element of `U`. -/
structure FiniteCoefficientAlgebra (U : Type u) (K : Type v)
    [DivisionRing U] [Field K] where
  carrier : Subring U
  embedding : K →+* U
  embedding_injective : Function.Injective embedding
  scalar_mem : ∀ z : K, embedding z ∈ carrier

namespace FiniteCoefficientAlgebra

variable (A : FiniteCoefficientAlgebra U K)

theorem weightedCombination_mem
    (directions : List U) (coefficients : List K)
    (hlen : coefficients.length = directions.length)
    (hdirections : ∀ h, h ∈ directions → h ∈ A.carrier)
    (hcoefficients : ∀ z, z ∈ coefficients → A.embedding z ∈ A.carrier) :
    weightedCombination A.embedding directions coefficients ∈ A.carrier := by
  induction directions generalizing coefficients with
  | nil =>
      cases coefficients with
      | nil => simp [weightedCombination, A.carrier.zero_mem]
      | cons z zs => simp at hlen
  | cons h hs ih =>
      cases coefficients with
      | nil => simp at hlen
      | cons z zs =>
          simp only [weightedCombination]
          apply A.carrier.add_mem
          · exact A.carrier.mul_mem (hcoefficients z (by simp))
              (hdirections h (by simp))
          · apply ih
            · simpa using hlen
            · intro h' hh'
              exact hdirections h' (by simp [hh'])
            · intro z' hz'
              exact hcoefficients z' (by simp [hz'])

theorem weightedCombination_mem_of_scalar_mem
    (directions : List U) (coefficients : List K)
    (hlen : coefficients.length = directions.length)
    (hdirections : ∀ h, h ∈ directions → h ∈ A.carrier) :
    weightedCombination A.embedding directions coefficients ∈ A.carrier :=
  A.weightedCombination_mem directions coefficients hlen hdirections
    (fun z _ => A.scalar_mem z)

end FiniteCoefficientAlgebra

/-!
One finite source package.  The local-test list is stored as a list of
`OriginalLocalTest`s, so the output assertions retain each test's literal
integer offset and right tail.  The `assembly` field is an exact identity in
the original ring; the two cofactor membership fields make the finite
coefficient control visible at the recombination point.
-/
structure OriginalFiniteCoefficientSource
    {LocalizationData : Type w} {CyclicModuleData : Type x}
    (A : FiniteCoefficientAlgebra U K)
    (d B a : U)
    (tests : List (OriginalLocalTest U LocalizationData CyclicModuleData))
    (directions : List U) where
  coefficients : List K
  coefficients_length : coefficients.length = directions.length
  coefficient_mem : ∀ z, z ∈ coefficients → A.embedding z ∈ A.carrier
  directions_mem : ∀ h, h ∈ directions → h ∈ A.carrier
  multiplier : U
  source : U
  source_eq : source = B + multiplier * a
  multiplier_eq : multiplier = weightedCombination A.embedding directions coefficients
  background_mem : B ∈ A.carrier
  tail_mem : a ∈ A.carrier
  multiplier_mem : multiplier ∈ A.carrier
  source_mem : source ∈ A.carrier
  source_nonzero : source ≠ 0
  admissible : ∀ t, t ∈ tests → t.Admissible d
  passes : ∀ t, t ∈ tests → t.Passes source
  rightTail_nonzero : ∀ t, t ∈ tests → t.rightTail ≠ 0
  assembly : AssemblyWitness d source
  cofactor₁_mem : assembly.right₁ ∈ A.carrier
  cofactor₂_mem : assembly.right₂ ∈ A.carrier

namespace OriginalFiniteCoefficientSource

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {A : FiniteCoefficientAlgebra U K}
variable {d B a : U}
variable {tests : List (OriginalLocalTest U LocalizationData CyclicModuleData)}
variable {directions : List U}

theorem affine_membership
    (S : OriginalFiniteCoefficientSource A d B a tests directions) :
    S.source = B + S.multiplier * a :=
  S.source_eq

theorem selected_multiplier_mem
    (S : OriginalFiniteCoefficientSource A d B a tests directions) :
    S.multiplier ∈ A.carrier :=
  S.multiplier_mem

theorem test_pass
    (S : OriginalFiniteCoefficientSource A d B a tests directions)
    {t : OriginalLocalTest U LocalizationData CyclicModuleData}
    (ht : t ∈ tests) :
    t.generation S.source t.offset t.rightTail :=
  S.passes t ht

theorem exact_recombination
    (S : OriginalFiniteCoefficientSource A d B a tests directions) :
    (1 : U) = d * S.assembly.right₁ +
      (S.source * d) * S.assembly.right₂ :=
  S.assembly.identity

def assembly_certificate
    (S : OriginalFiniteCoefficientSource A d B a tests directions) :
    SymplecticStafford.RightCertificate (R := U) d S.source 1 :=
  S.assembly.certificate

def to_tested_assembly
    (S : OriginalFiniteCoefficientSource A d B a tests directions) :
    TestedAssemblyWitness d B a tests :=
  { localSource :=
      { H := S.multiplier
        source := S.source
        source_eq := S.source_eq
        tests_pass := S.passes }
    assembly := S.assembly }

end OriginalFiniteCoefficientSource

/-!
The actual-top constructor.  The finite-direction selector supplies one
common scalar list and one source for all actual tests.  A separate callback
supplies the exact original-ring assembly and cofactor membership for that
same selected source; this is the only recombination input.
-/
theorem exists_original_finite_coefficient_source_of_actual_directions
    {LocalizationData : Type w} {CyclicModuleData : Type x}
    {R M I : Type*} {D : I → Type*}
    [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module K M]
    [∀ i, DivisionRing (D i)] [Fintype I] [DecidableEq I]
    (A : FiniteCoefficientAlgebra U K)
    (ιmap : (i : I) → K →+* D i)
    (hιmap : ∀ i, Function.Injective (ιmap i))
    (d : U)
    (tests : List (ActualOriginalDivisionTest U K LocalizationData
      CyclicModuleData R M I D A.embedding ιmap))
    (directions : List U) (B a : U) (hB : B ≠ 0) (ha : a ≠ 0)
    (hbackground_mem : B ∈ A.carrier) (htail_mem : a ∈ A.carrier)
    (hdirections : ∀ h, h ∈ directions → h ∈ A.carrier)
    (hadmissible : ∀ t, t ∈ tests → t.localTest.Admissible d)
    (hinitial : ∀ t, t ∈ tests →
      ∀ i, t.bridge.top (t.sourceMap B) i ≠ 0)
    (hassemble : ∀ (H source : U),
      source = B + H * a → source ≠ 0 →
      (∀ t, t ∈ tests → t.localTest.Passes source) →
      ∃ w : AssemblyWitness d source,
        w.right₁ ∈ A.carrier ∧ w.right₂ ∈ A.carrier) :
    Nonempty (OriginalFiniteCoefficientSource A d B a
      (tests.map (fun t => t.localTest)) directions) := by
  obtain ⟨H, source, coefficients, hsource, hsourcene, hlength, hcomb,
      hAdmissible, hpasses, htails⟩ :=
    exists_original_affine_source_of_actual_directions
      A.embedding A.embedding_injective ιmap hιmap d tests directions B a hB ha
      hadmissible hinitial
  have hcoefficients : ∀ z, z ∈ coefficients → A.embedding z ∈ A.carrier := by
    intro z hz
    exact A.scalar_mem z
  have hmultiplier_mem : H ∈ A.carrier := by
    rw [hcomb]
    exact A.weightedCombination_mem_of_scalar_mem directions coefficients
      hlength hdirections
  have hsource_mem : source ∈ A.carrier := by
    rw [hsource]
    exact A.carrier.add_mem hbackground_mem
      (A.carrier.mul_mem hmultiplier_mem htail_mem)
  have hlocal_passes : ∀ t, t ∈ tests.map (fun t => t.localTest) →
      t.Passes source := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact hpasses t' ht'
  obtain ⟨w, hw₁, hw₂⟩ := hassemble H source hsource hsourcene hpasses
  refine ⟨{ coefficients := coefficients
            coefficients_length := hlength
            coefficient_mem := hcoefficients
            directions_mem := hdirections
            multiplier := H
            source := source
            source_eq := hsource
            multiplier_eq := hcomb
            background_mem := hbackground_mem
            tail_mem := htail_mem
            multiplier_mem := hmultiplier_mem
            source_mem := hsource_mem
            source_nonzero := hsourcene
            admissible := ?_
            passes := hlocal_passes
            rightTail_nonzero := ?_
            assembly := w
            cofactor₁_mem := hw₁
            cofactor₂_mem := hw₂}⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact hAdmissible t' ht'
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact htails t' ht'

end SymplecticStafford.Source

#print axioms SymplecticStafford.Source.FiniteCoefficientAlgebra.weightedCombination_mem
#print axioms SymplecticStafford.Source.OriginalFiniteCoefficientSource.to_tested_assembly
#print axioms
  SymplecticStafford.Source.exists_original_finite_coefficient_source_of_actual_directions
