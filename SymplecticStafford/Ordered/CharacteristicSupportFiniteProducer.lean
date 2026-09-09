import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Support
import SymplecticStafford.Ordered.ActualM08Producer
import SymplecticStafford.Ordered.CharacteristicSupportProducer

/-!
# Finite-colon characteristic-support consumption

`CharacteristicSupportProducer.lean` consumes a local affine producer and a
localized-zero map for the common quotient.  This file adds the finite
right-generation input used by the actual common-colon argument.  The local
zero map is required to consume the *indexed* original-ring expansion of the
cleared denominator, so the support theorem cannot silently discard the
colon generators.  The companion theorem returns the exact ordered
`F * d * k` pencil certificate for every chosen colon generator.

No support theorem, localization, or source producer is constructed here.
Those remain explicit inputs to the structure below.
-/

namespace SymplecticStafford.Ordered

universe u v w

section

variable {A : Type u} [CommRing A]
variable {R : Type v} [Ring R]
variable {S : Type w} [Ring S]
variable {QJ QF QG : Type u}
variable [AddCommGroup QJ] [Module A QJ]
variable [AddCommGroup QF] [Module A QF]
variable [AddCommGroup QG] [Module A QG]

/--
The M08 support consumer with an explicit finite generator witness for the
common colon.  `local_producer` is still a pointwise chart obligation.  The
last field is intentionally stated for the original indexed expansion, not
merely for membership in `commonIdeal`; this is the finite coefficient bridge
used by a localized support proof.
-/
structure FiniteColonCharacteristicSupportProducer
    (κ : R →+* A) (ι : R →+* S) (d F G L C : R) (QJ : Type u)
    [AddCommGroup QJ] [Module A QJ] where
  injective : Function.Injective ι
  local_producer :
    ∀ p : PrimeSpectrum A,
      p ∉ characteristicSupport (A := A) QF →
      p ∉ characteristicSupport (A := A) QG →
      ∃ H : AmbientProducerData ι d F G L C,
        κ H.denominator ∉ p.asIdeal
  colon_generators :
    FiniteRightGeneration (R := R) (commonColonRightIdeal d G)
  common_zero_of_cleared_expansion :
    ∀ (p : PrimeSpectrum A) {s : R},
      κ s ∉ p.asIdeal →
      (∃ r : R, ∃ c : R → R,
        s = d * r +
          ∑ k ∈ colon_generators.generators, (F * d) * k * c k) →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl QJ)

/-- The ambient denominator returned by a local producer has the actual
indexed finite colon-generator expansion in the original ring. -/
theorem ambient_denominator_colon_generator_expansion
    (κ : R →+* A) (ι : R →+* S) (d F G L C : R)
    (D : FiniteColonCharacteristicSupportProducer
      (A := A) (QF := QF) (QG := QG) κ ι d F G L C QJ)
    (H : AmbientProducerData ι d F G L C) :
    ∃ r : R, ∃ c : R → R,
      H.denominator = d * r +
        ∑ k ∈ D.colon_generators.generators, (F * d) * k * c k := by
  exact commonIdeal_mem_from_colon_generators d F G D.colon_generators
    (ambient_producer_returns_original_commonIdeal ι D.injective
      d F G L C H).1

/-- The exact characteristic-support inclusion obtained after consuming the
finite indexed expansion and the supplied localized-zero bridge. -/
theorem characteristicSupport_commonIdeal_subset_union_of_finite_colon_generation
    (κ : R →+* A) (ι : R →+* S) (d F G L C : R)
    (D : FiniteColonCharacteristicSupportProducer
      (A := A) (QF := QF) (QG := QG) κ ι d F G L C QJ) :
    characteristicSupport (A := A) QJ ⊆
      characteristicSupport (A := A) QF ∪
        characteristicSupport (A := A) QG := by
  intro p hp
  by_contra hp_union
  have hpF : p ∉ characteristicSupport (A := A) QF := by
    intro h
    exact hp_union (Or.inl h)
  have hpG : p ∉ characteristicSupport (A := A) QG := by
    intro h
    exact hp_union (Or.inr h)
  obtain ⟨H, Haway⟩ := D.local_producer p hpF hpG
  obtain ⟨r, c, hexpand⟩ :=
    ambient_denominator_colon_generator_expansion κ ι d F G L C D H
  have hsub : Subsingleton (LocalizedModule p.asIdeal.primeCompl QJ) :=
    D.common_zero_of_cleared_expansion p Haway ⟨r, c, hexpand⟩
  have hpnot : p ∉ characteristicSupport (A := A) QJ := by
    exact Module.notMem_support_iff.mpr hsub
  exact hpnot hp

/-- Combined M08 output: the support cover and every original-ring
`F * d * k` certificate belonging to the finite colon-generator witness.
The right-sided factor order is retained verbatim. -/
theorem characteristicSupport_commonIdeal_subset_union_with_colon_pencil_certificates
    (κ : R →+* A) (ι : R →+* S) (d F G L C : R)
    (D : FiniteColonCharacteristicSupportProducer
      (A := A) (QF := QF) (QG := QG) κ ι d F G L C QJ) :
    (characteristicSupport (A := A) QJ ⊆
      characteristicSupport (A := A) QF ∪
        characteristicSupport (A := A) QG) ∧
      (∀ k ∈ D.colon_generators.generators, ∀ t : R,
        (∀ y : R, t * y = y * t) →
        ∃ c : R,
          G * d * k = d * c ∧
            F * d * k = d * (-t * c) +
              (F + t * G) * d * k) := by
  constructor
  · exact characteristicSupport_commonIdeal_subset_union_of_finite_colon_generation
      κ ι d F G L C D
  · intro k hk t ht
    exact common_colon_pencil_certificate d F G k t
      ((finiteRightGeneration_generator_mem D.colon_generators) k hk) ht

end

end SymplecticStafford.Ordered

#print axioms
  SymplecticStafford.Ordered.ambient_denominator_colon_generator_expansion
#print axioms
  SymplecticStafford.Ordered.characteristicSupport_commonIdeal_subset_union_of_finite_colon_generation
#print axioms
  SymplecticStafford.Ordered.characteristicSupport_commonIdeal_subset_union_with_colon_pencil_certificates
