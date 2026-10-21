module

public import Mathlib.RingTheory.Support
public import SymplecticStafford.Ordered.CommonColonProducer

@[expose] public section

/-!
# Actual characteristic-support consumption for M08

`M08SupportUnion.lean` uses a support function and a branch-exclusion field,
which is intentionally only a boundary.  Here the support is genuinely
`Module.support` over a commutative coefficient ring.  The missing geometric
work is isolated as two local chart obligations: a producer certificate at a
prime outside both branch supports, and the statement that a cleared element
of the original common ideal kills the localized common quotient.

The conclusion is then a theorem about actual spectrum support, not an
assumed support-union proposition.  In particular, the producer is the
`AmbientProducerData` theorem from `CommonColonProducer`; the local bridge
returns its denominator to the original ring and records that it avoids the
chosen prime.
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

/-- The actual support of an associated/characteristic module. -/
abbrev characteristicSupport (Q : Type u) [AddCommGroup Q] [Module A Q] :
    Set (PrimeSpectrum A) := Module.support A Q

/- The local data needed to consume a characteristic-support point.  The
   first field is the exact chart producer; the second is the local
   characteristic-support bridge for the common quotient.  Neither field is
   itself the desired support-union conclusion. -/
structure LocalCharacteristicSupportProducer
    (κ : R →+* A) (ι : R →+* S) (d F G L C : R)
    (QJ : Type u) [AddCommGroup QJ] [Module A QJ] where
  injective : Function.Injective ι
  local_producer :
    ∀ p : PrimeSpectrum A,
      p ∉ characteristicSupport (A := A) QF →
      p ∉ characteristicSupport (A := A) QG →
      ∃ H : AmbientProducerData ι d F G L C,
        κ H.denominator ∉ p.asIdeal
  common_zero_of_cleared_mem :
    ∀ (p : PrimeSpectrum A) {s : R},
      κ s ∉ p.asIdeal → s ∈ commonIdeal d F G →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl QJ)

/-- The characteristic-support union theorem once the actual local chart
    producer and its quotient-zero bridge have been supplied. -/
theorem characteristicSupport_commonIdeal_subset_union
    (κ : R →+* A) (ι : R →+* S) (d F G L C : R)
    (D : LocalCharacteristicSupportProducer (A := A) (QF := QF) (QG := QG)
      κ ι d F G L C QJ) :
    characteristicSupport (A := A) QJ ⊆ characteristicSupport (A := A) QF ∪
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
  have Hcommon := ambient_producer_returns_original_commonIdeal ι D.injective
    d F G L C H
  have hsub :
      Subsingleton (LocalizedModule p.asIdeal.primeCompl QJ) :=
    D.common_zero_of_cleared_mem p Haway Hcommon.1
  have hpnot : p ∉ characteristicSupport (A := A) QJ := by
    exact (Module.notMem_support_iff.mpr hsub)
  exact hpnot hp

end

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.characteristicSupport_commonIdeal_subset_union
