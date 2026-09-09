import Mathlib.Tactic.NoncommRing
import SymplecticStafford.Filtered.FullSymbolOriginalCofactor
import SymplecticStafford.Source.Assembly

/-!
# Descent of localized divisor certificates to original assembly

`FullSymbolOriginalCofactor` produces an original identity with the cleared
denominator on the left-hand side.  Such an identity is not yet a Stafford
certificate: a denominator from the localization need not be a unit in the
original ring.  This file makes the missing descent datum explicit by asking
for a right inverse of every denominator in the supplied chart.

With that datum, each localized two-generator identity gives literal
original cofactors, and a divisor-indexed family of such certificates feeds
the existing `DivisorIndexedAssembly` consumer.  No claim is made that the
denominator inverses, charts, or localized identities follow from filtered
hypotheses.
-/

namespace SymplecticStafford.Source

universe u

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.FullSymbolRightLocalization
open SymplecticStafford.Filtered.FullSymbolOriginalCofactor

variable {R : Type u} [Ring R]

/- A finite localized source certificate for one divisor.  The two displayed
   coefficients are exactly the finite family cleared by the preceding
   common-denominator theorem. -/
structure LocalizedDivisorCertificate (d f : R) where
  chart : FullSymbolRightLocalization.Data R
  q₁ : FullSymbolRightLocalization.Data.Localization chart
  q₂ : FullSymbolRightLocalization.Data.Localization chart
  localized_identity : FullSymbolRightLocalization.Data.numerator chart d * q₁ +
      (FullSymbolRightLocalization.Data.numerator chart f *
        FullSymbolRightLocalization.Data.numerator chart d) * q₂ = 1
  denominator_right_inverse :
    ∀ s : chart.denominators, ∃ u : R, (s : R) * u = 1

namespace LocalizedDivisorCertificate

variable {d f : R}

/- The cleared denominator is first retained, then cancelled only using the
   supplied original-ring right inverse.  All factors stay on the right. -/
noncomputable def toAssemblyWitness
    (C : LocalizedDivisorCertificate d f) : AssemblyWitness d f := by
  classical
  let hcleared := localized_two_generator_to_original C.chart d f C.q₁ C.q₂
      C.localized_identity
  let s : R := Classical.choose hcleared
  have hst : ∃ r t : R, s ∈ C.chart.denominators ∧
      s = d * r + (f * d) * t := Classical.choose_spec hcleared
  let r : R := Classical.choose hst
  have ht : ∃ t : R, s ∈ C.chart.denominators ∧
      s = d * r + (f * d) * t := Classical.choose_spec hst
  let t : R := Classical.choose ht
  have hst' : s ∈ C.chart.denominators ∧
      s = d * r + (f * d) * t := Classical.choose_spec ht
  let sd : C.chart.denominators := ⟨s, hst'.1⟩
  let hu_exists := C.denominator_right_inverse sd
  let u : R := Classical.choose hu_exists
  have hu : (sd : R) * u = 1 := Classical.choose_spec hu_exists
  refine ⟨r * u, t * u, ?_⟩
  calc
    (1 : R) = s * u := hu.symm
    _ = (d * r + (f * d) * t) * u := by rw [hst'.2]
    _ = d * (r * u) + (f * d) * (t * u) := by noncomm_ring

noncomputable def toCertificate
    (C : LocalizedDivisorCertificate d f) :
    SymplecticStafford.RightCertificate (R := R) d f 1 :=
  C.toAssemblyWitness.certificate

end LocalizedDivisorCertificate

/- A supplied actual chart and finite localized identity for every nonzero
   divisor.  The source may depend on the divisor, exactly as in the
   divisor-indexed original assembly contract. -/
structure DivisorIndexedLocalizedProducer where
  chart : ∀ (d : R), d ≠ 0 → FullSymbolRightLocalization.Data R
  source : ∀ (d : R), d ≠ 0 → R
  q₁ : ∀ (d : R) (hd : d ≠ 0),
    FullSymbolRightLocalization.Data.Localization (chart d hd)
  q₂ : ∀ (d : R) (hd : d ≠ 0),
    FullSymbolRightLocalization.Data.Localization (chart d hd)
  localized_identity : ∀ (d : R) (hd : d ≠ 0),
    FullSymbolRightLocalization.Data.numerator (chart d hd) d * q₁ d hd +
        (FullSymbolRightLocalization.Data.numerator (chart d hd) (source d hd) *
          FullSymbolRightLocalization.Data.numerator (chart d hd) d) *
            q₂ d hd = 1
  denominator_right_inverse : ∀ (d : R) (hd : d ≠ 0)
    (s : (chart d hd).denominators), ∃ u : R, (s : R) * u = 1

namespace DivisorIndexedLocalizedProducer

variable (P : DivisorIndexedLocalizedProducer (R := R))

noncomputable def certificate {d : R} (hd : d ≠ 0) :
    LocalizedDivisorCertificate d (P.source d hd) where
  chart := P.chart d hd
  q₁ := P.q₁ d hd
  q₂ := P.q₂ d hd
  localized_identity := P.localized_identity d hd
  denominator_right_inverse := P.denominator_right_inverse d hd

noncomputable def toDivisorIndexedAssembly : DivisorIndexedAssembly R where
  source := fun {d} hd => P.source d hd
  assemble := fun {d} hd =>
    (P.certificate hd).toAssemblyWitness

theorem sameDivisor
    (P : DivisorIndexedLocalizedProducer (R := R)) :
    SymplecticStafford.SameDivisorS1 (R := R) :=
  (toDivisorIndexedAssembly P).sameDivisor

end DivisorIndexedLocalizedProducer

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.LocalizedDivisorCertificate.toAssemblyWitness
#print axioms
  SymplecticStafford.Source.DivisorIndexedLocalizedProducer.toDivisorIndexedAssembly
#print axioms
  SymplecticStafford.Source.DivisorIndexedLocalizedProducer.sameDivisor
