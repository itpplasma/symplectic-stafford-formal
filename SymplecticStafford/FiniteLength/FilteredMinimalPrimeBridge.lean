import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.FiniteLength
import SymplecticStafford.FiniteLength.MinimalPrimeLocalTheorem

/-!
# Filtered/localized bridge to minimal-prime finite length

The filtered proof produces a genuine commutative localization of the
associated graded coefficient ring.  At a minimal characteristic support
prime its finite module has support dimension zero.  This file turns that
dimension statement into finite composition length without taking local
Noetherianity or minimality of the module annihilator as an input.

No assertion is made for an arbitrary ring merely declared local: the
localization is the actual `Localization.AtPrime` object, so Noetherianity is
inherited from the ambient ring by Mathlib's localization theorem.  The
minimal-prime condition is derived from the support-dimension-zero equality.
-/

namespace SymplecticStafford.FiniteLength

universe u v

section AtPrime

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (p : Ideal A) [p.IsPrime]
variable {M : Type v} [AddCommGroup M]
variable [Module (Localization.AtPrime p) M]
variable [Module.Finite (Localization.AtPrime p) M]
variable [Nontrivial M]

private theorem atPrime_maximal_mem_annihilator_minimalPrimes
    (hDim : Module.supportDim (Localization.AtPrime p) M = 0) :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      (Module.annihilator (Localization.AtPrime p) M).minimalPrimes := by
  let R := Localization.AtPrime p
  let I : Ideal R := Module.annihilator R M
  have hSupp : Module.support R M =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R) := by
    exact support_of_supportDim_eq_zero R M hDim
  have hmaxPrime : (IsLocalRing.maximalIdeal R).IsPrime :=
    Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal R)
  letI : (IsLocalRing.maximalIdeal R).IsPrime := hmaxPrime
  have hle : I ≤ IsLocalRing.maximalIdeal R :=
    Module.annihilator_le_of_mem_support
      (IsLocalRing.closedPoint_mem_support R M)
  obtain ⟨q, hq, hqle⟩ :=
    Ideal.exists_minimalPrimes_le (I := I) (J := IsLocalRing.maximalIdeal R)
      hle
  have hqSupport :
      (⟨q, hq.1.1⟩ : PrimeSpectrum R) ∈ Module.support R M := by
    exact Module.mem_support_iff_of_finite.mpr hq.1.2
  have hmaxleq : IsLocalRing.maximalIdeal R ≤ q := by
    have hz := hqSupport
    rw [hSupp, PrimeSpectrum.mem_zeroLocus] at hz
    exact hz
  have hEq : q = IsLocalRing.maximalIdeal R :=
    le_antisymm hqle hmaxleq
  simpa [hEq] using hq

/- The support-dimension-zero route includes the zero module: in that case
  `support_of_supportDim_eq_zero` is deliberately not applicable, so handle it
  before invoking the local support theorem. -/
theorem isFiniteLength_of_atPrime_supportDim_zero
    (hDim : Module.supportDim (Localization.AtPrime p) M = 0) :
    IsFiniteLength (Localization.AtPrime p) M := by
  classical
  by_cases hsub : Subsingleton M
  · letI : Subsingleton M := hsub
    exact IsFiniteLength.of_subsingleton
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    letI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    have hmin := atPrime_maximal_mem_annihilator_minimalPrimes p hDim
    exact isFiniteLength_of_local_minimal_annihilator hmin

end AtPrime

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.isFiniteLength_of_atPrime_supportDim_zero
