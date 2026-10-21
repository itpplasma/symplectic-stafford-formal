module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.FiniteLength
public import SymplecticStafford.FiniteLength.MinimalPrimeLocalTheorem

@[expose] public section

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

section CanonicalLocalization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {G : Type v} [AddCommGroup G] [Module A G]
variable [Module.Finite A G]

/-- The canonical localization of a finite module is nonzero at a minimal
prime of its actual annihilator.  This is the support half of M05, stated
without a filtered/Rees presentation. -/
theorem localizedModule_nontrivial_of_mem_annihilator_minimalPrimes
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Module.annihilator A G).minimalPrimes) :
    Nontrivial (LocalizedModule P.primeCompl G) := by
  let p : PrimeSpectrum A := ⟨P, inferInstance⟩
  have hp : p ∈ Module.support A G :=
    Module.mem_support_iff_of_finite.mpr hP.1.2
  simpa [p] using (Module.mem_support_iff.mp hp)

/-- The annihilator of the original finite module maps into the annihilator
of its canonical localization.  The proof clears no denominators and uses
the actual `LocalizedModule` quotient. -/
private theorem map_annihilator_le_localizedModule_annihilator
    (P : Ideal A) [P.IsPrime] :
    Ideal.map (algebraMap A (Localization.AtPrime P))
        (Module.annihilator A G) ≤
      Module.annihilator (Localization.AtPrime P)
        (LocalizedModule P.primeCompl G) := by
  rw [Ideal.map_le_iff_le_comap]
  intro c hc
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  induction z using LocalizedModule.induction_on with
  | _ g s =>
      rw [IsLocalizedModule.mk_eq_mk']
      rw [← IsLocalization.mk'_one (M := P.primeCompl),
        IsLocalizedModule.mk'_smul_mk', Module.mem_annihilator.mp hc g]
      simp

/-- A minimal annihilator prime gives the local finite-length module required
by M05.  Both nontriviality and finite length refer to the same canonical
`Localization.AtPrime`/`LocalizedModule` pair; no support-dimension or
filtered producer is hidden in this theorem. -/
theorem localizedModule_nontrivial_and_isFiniteLength_of_mem_annihilator_minimalPrimes
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Module.annihilator A G).minimalPrimes) :
    Nontrivial (LocalizedModule P.primeCompl G) ∧
      IsFiniteLength (Localization.AtPrime P)
        (LocalizedModule P.primeCompl G) := by
  classical
  let R := Localization.AtPrime P
  letI : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing P.primeCompl R inferInstance
  letI : Module.Finite R (LocalizedModule P.primeCompl G) :=
    Module.Finite.of_isLocalizedModule P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl G)
  have hnontrivial : Nontrivial (LocalizedModule P.primeCompl G) :=
    localizedModule_nontrivial_of_mem_annihilator_minimalPrimes P hP
  letI : Nontrivial (LocalizedModule P.primeCompl G) := hnontrivial
  have hmap := map_annihilator_le_localizedModule_annihilator (G := G) P
  have hradmap :
      (Ideal.map (algebraMap A R) (Module.annihilator A G)).radical =
        P.map (algebraMap A R) := by
    exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      R P (Module.annihilator A G) hP
  have hmaxrad : IsLocalRing.maximalIdeal R ≤
      (Module.annihilator R (LocalizedModule P.primeCompl G)).radical := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← hradmap]
    exact Ideal.radical_mono hmap
  have hannle : Module.annihilator R (LocalizedModule P.primeCompl G) ≤
      IsLocalRing.maximalIdeal R :=
    Module.annihilator_le_of_mem_support
      (IsLocalRing.closedPoint_mem_support R
        (LocalizedModule P.primeCompl G))
  have hmin : IsLocalRing.maximalIdeal R ∈
      (Module.annihilator R (LocalizedModule P.primeCompl G)).minimalPrimes := by
    have hmaxprime : (IsLocalRing.maximalIdeal R).IsPrime :=
      Ideal.IsMaximal.isPrime (IsLocalRing.maximalIdeal.isMaximal R)
    refine ⟨⟨hmaxprime, hannle⟩, ?_⟩
    intro q hq hqle
    have hradq :
        (Module.annihilator R (LocalizedModule P.primeCompl G)).radical ≤ q :=
      hq.1.radical_le_iff.mpr hq.2
    exact hmaxrad.trans hradq
  exact ⟨hnontrivial, isFiniteLength_of_local_minimal_annihilator hmin⟩

/-- The same endpoint using the actual Mathlib module support.  A minimal
support point is first converted to a minimal prime over the actual
annihilator; this is the source-independent interface needed by a future
filtered/Rees support producer. -/
theorem localizedModule_nontrivial_and_isFiniteLength_of_minimal_support
    (P : PrimeSpectrum A)
    (hP : P ∈ Module.support A G)
    (hmin : ∀ Q : PrimeSpectrum A, Q ∈ Module.support A G →
      Q ≤ P → P ≤ Q) :
    Nontrivial (LocalizedModule P.asIdeal.primeCompl G) ∧
      IsFiniteLength (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl G) := by
  have hann : Module.annihilator A G ≤ P.asIdeal :=
    Module.annihilator_le_of_mem_support hP
  have hminann : P.asIdeal ∈ (Module.annihilator A G).minimalPrimes := by
    refine ⟨⟨P.isPrime, hann⟩, ?_⟩
    intro q hq hqle
    have hqsupport :
        (⟨q, hq.1⟩ : PrimeSpectrum A) ∈ Module.support A G :=
      Module.mem_support_iff_of_finite.mpr hq.2
    exact hmin _ hqsupport hqle
  exact localizedModule_nontrivial_and_isFiniteLength_of_mem_annihilator_minimalPrimes
    P.asIdeal hminann

end CanonicalLocalization

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.isFiniteLength_of_atPrime_supportDim_zero
#print axioms
  SymplecticStafford.FiniteLength.localizedModule_nontrivial_and_isFiniteLength_of_mem_annihilator_minimalPrimes
#print axioms
  SymplecticStafford.FiniteLength.localizedModule_nontrivial_and_isFiniteLength_of_minimal_support
