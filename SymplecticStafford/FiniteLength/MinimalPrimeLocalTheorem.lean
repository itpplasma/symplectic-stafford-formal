import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Minimal-prime local length from the actual annihilator support

This is the commutative local algebra core of M05.  For a finite module over a
Noetherian local ring, if the maximal ideal is minimal over the actual module
annihilator, Mathlib's minimal-prime quotient theorem makes the annihilator
quotient Artinian.  The quotient module is finite and therefore Artinian; the
surjective quotient map then reflects Artinianity back to the original ring,
and Noetherianity plus Artinianity gives finite composition length.

No support, localization, or finite-dimensionality field is supplied by the
statement.  A later filtered/Rees proof only has to identify its localized
module and verify the displayed minimal-prime hypothesis.
-/

namespace SymplecticStafford.FiniteLength

theorem isFiniteLength_of_local_minimal_annihilator
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [IsLocalRing R]
    (hmin : IsLocalRing.maximalIdeal R ∈
      (Module.annihilator R M).minimalPrimes) :
    IsFiniteLength R M := by
  let I : Ideal R := Module.annihilator R M
  have hArt : IsArtinianRing (R ⧸ I) := by
    exact IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hmin
  let hT : Module.IsTorsionBySet R M I :=
    Module.isTorsionBySet_annihilator R M
  letI : Module (R ⧸ I) M := hT.module
  letI : Module.Finite (R ⧸ I) M :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  letI : IsArtinianRing (R ⧸ I) := hArt
  have hArtQuot : IsArtinian (R ⧸ I) M := inferInstance
  have hArtOrig : IsArtinian R M := by
    exact isArtinian_of_surjective_algebraMap
      (R := R ⧸ I) (S := R) (M := M)
      Ideal.Quotient.mk_surjective
  have hNoethOrig : IsNoetherian R M := inferInstance
  exact (isFiniteLength_iff_isNoetherian_isArtinian).2
    ⟨hNoethOrig, hArtOrig⟩

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.isFiniteLength_of_local_minimal_annihilator
