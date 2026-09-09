import SymplecticStafford.FiniteLength.PrimeVsHomogeneousLocalizationBoundary

/- Independent oracle for the ordinary-prime/homogeneous-localization boundary. -/
namespace SymplecticStaffordTest.PrimeVsHomogeneousLocalizationBoundary

open SymplecticStafford.FiniteLength

example :
    (⊥ : Ideal (LaurentPolynomial ℚ)) < homogeneousLaurentIdeal ∧
      homogeneousLaurentIdeal < (⊤ : Ideal (LaurentPolynomial ℚ)) :=
  homogeneousLaurentIdeal_strict

example (I : Submodule (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℚ))) :
    ¬ ((⊥ : Submodule (FractionRing (Polynomial ℚ))
      (FractionRing (Polynomial ℚ))) < I ∧
      I < (⊤ : Submodule (FractionRing (Polynomial ℚ))
        (FractionRing (Polynomial ℚ)))) :=
  fractionField_no_strict_submodule I

end SymplecticStaffordTest.PrimeVsHomogeneousLocalizationBoundary
