import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum
import SymplecticStafford.Filtered.ReesPolynomialNoetherian

/- Independent oracle for the concrete Mathlib Rees chart and its bridge to
   `ReesNoetherianCriterion`. -/
namespace SymplecticStaffordTest.ReesPolynomialNoetherian

open SymplecticStafford.Filtered
open Polynomial

abbrev QIdeal : Ideal ℚ := Ideal.span ({(2 : ℚ)} : Set ℚ)

noncomputable def chartCertificate :
    ReesNoetherianCertificate (reesAlgebra QIdeal) :=
  reesAlgebraNoetherianCertificate QIdeal

example : IsNoetherianRing (reesAlgebra QIdeal) := by
  exact reesAlgebraNoetherianCertificate_isNoetherian QIdeal

example : chartCertificate.degree 0 = 0 := by
  simp [chartCertificate, reesAlgebraNoetherianCertificate,
    noetherianRingCertificate, idealTwoLevelDegree]

example : chartCertificate.degree 7 = 1 := by
  norm_num [chartCertificate, reesAlgebraNoetherianCertificate,
    noetherianRingCertificate, idealTwoLevelDegree]

example : Polynomial.monomial 1 (2 : ℚ) ∈ reesAlgebra QIdeal := by
  rw [reesAlgebra.monomial_mem]
  simp [QIdeal]

example (J : Ideal (reesAlgebra QIdeal)) : J.FG := by
  exact (isNoetherianRing_iff_ideal_fg (reesAlgebra QIdeal)).mp
    (reesAlgebraNoetherianCertificate_isNoetherian QIdeal) J

end SymplecticStaffordTest.ReesPolynomialNoetherian
