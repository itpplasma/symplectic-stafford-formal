module

public import SymplecticStafford.Filtered.ReesGoodSubquotient
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent oracle for the downstream finite-good-module consumer. -/
namespace SymplecticStaffordTest.ReesGoodSubquotient

open SymplecticStafford.Filtered

noncomputable def rationalCertificate :
    ReesModuleNoetherianCertificate ℚ ℚ :=
  moduleCertificate_of_noetherianRing

example : IsNoetherian ℚ ℚ := by
  exact moduleCertificate_of_noetherianRing_isNoetherian

example : rationalCertificate.degree 0 = 0 := by
  simp [rationalCertificate, moduleCertificate_of_noetherianRing,
    noetherianModuleCertificate, twoLevelDegree]

example : rationalCertificate.degree 7 = 1 := by
  simp [rationalCertificate, moduleCertificate_of_noetherianRing,
    noetherianModuleCertificate, twoLevelDegree]

example (N : Submodule ℚ ℚ) : IsNoetherian ℚ (ℚ ⧸ N) :=
  noetherian_good_subquotient N

end SymplecticStaffordTest.ReesGoodSubquotient
