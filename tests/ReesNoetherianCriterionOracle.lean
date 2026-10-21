module

public import Mathlib.Data.ZMod.Basic
public import SymplecticStafford.Filtered.ReesNoetherianCriterion

@[expose] public section

/- Independent oracle for the strict filtered-reduction theorem.  The
  one-element ring makes the reduction branch vacuous, while still checking
  the complete ideal-generation/noetherian conclusion through the public
  theorem. -/
namespace SymplecticStaffordTest.ReesNoetherianCriterion

open SymplecticStafford.Filtered

def trivialCertificate : ReesNoetherianCertificate (ZMod 1) where
  degree := fun _ => 0
  generators := fun _ => {0}
  generators_mem := by
    intro I x hx
    have hx0 : x = 0 := Subsingleton.elim _ _
    simpa [hx0]
  reduce := by
    intro I x hx hne
    exact False.elim (hne (Subsingleton.elim _ _))

example : IsNoetherianRing (ZMod 1) :=
  trivialCertificate.isNoetherianRing

example (I : Ideal (ZMod 1)) :
    I = Ideal.span (trivialCertificate.generators I : Set (ZMod 1)) :=
  trivialCertificate.ideal_eq_span_generators I

end SymplecticStaffordTest.ReesNoetherianCriterion
