import Mathlib.Data.ZMod.Basic
import SymplecticStafford.Filtered.ReesNoetherianCriterion

/- Independent oracle for the module strict-reduction consumer.  The
one-element module makes the reduction branch vacuous while checking the
submodule-generation and Noetherian-module conclusions at actual module
types. -/
namespace SymplecticStaffordTest.ReesModuleNoetherianCriterion

open SymplecticStafford.Filtered

def trivialCertificate :
    ReesModuleNoetherianCertificate (ZMod 1) (ZMod 1) where
  degree := fun _ => 0
  generators := fun _ => {0}
  generators_mem := by
    intro N x hx
    have hx0 : x = 0 := Subsingleton.elim _ _
    simpa [hx0]
  reduce := by
    intro N x hx hne
    exact False.elim (hne (Subsingleton.elim _ _))

example : IsNoetherian (ZMod 1) (ZMod 1) :=
  trivialCertificate.isNoetherianModule

example (N : Submodule (ZMod 1) (ZMod 1)) : N.FG :=
  trivialCertificate.submodule_fg N

example (N : Submodule (ZMod 1) (ZMod 1)) :
    N = Submodule.span (ZMod 1) (trivialCertificate.generators N : Set (ZMod 1)) :=
  trivialCertificate.submodule_eq_span_generators N

end SymplecticStaffordTest.ReesModuleNoetherianCriterion
