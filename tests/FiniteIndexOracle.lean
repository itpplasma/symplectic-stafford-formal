import SymplecticStafford.Induction.FiniteIndex
import Mathlib.Data.ZMod.Basic

/-!
# Independent oracle checks for finite-index M09--M10 composition

The `ZMod 1` model has no nonzero divisor, so its producer obligations close
by contradiction.  It is therefore an oracle for the *index plumbing* only:
the test exercises the explicit base, every-index successor family, endpoint
arithmetic, and zero-extraction arguments without pretending to instantiate
the paper's source producer.
-/

namespace SymplecticStafford.FiniteIndexOracle

open SymplecticStafford.Induction

abbrev U := ZMod 1

def defect : U → U → List (LocalTest U U U) → Int :=
  fun _ _ _ => -1

def parameters : CentralParameters U U where
  embed := fun scalar => scalar
  central := by intros; exact mul_comm _ _

def base : StrongPh 3 1 defect := by
  intro d hd
  exact False.elim (hd (Subsingleton.elim d 0))

def successorFamily : SuccessorFamily parameters Unit 3 defect := by
  intro h lower d hd
  exact False.elim (hd (Subsingleton.elim d 0))

def endpoint : StrongPh 3 (3 + 1) defect :=
  strongPh_fin_index parameters Unit 3 defect base successorFamily

example : StrongPh 3 4 defect := by
  exact endpoint

def zeroExtraction : ∀ {d f : U} {Ω : List (LocalTest U U U)},
    defect d f Ω ≤ -1 → OriginalCofactors d f := by
  intro d f Ω h
  refine {R := 0, S := 0, identity := ?_}
  exact Subsingleton.elim _ _

example (d : U) (hd : d ≠ 0) (A : AffineSource U)
    (Ω : List (LocalTest U U U))
    (hΩ : AdmissibleTestList d Ω) :
    OriginalCofactors d (endpoint d hd A Ω hΩ).source := by
  exact terminal_cofactors_fin_index parameters Unit 3 defect base
    successorFamily zeroExtraction (defectBound_terminal 3)
    d hd A Ω hΩ

end SymplecticStafford.FiniteIndexOracle
