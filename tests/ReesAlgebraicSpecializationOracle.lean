module

public import SymplecticStafford.Filtered.ReesAlgebraicSpecialization
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Independent behavioral oracle for finite algebraic Rees specialization. -/
namespace SymplecticStaffordTest.ReesAlgebraicSpecialization

open SymplecticStafford.Filtered

noncomputable section

def integerFiltration : NegFiltrationData ℤ where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩
  neg_mem := by simp

def term (n : ℕ) (a : ℤ) : ReesTerm integerFiltration.toFiltrationData :=
  ⟨n, a, by simp [integerFiltration, HasDegreeAtMost]⟩

def terms : Fin 2 → ReesTerm integerFiltration.toFiltrationData
  | 0 => term 1 3
  | 1 => term 4 5

def indices : Finset (Fin 2) := {0, 1}

example :
    ReesAlgebraicSpecialization.finiteEvaluate integerFiltration indices terms = 8 := by
  norm_num [ReesAlgebraicSpecialization.finiteEvaluate_eq_sum, terms, term, indices]

example :
    ReesAlgebraicSpecialization.finiteEvaluate integerFiltration indices terms * 2 = 16 := by
  norm_num [ReesAlgebraicSpecialization.finiteEvaluate_eq_sum, terms, term, indices]

example :
    ReesAlgebraicSpecialization.finiteEvaluate integerFiltration indices terms • (7 : ℤ) = 56 := by
  norm_num [ReesAlgebraicSpecialization.finiteLift_smul, terms, term, indices]

def moduleFiltration : ModuleFiltrationData integerFiltration.toFiltrationData ℤ where
  carrier _ := Set.univ
  zero_mem := by simp
  add_mem := by simp
  smul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩

def shiftByThree :
    ShiftedFilteredLinearMap integerFiltration.toFiltrationData
      moduleFiltration moduleFiltration 3 where
  toFun := id
  map_zero' := rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl
  filtered' := by intro n x hx; simp [moduleFiltration]

def moduleTerms : Fin 2 → ReesModuleTerm moduleFiltration
  | 0 => ⟨2, 4, by simp [moduleFiltration, ModuleHasDegreeAtMost]⟩
  | 1 => ⟨5, 6, by simp [moduleFiltration, ModuleHasDegreeAtMost]⟩

example :
    ReesAlgebraicSpecialization.finiteShiftedEvaluate integerFiltration
      shiftByThree indices moduleTerms = 10 := by
  norm_num [ReesAlgebraicSpecialization.finiteShiftedEvaluate_eq_sum,
    moduleTerms, shiftByThree, indices]

example (a : ReesTerm integerFiltration.toFiltrationData) :
    ReesAlgebraicSpecialization.finiteShiftedEvaluate integerFiltration
      shiftByThree indices
      (fun i => ReesModuleTerm.smul a (moduleTerms i)) =
      a.value •
        ReesAlgebraicSpecialization.finiteShiftedEvaluate integerFiltration
          shiftByThree indices moduleTerms := by
  exact ReesAlgebraicSpecialization.finiteShiftedEvaluate_smul
    integerFiltration shiftByThree a indices moduleTerms

example (c : ReesRing integerFiltration) (x : ℤ) :
    shiftByThree.toFun (ReesRing.evaluationAtOne integerFiltration c • x) =
      ReesRing.evaluationAtOne integerFiltration c • shiftByThree.toFun x := by
  exact ReesAlgebraicSpecialization.shiftedMap_preserves_evaluation_action
    integerFiltration shiftByThree c x

example :
    ReesAlgebraicSpecialization.finiteShiftedEvaluate integerFiltration
      shiftByThree indices
      (fun i => ReesModuleTerm.reindex (moduleTerms i)
        (show (moduleTerms i).degree ≤ 6 by fin_cases i <;>
          simp [moduleTerms])) = 10 := by
  have h := ReesAlgebraicSpecialization.finiteShiftedEvaluate_reindex_invariant
    integerFiltration shiftByThree indices moduleTerms (fun _ => 6)
      (by intro i; fin_cases i <;> simp [moduleTerms])
  calc
    _ = ReesAlgebraicSpecialization.finiteShiftedEvaluate integerFiltration
        shiftByThree indices moduleTerms := h
    _ = 10 := by
      norm_num [ReesAlgebraicSpecialization.finiteShiftedEvaluate_eq_sum,
        moduleTerms, indices, shiftByThree]

def divisor : ReesTerm integerFiltration.toFiltrationData := term 2 1
def source : ReesTerm integerFiltration.toFiltrationData := term 1 8

def boundedCertificate :
    ReesAlgebraicSpecialization.BoundedCofactorData integerFiltration divisor source where
  right₁ := term 0 1
  right₂ := term 0 0
  identity := by norm_num [divisor, source, term]

example :
    (1 : ℤ) ∈ SymplecticStafford.twoGeneratedRightIdeal 1 8 := by
  exact ReesAlgebraicSpecialization.BoundedCofactorData.original_membership
    integerFiltration boundedCertificate

example :
    (ReesAlgebraicSpecialization.BoundedCofactorData.toCertificate
      integerFiltration boundedCertificate).right₁ = 1 := by
  rfl

example :
    (1 : ℤ) = 1 *
        (ReesAlgebraicSpecialization.BoundedCofactorData.toCertificate
          integerFiltration boundedCertificate).right₁ +
      (8 * 1) *
        (ReesAlgebraicSpecialization.BoundedCofactorData.toCertificate
          integerFiltration boundedCertificate).right₂ := by
  exact ReesAlgebraicSpecialization.BoundedCofactorData.certificate_identity
    integerFiltration boundedCertificate

end

end SymplecticStaffordTest.ReesAlgebraicSpecialization
