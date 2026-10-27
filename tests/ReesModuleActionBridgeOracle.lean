module

public import SymplecticStafford.Filtered.ReesModuleActionBridge

@[expose] public section

/-!
Independent checks for the concrete action bridge.  The examples use the
constant exhaustive filtration, so every displayed coefficient has a
bounded witness.  They check the actual ring homomorphism, its homogeneous
values, and the resulting `Module (ReesRing F) ℤ` instance. -/

namespace SymplecticStaffordTest.ReesModuleActionBridge

open SymplecticStafford.Filtered

noncomputable section

def constantFiltration : NegFiltrationData ℤ where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩
  neg_mem := by simp

def homogeneous (n : ℕ) (a : ℤ) : ReesRing constantFiltration :=
  ReesRing.monomial constantFiltration n a (by simp [constantFiltration])

example (n : ℕ) (a : ℤ) :
    ReesRing.evaluationAtOne constantFiltration (homogeneous n a) = a := by
  exact ReesRing.evaluationAtOne_monomial constantFiltration n a _

example (n : Multiplicative ℕ) (a : ℤ) :
    ReesRing.polynomialEvaluationAtOne (R := ℤ)
        (SkewMonoidAlgebra.single n a) = a := by
  exact ReesRing.polynomialEvaluationAtOne_single n a

example (p : ReesRing constantFiltration) (x : ℤ) :
    letI : Module (ReesRing constantFiltration) ℤ :=
      ReesRing.moduleViaEvaluationAtOne constantFiltration ℤ
    p • x = ReesRing.evaluationAtOne constantFiltration p • x := by
  rfl

example : Function.Surjective (ReesRing.evaluationAtOne constantFiltration) := by
  intro z
  refine ⟨homogeneous 0 z, ?_⟩
  exact ReesRing.evaluationAtOne_monomial constantFiltration 0 z _

end

end SymplecticStaffordTest.ReesModuleActionBridge
