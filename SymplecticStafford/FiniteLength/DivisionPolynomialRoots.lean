module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-!
Central scalar roots of a nonzero polynomial over an arbitrary algebra.
A separating linear functional produces a nonzero scalar polynomial. This
requires no finite-dimensionality over the center. It supplies the root-set
step for division-ring pencil denominators; generic matrix invertibility
and the production of those denominators are separate obligations.

Drafting wave: source written without a compiler run.
-/

namespace SymplecticStafford.FiniteLength.DivisionPolynomialRoots

open Polynomial

universe u v
variable {k : Type u} {D : Type v} [Field k] [Ring D] [Algebra k D]

noncomputable section

/-- Apply a scalar-valued linear functional to every coefficient. -/
def projectCoefficients (φ : Module.Dual k D) (p : D[X]) : k[X] :=
  ∑ n ∈ p.support, Polynomial.monomial n (φ (p.coeff n))

theorem projectCoefficients_coeff (φ : Module.Dual k D) (p : D[X]) (n : ℕ) :
    (projectCoefficients φ p).coeff n = φ (p.coeff n) := by
  classical
  by_cases hn : n ∈ p.support
  · simp [projectCoefficients, Polynomial.coeff_monomial, hn]
  · have hz : p.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [projectCoefficients, Polynomial.coeff_monomial, hn, hz]

/-- Only central scalar evaluation is transported through the functional. -/
theorem projectCoefficients_eval (φ : Module.Dual k D) (p : D[X]) (a : k) :
    φ (p.eval (algebraMap k D a)) = (projectCoefficients φ p).eval a := by
  classical
  conv_lhs => rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [projectCoefficients, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hmul : p.coeff n * (algebraMap k D a) ^ n =
      (a ^ n) • p.coeff n := by
    rw [← map_pow, Algebra.smul_def]
    exact (Algebra.commutes (a ^ n) (p.coeff n)).symm
  rw [hmul, map_smul]
  exact mul_comm _ _

/-- A nonzero algebra-valued polynomial has finitely many roots among the
central scalars, even when the algebra is infinite-dimensional over `k`. -/
theorem finite_central_roots (p : D[X]) (hp : p ≠ 0) :
    {a : k | p.eval (algebraMap k D a) = 0}.Finite := by
  classical
  have hn : p.coeff p.natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using
      (Polynomial.leadingCoeff_ne_zero.mpr hp)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k D,
      φ (p.coeff p.natDegree) ≠ 0 := by
    by_contra! hall
    exact hn ((Module.forall_dual_apply_eq_zero_iff k _).mp hall)
  let q : k[X] := projectCoefficients φ p
  have hq : q ≠ 0 := by
    intro hz
    have hc := congrArg (fun f : k[X] => f.coeff p.natDegree) hz
    rw [show q = projectCoefficients φ p from rfl,
      projectCoefficients_coeff, Polynomial.coeff_zero] at hc
    exact hφ hc
  apply q.roots.toFinset.finite_toSet.subset
  intro a ha
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq]
  change q.eval a = 0
  rw [show q = projectCoefficients φ p from rfl,
    ← projectCoefficients_eval, ha, map_zero]

/-- Finitely many nonzero denominator polynomials have one finite exceptional
set of central scalar values. -/
theorem finite_bad_scalars {ι : Type*} (s : Finset ι) (p : ι → D[X])
    (hp : ∀ i ∈ s, p i ≠ 0) :
    {a : k | ∃ i ∈ s, (p i).eval (algebraMap k D a) = 0}.Finite := by
  classical
  have h : (⋃ i ∈ (s : Set ι),
      {a : k | (p i).eval (algebraMap k D a) = 0}).Finite :=
    s.finite_toSet.biUnion (fun i hi => finite_central_roots (p i) (hp i hi))
  convert h using 1
  ext a
  simp

end
end SymplecticStafford.FiniteLength.DivisionPolynomialRoots

#print axioms SymplecticStafford.FiniteLength.DivisionPolynomialRoots.finite_central_roots
#print axioms SymplecticStafford.FiniteLength.DivisionPolynomialRoots.finite_bad_scalars
