module

public import SymplecticStafford.Filtered.BoundedReesBridge

@[expose] public section

/-!
# Independent oracle for the bounded Rees bridge

The filtration below is the full filtration on `ℚ`.  The checks compute
coefficients of a concrete two-term lift directly in the ambient skew
polynomial algebra, and separately verify that a one-term lift is nonzero.
They exercise the coefficient/support behavior rather than merely checking
that the declarations in `BoundedReesBridge` have the expected types.
-/

namespace SymplecticStafford.Filtered

open Multiplicative SkewMonoidAlgebra

def rationalFullFiltration : NegFiltrationData ℚ where
  carrier := fun _ => Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; exact hx
  exhaustive := by intro q; exact ⟨0, by simp⟩
  neg_mem := by simp

noncomputable def twoTerm : ReesRing rationalFullFiltration :=
  ReesRing.homogeneousLift rationalFullFiltration 0 3 (by simp [rationalFullFiltration]) +
    ReesRing.homogeneousLift rationalFullFiltration 2 5 (by simp [rationalFullFiltration])

example :
    ((twoTerm : ReesRing rationalFullFiltration) : ReesPolynomial ℚ).coeff 0 = 3 := by
  unfold twoTerm
  change ((SkewPolynomial.monomial 0 3 + SkewPolynomial.monomial 2 5 :
      ReesPolynomial ℚ).coeff 0) = 3
  simp [SkewPolynomial.coeff_add, SkewPolynomial.coeff_monomial]

example :
    ((twoTerm : ReesRing rationalFullFiltration) : ReesPolynomial ℚ).coeff 2 = 5 := by
  unfold twoTerm
  change ((SkewPolynomial.monomial 0 3 + SkewPolynomial.monomial 2 5 :
      ReesPolynomial ℚ).coeff 2) = 5
  simp [SkewPolynomial.coeff_add, SkewPolynomial.coeff_monomial]

example :
    ((twoTerm : ReesRing rationalFullFiltration) : ReesPolynomial ℚ).coeff 1 = 0 := by
  unfold twoTerm
  change ((SkewPolynomial.monomial 0 3 + SkewPolynomial.monomial 2 5 :
      ReesPolynomial ℚ).coeff 1) = 0
  simp [SkewPolynomial.coeff_add, SkewPolynomial.coeff_monomial]

example :
    ReesRing.homogeneousLift rationalFullFiltration 3 7
      (by simp [rationalFullFiltration]) ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun p : ReesRing rationalFullFiltration =>
      ((p : ReesPolynomial ℚ).coeff 3)) h
  have hseven :
      ((ReesRing.homogeneousLift rationalFullFiltration 3 7
        (by simp [rationalFullFiltration]) : ReesRing rationalFullFiltration) :
        ReesPolynomial ℚ).coeff 3 = 7 :=
    ReesRing.homogeneousLift_coeff_eq rationalFullFiltration 3 7 _
  have hzero :
      ((ReesRing.homogeneousLift rationalFullFiltration 3 7
        (by simp [rationalFullFiltration]) : ReesRing rationalFullFiltration) :
        ReesPolynomial ℚ).coeff 3 = 0 := by
    simpa using hcoeff
  rw [hseven] at hzero
  norm_num at hzero

end SymplecticStafford.Filtered
