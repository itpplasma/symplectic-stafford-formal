import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations
import SymplecticStafford.Filtered.ReesNoetherianTransfer

/-!
# Polynomial-chart oracle for the filtered-to-Rees transfer

This is a concrete genuine additive filtration on `ℚ[X]`.  The oracle checks
the finite coefficient-lift interface on the polynomial chart and then
instantiates the transfer theorem with an explicit homogeneous-lifting
certificate as a local hypothesis.  The latter remains a supplied premise:
the oracle does not pretend that a polynomial filtration alone proves the
Noetherianity of its bounded Rees ring.
-/

namespace SymplecticStafford.Filtered

namespace ReesNoetherianTransferOracle

noncomputable section

open SymplecticStafford.Filtered

local instance : Algebra ℚ (Polynomial ℚ) := Polynomial.algebraOfAlgebra

def polynomialFiltration : AdditiveFilteredRingData (Polynomial ℚ) where
  carrier n :=
    { carrier := {p | p.natDegree ≤ n}
      zero_mem' := by simp
      add_mem' := by
        intro p q hp hq
        exact (Polynomial.natDegree_add_le p q).trans (max_le hp hq)
      neg_mem' := by
        intro p hp
        simpa [Polynomial.natDegree_neg] using hp }
  one_mem := by simp
  mul_mem := by
    intro i j p q hp hq
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq)
  monotone := by
    intro i j hij p hp
    exact hp.trans hij
  exhaustive := by
    intro p
    refine ⟨p.natDegree, ?_⟩
    change p.natDegree ≤ p.natDegree
    exact le_rfl

def polynomialLift (p : Polynomial ℚ) (n : ℕ)
    (hn : p.natDegree ≤ n) :
    ReesRing polynomialFiltration.toNegFiltrationData :=
  ReesRing.homogeneousLift polynomialFiltration.toNegFiltrationData n p
    (by exact hn)

example : Polynomial.X ∈ polynomialFiltration.carrier 1 := by
  change Polynomial.X.natDegree ≤ 1
  simp

example :
    (((polynomialLift (Polynomial.X + 1) 2 (by
      exact (Polynomial.natDegree_add_le _ _).trans (by simp)) :
      ReesRing polynomialFiltration.toNegFiltrationData) :
      ReesPolynomial (Polynomial ℚ)).coeff 2 = Polynomial.X + 1) := by
  exact ReesRing.homogeneousLift_coeff_eq
    polynomialFiltration.toNegFiltrationData 2 (Polynomial.X + 1) _

example (H : AdditiveFilteredRingData.HomogeneousIdealLifting polynomialFiltration) :
    IsNoetherianRing
      (AdditiveFilteredRingData.boundedReesRing polynomialFiltration) :=
  AdditiveFilteredRingData.isNoetherianRing_of_homogeneous_lifting
    polynomialFiltration H

end

end ReesNoetherianTransferOracle

end SymplecticStafford.Filtered
