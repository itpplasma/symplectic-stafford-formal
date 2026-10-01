import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic
import SymplecticStafford.Filtered.M01FiniteHomogeneousReesProducer

/-!
# Independent oracle for the bounded M01 homogeneous-symbol producer

The oracle uses the genuine degree filtration on `ℚ[X]`, feeds the nonzero
element `X^2` to the producer, forces the selected degree to be two, and
consumes its nonzero quotient class, nonzero Rees lift, coefficient identity,
and multiplicative coefficient-symbol transport with the degree-one class of
`X`.
-/

namespace SymplecticStafford.M01FiniteHomogeneousReesProducerOracle

noncomputable section

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.AdditiveFilteredRingData

local instance : Algebra ℚ (Polynomial ℚ) := Polynomial.algebraOfAlgebra

def polynomialFiltration : AdditiveFilteredRingData (Polynomial ℚ) where
  carrier n :=
    { carrier := {p | p.natDegree ≤ n}
      zero_mem' := by simp
      add_mem' := by
        intro p q hp hq
        exact (Polynomial.natDegree_add_le p q).trans
          (max_le hp hq)
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
    exact ⟨p.natDegree, show p.natDegree ≤ p.natDegree from le_rfl⟩

theorem degreeOneMem : Polynomial.X ∈ polynomialFiltration.carrier 1 := by
  change Polynomial.X.natDegree ≤ 1
  simp

def degreeOneClass :
    AdditiveFilteredRingData.associatedLayer polynomialFiltration 1 :=
  AdditiveFilteredRingData.associatedClass polynomialFiltration 1
    Polynomial.X degreeOneMem

theorem polynomial_producer_behaves :
    ∃ n : ℕ, ∃ hna : (Polynomial.X ^ 2) ∈ polynomialFiltration.carrier n,
      n = 2 ∧
      (∀ k < n, (Polynomial.X ^ 2) ∉ polynomialFiltration.carrier k) ∧
      let q := AdditiveFilteredRingData.associatedClass
        polynomialFiltration n (Polynomial.X ^ 2) hna
      let x := ActualAssociatedGraded.representative polynomialFiltration n q
      let p := ReesNoetherianTransfer.shiftedHomogeneousLift
        polynomialFiltration n 0 q
      q ≠ 0 ∧
      p ≠ 0 ∧
      ((p : ReesPolynomial (Polynomial ℚ)).coeff n = (x : Polynomial ℚ)) ∧
      AdditiveFilteredRingData.associatedClass polynomialFiltration n
          (x : Polynomial ℚ) x.property = q ∧
      ReesNoetherianTransfer.CoefficientSymbol polynomialFiltration n p
          (Finsupp.single 0 q) ∧
      ∀ m y,
        ReesNoetherianTransfer.CoefficientSymbol polynomialFiltration (n + m)
          (p * ReesNoetherianTransfer.shiftedHomogeneousLift
            polynomialFiltration m 0 y)
          (Finsupp.single 0
            (AdditiveFilteredRingData.associatedLayerMul
              polynomialFiltration n m q y)) := by
  obtain ⟨n, hna, hmin, hq, hp, hpcoeff, hxclass, hsymbol, hmul⟩ :=
    exists_minimal_layer_homogeneous_symbol polynomialFiltration
      (a := Polynomial.X ^ 2) (by simp)
  have hlow : 2 ≤ n := by
    have h := hna
    change (Polynomial.X ^ 2).natDegree ≤ n at h
    simpa using h
  have hn : n = 2 := by
    apply Nat.le_antisymm
    · by_contra h
      have hlt : 2 < n := by omega
      apply hmin 2 hlt
      change (Polynomial.X ^ 2).natDegree ≤ 2
      simp
    · exact hlow
  refine ⟨n, hna, hn, hmin, ?_⟩
  simpa using And.intro hq
    (And.intro hp
      (And.intro hpcoeff
        (And.intro hxclass
          (And.intro hsymbol hmul))))

example :
    ∃ n : ℕ, ∃ hna : (Polynomial.X ^ 2) ∈ polynomialFiltration.carrier n,
      n = 2 := by
  obtain ⟨n, hna, hn, _⟩ := polynomial_producer_behaves
  exact ⟨n, hna, hn⟩

example :
    AdditiveFilteredRingData.associatedClass polynomialFiltration 1
        Polynomial.X degreeOneMem ≠ 0 := by
  intro hzero
  have hpred :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      polynomialFiltration 1 Polynomial.X degreeOneMem).mp hzero
  change Polynomial.X.natDegree ≤ 0 at hpred
  simp at hpred

example :
    ∃ n : ℕ, ∃ hna : (Polynomial.X ^ 2) ∈ polynomialFiltration.carrier n,
      n = 2 ∧
      let q := AdditiveFilteredRingData.associatedClass
        polynomialFiltration n (Polynomial.X ^ 2) hna
      let p := ReesNoetherianTransfer.shiftedHomogeneousLift
        polynomialFiltration n 0 q
      ReesNoetherianTransfer.CoefficientSymbol polynomialFiltration (n + 1)
        (p * ReesNoetherianTransfer.shiftedHomogeneousLift
          polynomialFiltration 1 0 degreeOneClass)
        (Finsupp.single 0
          (AdditiveFilteredRingData.associatedLayerMul
            polynomialFiltration n 1 q degreeOneClass)) := by
  obtain ⟨n, hna, hmin, hq, hp, hpcoeff, hxclass, hsymbol, hmul⟩ :=
    exists_minimal_layer_homogeneous_symbol polynomialFiltration
      (a := Polynomial.X ^ 2) (by simp)
  have hlow : 2 ≤ n := by
    have h := hna
    change (Polynomial.X ^ 2).natDegree ≤ n at h
    simpa using h
  have hn : n = 2 := by
    apply Nat.le_antisymm
    · by_contra h
      have hlt : 2 < n := by omega
      apply hmin 2 hlt
      change (Polynomial.X ^ 2).natDegree ≤ 2
      simp
    · exact hlow
  refine ⟨n, hna, hn, ?_⟩
  simpa using hmul 1 degreeOneClass

end

end SymplecticStafford.M01FiniteHomogeneousReesProducerOracle

#print axioms
  SymplecticStafford.M01FiniteHomogeneousReesProducerOracle.polynomial_producer_behaves
