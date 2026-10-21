module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import SymplecticStafford.Filtered.RegularSymbolDegree

@[expose] public section

/-! Independent ordinary-degree calibration for regular-symbol cancellation. -/

namespace SymplecticStafford.RegularSymbolDegreeOracle

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.RegularSymbolDegree

noncomputable section

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

def monomialMem (n : ℕ) :
    (Polynomial.X ^ n : Polynomial ℚ) ∈ polynomialFiltration.carrier n := by
  change (Polynomial.X ^ n : Polynomial ℚ).natDegree ≤ n
  simp

private theorem class_zero_of_X_pow_mul_class_zero
    (i j : ℕ) (p : Polynomial ℚ)
    (hp : p ∈ polynomialFiltration.carrier j)
    (hprod :
      AdditiveFilteredRingData.associatedClass polynomialFiltration (i + j)
          ((Polynomial.X : Polynomial ℚ) ^ i * p)
          (polynomialFiltration.mul_mem (monomialMem i) hp) = 0) :
    AdditiveFilteredRingData.associatedClass polynomialFiltration j p hp = 0 := by
  have hprev : (Polynomial.X : Polynomial ℚ) ^ i * p ∈
      AdditiveFilteredRingData.predecessor polynomialFiltration (i + j) :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff polynomialFiltration
      (i + j) ((Polynomial.X : Polynomial ℚ) ^ i * p)
      (polynomialFiltration.mul_mem (monomialMem i) hp)).mp hprod
  by_cases hp0 : p = 0
  · subst p
    apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      polynomialFiltration j 0 hp).mpr
    exact (AdditiveFilteredRingData.predecessor polynomialFiltration j).zero_mem
  · have hsum0 : i + j ≠ 0 := by
      intro h
      rcases Nat.eq_zero_of_add_eq_zero h with ⟨hi, hj⟩
      subst i
      subst j
      have hz : p = 0 := by
        simpa [AdditiveFilteredRingData.predecessor] using hprev
      exact hp0 hz
    have hprev' : (Polynomial.X : Polynomial ℚ) ^ i * p ∈
        polynomialFiltration.carrier ((i + j) - 1) := by
      rw [AdditiveFilteredRingData.predecessor, if_neg hsum0] at hprev
      exact hprev
    change ((Polynomial.X : Polynomial ℚ) ^ i * p).natDegree ≤
      (i + j) - 1 at hprev'
    have hproddeg :
        ((Polynomial.X : Polynomial ℚ) ^ i * p).natDegree = p.natDegree + i := by
      exact Polynomial.natDegree_X_pow_mul i hp0
    have hpdeg : p.natDegree ≤ j - 1 := by
      rw [hproddeg] at hprev'
      omega
    apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      polynomialFiltration j p hp).mpr
    by_cases hj0 : j = 0
    · have : False := by omega
      exact this.elim
    · rw [AdditiveFilteredRingData.predecessor, if_neg hj0]
      change p.natDegree ≤ j - 1
      exact hpdeg

def xPowRegularSymbol (i : ℕ) :
    RegularSymbolDegree.Data polynomialFiltration i where
  representative := Polynomial.X ^ i
  representative_mem := monomialMem i
  symbol_ne_zero := by
    intro hzero
    have hpred :=
      (AdditiveFilteredRingData.associatedClass_eq_zero_iff polynomialFiltration
        i (Polynomial.X ^ i) (monomialMem i)).mp hzero
    by_cases hi : i = 0
    · subst i
      simpa [AdditiveFilteredRingData.predecessor] using hpred
    · have hpred' : (Polynomial.X : Polynomial ℚ) ^ i ∈
          polynomialFiltration.carrier (i - 1) := by
        rw [AdditiveFilteredRingData.predecessor, if_neg hi] at hpred
        exact hpred
      change ((Polynomial.X : Polynomial ℚ) ^ i).natDegree ≤ i - 1 at hpred'
      rw [Polynomial.natDegree_X_pow] at hpred'
      omega
  left_regular := by
    intro j y hy
    revert hy
    refine Quotient.inductionOn y ?_
    intro p hy
    change AdditiveFilteredRingData.associatedLayerMul polynomialFiltration i j
        (Submodule.Quotient.mk ⟨Polynomial.X ^ i, monomialMem i⟩)
        (Submodule.Quotient.mk p) = 0 at hy
    have hprod :
        AdditiveFilteredRingData.associatedClass polynomialFiltration (i + j)
            ((Polynomial.X : Polynomial ℚ) ^ i * p.1)
            (polynomialFiltration.mul_mem (monomialMem i) p.2) = 0 := by
      rw [AdditiveFilteredRingData.associatedLayerMul_mk_mk] at hy
      exact hy
    have hpzero := class_zero_of_X_pow_mul_class_zero i j p.1 p.2 hprod
    exact hpzero

def xPowRegularSymbol_1 := xPowRegularSymbol 1

example :
    (Polynomial.X : Polynomial ℚ) * Polynomial.X ^ 2 ∈
      polynomialFiltration.carrier 3 := by
  change ((Polynomial.X : Polynomial ℚ) * Polynomial.X ^ 2).natDegree ≤ 3
  simp

example :
    Polynomial.X ^ 2 ∈ polynomialFiltration.carrier 2 := by
  exact monomialMem 2

example :
    Polynomial.X ^ 2 ∉ polynomialFiltration.carrier 1 := by
  intro h
  change ((Polynomial.X : Polynomial ℚ) ^ 2).natDegree ≤ 1 at h
  simp at h

example :
    (xPowRegularSymbol_1.representative * (Polynomial.X ^ 2 : Polynomial ℚ)) ∈
      polynomialFiltration.carrier 3 := by
  change (xPowRegularSymbol_1.representative *
      (Polynomial.X ^ 2 : Polynomial ℚ)).natDegree ≤ 3
  simp [xPowRegularSymbol_1, xPowRegularSymbol]

example :
    Polynomial.X ^ 2 ∈ polynomialFiltration.carrier (3 - 1) := by
  exact (xPowRegularSymbol_1.degree_controlled_mul
    (by
      change (xPowRegularSymbol_1.representative *
          (Polynomial.X ^ 2 : Polynomial ℚ)).natDegree ≤ 3
      simp [xPowRegularSymbol_1, xPowRegularSymbol])).1 (by omega)

example :
    (Polynomial.X ^ 2 : Polynomial ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 2) h
  simpa using hc

example :
    ¬ ((xPowRegularSymbol_1.representative *
        (Polynomial.X ^ 2 : Polynomial ℚ)) ∈
      polynomialFiltration.carrier 0) := by
  intro hcontra
  have hzero :=
    (xPowRegularSymbol_1.degree_controlled_mul hcontra).2 (by omega)
  have hne : (Polynomial.X ^ 2 : Polynomial ℚ) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 2) h
    simpa using hc
  exact hne hzero

end

end SymplecticStafford.RegularSymbolDegreeOracle

#print axioms
  SymplecticStafford.RegularSymbolDegreeOracle.xPowRegularSymbol
#print axioms
  SymplecticStafford.Filtered.RegularSymbolDegree.Data.degree_controlled_mul
