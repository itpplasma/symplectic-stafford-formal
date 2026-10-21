module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import SymplecticStafford.Filtered.SymbolDenominatorSubmonoid

@[expose] public section

/-!
Independent oracle for the actual symbol-denominator construction.

The filtration is the ordinary degree filtration on `ℚ[X]`.  Its selected
symbol in degree `n` is the nonzero monomial class of `X^n`; the oracle checks
the multiplicative submonoid, least-degree API, and the representative-level
subtraction `X^2 - X` versus `X^2`.
-/

namespace SymplecticStafford.SymbolDenominatorSubmonoidOracle

open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.SymbolDenominatorSubmonoid

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

def monomialClass (n : ℕ) :
    AdditiveFilteredRingData.associatedLayer polynomialFiltration n :=
  AdditiveFilteredRingData.associatedClass polynomialFiltration n
    (Polynomial.X ^ n) (monomialMem n)

def Sigma (n : ℕ) : Set
    (AdditiveFilteredRingData.associatedLayer polynomialFiltration n) :=
  {monomialClass n}

def symbolData : Data polynomialFiltration where
  Sigma := Sigma
  one_mem := by
    change
      AdditiveFilteredRingData.associatedClass polynomialFiltration 0 1
          polynomialFiltration.one_mem ∈ {monomialClass 0}
    simpa [monomialClass]
  mul_mem := by
    intro i j x y hx hy
    rcases Set.mem_singleton_iff.mp hx with rfl
    rcases Set.mem_singleton_iff.mp hy with rfl
    change
      AdditiveFilteredRingData.associatedLayerMul polynomialFiltration i j
          (Submodule.Quotient.mk ⟨Polynomial.X ^ i, monomialMem i⟩)
          (Submodule.Quotient.mk ⟨Polynomial.X ^ j, monomialMem j⟩) ∈
        {monomialClass (i + j)}
    rw [AdditiveFilteredRingData.associatedLayerMul_mk_mk]
    simp [monomialClass, pow_add]
  zero_not_mem := by
    intro n hzero
    have hclass :
        (0 : AdditiveFilteredRingData.associatedLayer polynomialFiltration n) =
          monomialClass n := Set.mem_singleton_iff.mp hzero
    have hpred : Polynomial.X ^ n ∈
        AdditiveFilteredRingData.predecessor polynomialFiltration n :=
      (AdditiveFilteredRingData.associatedClass_eq_zero_iff
        polynomialFiltration n (Polynomial.X ^ n) (monomialMem n)).mp
        hclass.symm
    by_cases hn : n = 0
    · subst n
      simpa [AdditiveFilteredRingData.predecessor] using hpred
    · have hpred' : Polynomial.X ^ n ∈
          polynomialFiltration.carrier (n - 1) := by
        simpa [AdditiveFilteredRingData.predecessor, hn] using hpred
      change (Polynomial.X ^ n : Polynomial ℚ).natDegree ≤ n - 1 at hpred'
      have hdeg : (Polynomial.X ^ n : Polynomial ℚ).natDegree = n := by
        simp [hn]
      rw [hdeg] at hpred'
      omega

abbrev S : Submonoid (Polynomial ℚ) :=
  submonoid polynomialFiltration symbolData

def xMemCarrier : (Polynomial.X : Polynomial ℚ) ∈
    polynomialFiltration.carrier 1 := by
  change Polynomial.X.natDegree ≤ 1
  simp

def xSquaredMemCarrier : (Polynomial.X ^ 2 : Polynomial ℚ) ∈
    polynomialFiltration.carrier 2 := monomialMem 2

def xPred : (Polynomial.X : Polynomial ℚ) ∈
    AdditiveFilteredRingData.predecessor polynomialFiltration 2 := by
  change (Polynomial.X : Polynomial ℚ) ∈ polynomialFiltration.carrier (2 - 1)
  change Polynomial.X.natDegree ≤ 2 - 1
  simp

def xSelected :
    AdditiveFilteredRingData.associatedClass polynomialFiltration 1
        Polynomial.X xMemCarrier ∈ symbolData.Sigma 1 := by
  change
    AdditiveFilteredRingData.associatedClass polynomialFiltration 1
        Polynomial.X xMemCarrier ∈
      ({monomialClass 1} : Set
        (AdditiveFilteredRingData.associatedLayer polynomialFiltration 1))
  apply Set.mem_singleton_iff.mpr
  change
    AdditiveFilteredRingData.associatedClass polynomialFiltration 1
        Polynomial.X xMemCarrier =
      AdditiveFilteredRingData.associatedClass polynomialFiltration 1
        (Polynomial.X ^ 1) (monomialMem 1)
  apply (Submodule.Quotient.eq _).mpr
  change Polynomial.X - Polynomial.X ^ 1 ∈
    AdditiveFilteredRingData.predecessor polynomialFiltration 1
  simp

def xSquaredSelected :
    AdditiveFilteredRingData.associatedClass polynomialFiltration 2
        (Polynomial.X ^ 2) xSquaredMemCarrier ∈ symbolData.Sigma 2 := by
  change
    AdditiveFilteredRingData.associatedClass polynomialFiltration 2
        (Polynomial.X ^ 2) xSquaredMemCarrier ∈
      ({monomialClass 2} : Set
        (AdditiveFilteredRingData.associatedLayer polynomialFiltration 2))
  exact Set.mem_singleton _

def xSquaredSubMemCarrier : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ) ∈
    polynomialFiltration.carrier 2 := by
  exact (polynomialFiltration.carrier 2).sub_mem xSquaredMemCarrier
    (polynomialFiltration.monotone (by omega) xMemCarrier)

def xSquaredSubMem : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ) ∈ S :=
  sub_mem_of_selected_symbol polynomialFiltration symbolData
    xSquaredMemCarrier xSquaredSelected xPred

example : (1 : Polynomial ℚ) ∈ S := S.one_mem

example : (0 : Polynomial ℚ) ∉ S :=
  zero_not_mem polynomialFiltration symbolData

example : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ) ∈ S :=
  xSquaredSubMem

example : (Polynomial.X : Polynomial ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
  simpa using hc

example : (Polynomial.X : Polynomial ℚ) ∉
    polynomialFiltration.carrier 0 := by
  intro h
  change Polynomial.X.natDegree ≤ 0 at h
  simp at h

example : (Polynomial.X ^ 2 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 2) h
  simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc

example :
    AdditiveFilteredRingData.associatedClass polynomialFiltration 2
        (Polynomial.X ^ 2 - Polynomial.X) xSquaredSubMemCarrier =
      AdditiveFilteredRingData.associatedClass polynomialFiltration 2
        (Polynomial.X ^ 2) xSquaredMemCarrier := by
  exact associatedClass_sub_eq_of_mem_predecessor polynomialFiltration
    xSquaredMemCarrier xPred

example :
    AdditiveFilteredRingData.associatedClass polynomialFiltration 2
        (Polynomial.X ^ 2) xSquaredMemCarrier ≠ 0 := by
  intro hzero
  exact symbolData.zero_not_mem 2 (by
    rw [← hzero]
    exact xSquaredSelected)

example :
    AdditiveFilteredRingData.associatedClass polynomialFiltration 2
        (Polynomial.X ^ 2 - Polynomial.X) xSquaredSubMemCarrier ≠ 0 := by
  intro hzero
  have hEq := associatedClass_sub_eq_of_mem_predecessor polynomialFiltration
    xSquaredMemCarrier xPred
  have htop :
      AdditiveFilteredRingData.associatedClass polynomialFiltration 2
          (Polynomial.X ^ 2) xSquaredMemCarrier = 0 :=
    hEq.symm.trans hzero
  exact symbolData.zero_not_mem 2 (by
    rw [← htop]
    exact xSquaredSelected)

def xMem : (Polynomial.X : Polynomial ℚ) ∈ S := by
  exact (mem_submonoid_iff polynomialFiltration symbolData _).mpr
    ⟨1, xMemCarrier, xSelected⟩

example :
    degree polynomialFiltration symbolData xMem = 1 := by
  apply degree_eq_of_minimal polynomialFiltration symbolData
    (show Admissible polynomialFiltration symbolData
      (Polynomial.X : Polynomial ℚ) 1 from ⟨xMemCarrier, xSelected⟩)
  intro n hn hna
  have hn0 : n = 0 := by omega
  subst n
  rcases hna with ⟨h, _⟩
  change Polynomial.X.natDegree ≤ 0 at h
  simp at h

example :
    degree polynomialFiltration symbolData
      (show (Polynomial.X * Polynomial.X : Polynomial ℚ) ∈ S from
        S.mul_mem xMem xMem) = 2 := by
  rw [degree_mul polynomialFiltration symbolData xMem xMem]
  have hxdeg : degree polynomialFiltration symbolData xMem = 1 := by
    apply degree_eq_of_minimal polynomialFiltration symbolData
      (show Admissible polynomialFiltration symbolData
        (Polynomial.X : Polynomial ℚ) 1 from ⟨xMemCarrier, xSelected⟩)
    intro n hn hna
    have hn0 : n = 0 := by omega
    subst n
    rcases hna with ⟨h, _⟩
    change Polynomial.X.natDegree ≤ 0 at h
    simp at h
  rw [hxdeg]

end

end SymplecticStafford.SymbolDenominatorSubmonoidOracle

#print axioms
  SymplecticStafford.SymbolDenominatorSubmonoidOracle.symbolData
#print axioms
  SymplecticStafford.Filtered.SymbolDenominatorSubmonoid.degree_mul
