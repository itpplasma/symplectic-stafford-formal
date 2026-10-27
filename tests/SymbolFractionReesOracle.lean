module

public import Mathlib.Tactic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import SymplecticStafford.Filtered.SymbolFractionRees

@[expose] public section

/-!
Independent polynomial oracle for the Laurent Rees grading. The actual
right Ore localization contains nonzero 1/X of degree -1. Explicit single
terms X in degree 1 and 1/X in degree -1 multiply to one in both orders,
using ambient multiplication and denominator cancellation.
-/

namespace SymplecticStaffordTest.SymbolFractionReesOracle

open Polynomial
open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.SymbolDenominatorSubmonoid
open SymplecticStafford.Filtered.SymbolFractionInverse
open SymplecticStafford.Filtered.SymbolFractionFiltration
open AlgebraicAnalysis.OreRightLocalization

noncomputable section

def polyCarrier (n : ℕ) : AddSubgroup (ℚ[X]) where
  carrier := {p | p.natDegree ≤ n}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    exact (natDegree_add_le p q).trans (max_le hp hq)
  neg_mem' := by
    intro p hp
    simpa [natDegree_neg] using hp

def polyFiltration : AdditiveFilteredRingData (ℚ[X]) where
  carrier := polyCarrier
  one_mem := by simp [polyCarrier]
  mul_mem := by
    intro i j p q hp hq
    exact natDegree_mul_le_of_le hp hq
  monotone := by
    intro i j hij p hp
    change p.natDegree ≤ j
    exact hp.trans hij
  exhaustive := by
    intro p
    exact ⟨p.natDegree, by change p.natDegree ≤ p.natDegree; exact le_rfl⟩

private theorem xpow_mem (n : ℕ) :
    (X ^ n : ℚ[X]) ∈ polyFiltration.carrier n := by
  change (X ^ n).natDegree ≤ n
  simp [polyCarrier]

private theorem xpow_class_ne_zero (n : ℕ) :
    AdditiveFilteredRingData.associatedClass polyFiltration n (X ^ n)
        (xpow_mem n) ≠ 0 := by
  intro hzero
  have hpred :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff polyFiltration n
      (X ^ n) (xpow_mem n)).mp hzero
  by_cases hn : n = 0
  · subst n
    simpa [AdditiveFilteredRingData.predecessor] using hpred
  · rw [AdditiveFilteredRingData.predecessor, if_neg hn] at hpred
    change (X ^ n).natDegree ≤ n - 1 at hpred
    rw [natDegree_X_pow] at hpred
    omega

def polySymbols : SymbolDenominatorSubmonoid.Data polyFiltration where
  Sigma := fun n =>
    {AdditiveFilteredRingData.associatedClass polyFiltration n (X ^ n)
      (xpow_mem n)}
  one_mem := by
    rw [Set.mem_singleton_iff]
    simp [pow_zero]
  mul_mem := by
    intro i j x y hx hy
    rw [Set.mem_singleton_iff] at hx hy ⊢
    subst x
    subst y
    change AdditiveFilteredRingData.associatedLayerMul polyFiltration i j
      (Submodule.Quotient.mk ⟨X ^ i, xpow_mem i⟩)
      (Submodule.Quotient.mk ⟨X ^ j, xpow_mem j⟩) = _
    rw [AdditiveFilteredRingData.associatedLayerMul_mk_mk]
    simp [pow_add]
  zero_not_mem := by
    intro n hn
    rw [Set.mem_singleton_iff] at hn
    exact xpow_class_ne_zero n hn.symm

def polyLocalization : FullSymbolRightLocalization.Data (ℚ[X]) where
  denominators := SymbolDenominatorSubmonoid.submonoid polyFiltration polySymbols
  regular := by
    intro s hs p hzero
    rcases (mem_submonoid_iff polyFiltration polySymbols (s : ℚ[X])).mp hs with
      ⟨n, hs, hSigma⟩
    have hs0 : (s : ℚ[X]) ≠ 0 := by
      intro hs0
      subst s
      apply associatedClass_ne_zero_of_mem_sigma polyFiltration polySymbols hSigma
      apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff
        polyFiltration n 0 hs).mpr
      exact (AdditiveFilteredRingData.predecessor polyFiltration n).zero_mem
    exact (mul_eq_zero.mp hzero).resolve_right hs0
  ore := inferInstance

abbrev concreteInverse : SymbolFractionInverse.Data (ℚ[X]) where
  filtration := polyFiltration
  symbols := polySymbols
  localization := polyLocalization
  denominators_eq_submonoid := rfl

theorem polyDegreeZero : (1 : ℚ[X]) ∈ polyFiltration.carrier 0 := by
  change (1 : ℚ[X]).natDegree ≤ 0
  simp

def xDenominator : concreteInverse.localization.denominators :=
  ⟨X, by
    rw [concreteInverse.denominators_eq_submonoid]
    have hx : X ∈ concreteInverse.filtration.carrier 1 := by
      change X.natDegree ≤ 1
      simp
    have hclass :
        AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1 X hx ∈
          concreteInverse.symbols.Sigma 1 := by
      change AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1 X hx ∈
        {AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1
          (X ^ 1) (by
            change (X ^ 1).natDegree ≤ 1
            simp)}
      rw [Set.mem_singleton_iff]
      simp [pow_one]
    exact ⟨1, ⟨hx, hclass⟩⟩⟩

def xSubOneDenominator : concreteInverse.localization.denominators :=
  ⟨X - 1, by
    rw [concreteInverse.denominators_eq_submonoid]
    have hx : X ∈ concreteInverse.filtration.carrier 1 := by
      change X.natDegree ≤ 1
      simp
    have hclass :
        AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1 X hx ∈
          concreteInverse.symbols.Sigma 1 := by
      simp [polySymbols]
    have hpred : (1 : ℚ[X]) ∈
        AdditiveFilteredRingData.predecessor concreteInverse.filtration 1 := by
      rw [AdditiveFilteredRingData.predecessor]
      change (1 : ℚ[X]).natDegree ≤ 0
      simp
    exact sub_mem_of_selected_symbol concreteInverse.filtration concreteInverse.symbols
      hx hclass hpred⟩

private theorem xpow_left_regular (i j : ℕ)
    (y : AdditiveFilteredRingData.associatedLayer concreteInverse.filtration j)
    (hy : AdditiveFilteredRingData.associatedLayerMul concreteInverse.filtration i j
      (AdditiveFilteredRingData.associatedClass concreteInverse.filtration i
        (X ^ i) (xpow_mem i)) y = 0) : y = 0 := by
  revert hy
  refine Quotient.inductionOn y ?_
  intro p hy
  change AdditiveFilteredRingData.associatedLayerMul concreteInverse.filtration i j
      (Submodule.Quotient.mk ⟨X ^ i, xpow_mem i⟩) (Submodule.Quotient.mk p) = 0 at hy
  have hprod :
      AdditiveFilteredRingData.associatedClass concreteInverse.filtration (i + j)
        ((X : ℚ[X]) ^ i * p.1)
        (concreteInverse.filtration.mul_mem (xpow_mem i) p.2) = 0 := by
    rw [AdditiveFilteredRingData.associatedLayerMul_mk_mk] at hy
    exact hy
  have hprev :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff concreteInverse.filtration
      (i + j) ((X : ℚ[X]) ^ i * p.1)
      (concreteInverse.filtration.mul_mem (xpow_mem i) p.2)).mp hprod
  by_cases hp0 : p.1 = 0
  · have hp : p = 0 := Subtype.ext hp0
    subst p
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.zero_mem _
  · have hsum0 : i + j ≠ 0 := by
      intro h
      rcases Nat.eq_zero_of_add_eq_zero h with ⟨hi, hj⟩
      subst i
      subst j
      have : p.1 = 0 := by simpa [AdditiveFilteredRingData.predecessor] using hprev
      exact hp0 this
    rw [AdditiveFilteredRingData.predecessor, if_neg hsum0] at hprev
    change ((X : ℚ[X]) ^ i * p.1).natDegree ≤ (i + j) - 1 at hprev
    have hdeg : ((X : ℚ[X]) ^ i * p.1).natDegree = p.1.natDegree + i :=
      Polynomial.natDegree_X_pow_mul i hp0
    have hpdeg : p.1.natDegree ≤ j - 1 := by
      rw [hdeg] at hprev
      omega
    apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff
      concreteInverse.filtration j p.1 p.2).mpr
    by_cases hj0 : j = 0
    · omega
    · rw [AdditiveFilteredRingData.predecessor, if_neg hj0]
      change p.1.natDegree ≤ j - 1
      exact hpdeg

abbrev concreteData : SymbolFractionFiltration.Data (ℚ[X]) where
  inverse := concreteInverse
  left_regular := by
    intro s n hs hSigma j y hy
    change AdditiveFilteredRingData.associatedClass concreteInverse.filtration n
        (s : ℚ[X]) hs ∈
      {AdditiveFilteredRingData.associatedClass concreteInverse.filtration n
        (X ^ n) (xpow_mem n)} at hSigma
    rw [Set.mem_singleton_iff] at hSigma
    have hpow :
        AdditiveFilteredRingData.associatedClass concreteInverse.filtration n
            (s : ℚ[X]) hs =
          AdditiveFilteredRingData.associatedClass concreteInverse.filtration n
            (X ^ n) (xpow_mem n) := hSigma
    rw [hpow] at hy
    exact xpow_left_regular n j y hy

private theorem rightFraction_mul_denominator
    (a : ℚ[X]) (s : concreteInverse.localization.denominators) :
    concreteInverse.rightFraction a s *
        concreteInverse.localization.numerator (s : ℚ[X]) =
      concreteInverse.localization.numerator a := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid concreteInverse.localization.denominators) :=
    concreteInverse.localization.ore
  apply MulOpposite.unop_injective
  rw [show concreteInverse.rightFraction a s = MulOpposite.op
      (OreLocalization.oreDiv (MulOpposite.op a)
        (⟨MulOpposite.op (s : ℚ[X]), s.property⟩ :
          oppositeSubmonoid concreteInverse.localization.denominators)) by
        rfl]
  exact OreLocalization.mul_cancel
    (R := (ℚ[X])ᵐᵒᵖ)
    (S := oppositeSubmonoid concreteInverse.localization.denominators)
    (r := MulOpposite.op a)
    (s := (⟨MulOpposite.op (s : ℚ[X]), s.property⟩ :
      oppositeSubmonoid concreteInverse.localization.denominators))
    (t := (1 : oppositeSubmonoid concreteInverse.localization.denominators))

private theorem x_mem :
    (xDenominator : ℚ[X]) ∈ concreteInverse.filtration.carrier 1 := by
  change X.natDegree ≤ 1
  simp

private theorem x_sigma :
    AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1
        (xDenominator : ℚ[X]) x_mem ∈ concreteInverse.symbols.Sigma 1 := by
  dsimp [xDenominator]
  change AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1 X _ ∈
    {AdditiveFilteredRingData.associatedClass concreteInverse.filtration 1
      (X ^ 1) (by
        change (X ^ 1).natDegree ≤ 1
        simp)}
  rw [Set.mem_singleton_iff]
  simp [pow_one]

private theorem denominator_degree_x :
    concreteInverse.denominator_degree xDenominator = 1 := by
  have hna : SymbolDenominatorSubmonoid.Admissible concreteInverse.filtration
      concreteInverse.symbols (xDenominator : ℚ[X]) 1 := ⟨x_mem, x_sigma⟩
  simpa [SymbolFractionInverse.Data.denominator_degree, xDenominator] using
    SymbolDenominatorSubmonoid.degree_eq_of_admissible
      concreteInverse.filtration concreteInverse.symbols hna

def oneOverX : concreteData.inverse.localization.Localization :=
  concreteData.inverse.rightFraction 1 xDenominator

private theorem oneOverX_mem_minus_one :
    oneOverX ∈ concreteData.fractionFiltration (-1) := by
  change concreteInverse.fractionDegreeAtMost (-1 : ℤ)
    (concreteInverse.rightFraction 1 xDenominator)
  refine Or.inr ⟨1, xDenominator, 0, ?_, ?_, ?_⟩
  · exact polyDegreeZero
  · exact rightFraction_mul_denominator 1 xDenominator
  · rw [denominator_degree_x]
    norm_num

private theorem oneOverX_ne_zero : oneOverX ≠ 0 := by
  change concreteInverse.rightFraction 1 xDenominator ≠ 0
  intro hz
  have hmul := rightFraction_mul_denominator 1 xDenominator
  have hnum : concreteInverse.localization.numerator (1 : ℚ[X]) = 0 := by
    rw [← hmul, hz, zero_mul]
  have hone : (1 : ℚ[X]) = 0 :=
    concreteInverse.localization.numerator_injective (by simpa using hnum)
  exact one_ne_zero hone

private theorem oneOverX_mem_zero :
    oneOverX ∈ concreteData.fractionFiltration 0 :=
  concreteData.fractionFiltration_mono (by norm_num) oneOverX_mem_minus_one

def oneSubOverX : concreteData.degreeZeroSubring :=
  ⟨1 - oneOverX,
    (concreteData.fractionFiltration 0).sub_mem
      concreteData.degreeZeroSubring.one_mem oneOverX_mem_zero⟩

private theorem xSubOne_mem_zero :
    concreteData.inverse.rightFraction X xSubOneDenominator ∈
      concreteData.fractionFiltration 0 := by
  have ha : (1 : ℚ[X]) ∈ concreteInverse.filtration.carrier 0 :=
    polyDegreeZero
  rcases concreteInverse.inverse_mem_degreeZeroFractionSet x_mem x_sigma ha
      (by omega) with ⟨ss, tt, hss, htt, hmem⟩
  have hssx : ss = xDenominator := by
    apply Subtype.ext
    simpa [xDenominator] using hss
  have httx : tt = xSubOneDenominator := by
    apply Subtype.ext
    simpa [xDenominator, xSubOneDenominator] using htt
  change concreteInverse.fractionDegreeAtMost 0
    (concreteInverse.rightFraction X xSubOneDenominator)
  change concreteInverse.fractionDegreeAtMost 0
    (concreteInverse.rightFraction (ss : ℚ[X]) tt) at hmem
  simpa [hssx, httx, xDenominator] using hmem

theorem one_over_x_subtype_inverse :
    ∃ v : concreteData.degreeZeroSubring,
      (v : concreteData.inverse.localization.Localization) =
          concreteInverse.rightFraction X xSubOneDenominator ∧
      ((oneSubOverX * v : concreteData.degreeZeroSubring) :
          concreteData.inverse.localization.Localization) = 1 ∧
      ((v * oneSubOverX : concreteData.degreeZeroSubring) :
          concreteData.inverse.localization.Localization) = 1 := by
  have ha : (1 : ℚ[X]) ∈ concreteInverse.filtration.carrier 0 :=
    polyDegreeZero
  rcases concreteInverse.one_sub_rightFraction_mul_inverse x_mem x_sigma ha
      (by omega) with ⟨ss, tt, hss, htt, hleft, hright⟩
  have hssx : ss = xDenominator := by
    apply Subtype.ext
    simpa [xDenominator] using hss
  have httx : tt = xSubOneDenominator := by
    apply Subtype.ext
    simpa [xDenominator, xSubOneDenominator] using htt
  let v : concreteData.degreeZeroSubring :=
    ⟨concreteInverse.rightFraction X xSubOneDenominator, xSubOne_mem_zero⟩
  refine ⟨v, rfl, ?_, ?_⟩
  · change (1 - oneOverX) *
        concreteInverse.rightFraction X xSubOneDenominator = 1
    have hleft' := hleft
    rw [hssx, httx] at hleft'
    simpa [oneOverX, xDenominator] using hleft'
  · change concreteInverse.rightFraction X xSubOneDenominator *
        (1 - oneOverX) = 1
    have hright' := hright
    rw [hssx, httx] at hright'
    simpa [oneOverX, xDenominator] using hright'

def xAddOneDenominator : concreteInverse.localization.denominators :=
  ⟨X + 1, by
    rw [concreteInverse.denominators_eq_submonoid]
    have hpred : (-1 : ℚ[X]) ∈
        AdditiveFilteredRingData.predecessor concreteInverse.filtration 1 := by
      rw [AdditiveFilteredRingData.predecessor]
      change (-1 : ℚ[X]).natDegree ≤ 0
      simp
    simpa [sub_neg_eq_add, xDenominator] using
      sub_mem_of_selected_symbol concreteInverse.filtration concreteInverse.symbols
        x_mem x_sigma hpred⟩

private theorem rightFraction_neg
    (a : ℚ[X]) (s : concreteInverse.localization.denominators) :
    concreteInverse.rightFraction (-a) s =
      -concreteInverse.rightFraction a s := by
  apply (concreteInverse.localization.denominator_unit s).mul_right_cancel
  calc
    concreteInverse.rightFraction (-a) s *
          concreteInverse.localization.numerator (s : ℚ[X]) =
        concreteInverse.localization.numerator (-a) :=
      rightFraction_mul_denominator (-a) s
    _ = -concreteInverse.localization.numerator a := by rw [map_neg]
    _ = (-concreteInverse.rightFraction a s) *
          concreteInverse.localization.numerator (s : ℚ[X]) := by
      calc
        -concreteInverse.localization.numerator a =
            -(concreteInverse.rightFraction a s *
              concreteInverse.localization.numerator (s : ℚ[X])) := by
                rw [rightFraction_mul_denominator]
          _ = (-concreteInverse.rightFraction a s) *
              concreteInverse.localization.numerator (s : ℚ[X]) := by
                exact (neg_mul
                  (concreteInverse.rightFraction a s)
                  (concreteInverse.localization.numerator (s : ℚ[X]))).symm

private theorem xAddOne_mem_zero :
    concreteData.inverse.rightFraction X xAddOneDenominator ∈
      concreteData.fractionFiltration 0 := by
  have ha : (-1 : ℚ[X]) ∈ concreteInverse.filtration.carrier 0 := by
    change (-1 : ℚ[X]).natDegree ≤ 0
    simp
  rcases concreteInverse.inverse_mem_degreeZeroFractionSet x_mem x_sigma ha
      (by omega) with ⟨ss, tt, hss, htt, hmem⟩
  have hssx : ss = xDenominator := by
    apply Subtype.ext
    simpa [xDenominator] using hss
  have httx : tt = xAddOneDenominator := by
    apply Subtype.ext
    simpa [xDenominator, xAddOneDenominator] using htt
  change concreteInverse.fractionDegreeAtMost 0
    (concreteInverse.rightFraction X xAddOneDenominator)
  change concreteInverse.fractionDegreeAtMost 0
    (concreteInverse.rightFraction (ss : ℚ[X]) tt) at hmem
  simpa [hssx, httx, xDenominator] using hmem

theorem one_plus_x_jacobson_orientation :
    ∃ z : concreteData.degreeZeroSubring,
      (z : concreteData.inverse.localization.Localization) =
          concreteInverse.rightFraction X xAddOneDenominator ∧
      ((z * (1 + ⟨oneOverX, oneOverX_mem_zero⟩ :
          concreteData.degreeZeroSubring) : concreteData.degreeZeroSubring) :
          concreteData.inverse.localization.Localization) = 1 ∧
      z * (1 : concreteData.degreeZeroSubring) *
          (⟨oneOverX, oneOverX_mem_zero⟩ : concreteData.degreeZeroSubring) + z - 1 = 0 := by
  have ha : (-1 : ℚ[X]) ∈ concreteInverse.filtration.carrier 0 := by
    change (-1 : ℚ[X]).natDegree ≤ 0
    simp
  rcases concreteInverse.one_sub_rightFraction_mul_inverse x_mem x_sigma ha
      (by omega) with ⟨ss, tt, hss, htt, _hleft, hright⟩
  have hssx : ss = xDenominator := by
    apply Subtype.ext
    simpa [xDenominator] using hss
  have httx : tt = xAddOneDenominator := by
    apply Subtype.ext
    simpa [xDenominator, xAddOneDenominator] using htt
  have hneg : concreteInverse.rightFraction (-1) xDenominator =
      -concreteInverse.rightFraction 1 xDenominator :=
    rightFraction_neg 1 xDenominator
  let z : concreteData.degreeZeroSubring :=
    ⟨concreteInverse.rightFraction X xAddOneDenominator, xAddOne_mem_zero⟩
  refine ⟨z, rfl, ?_, ?_⟩
  · change concreteInverse.rightFraction X xAddOneDenominator *
        (1 + oneOverX) = 1
    have hright' := hright
    rw [hssx, httx, hneg] at hright'
    simpa [oneOverX, xDenominator, sub_neg_eq_add] using hright'
  · apply Subtype.ext
    change (z : concreteData.inverse.localization.Localization) *
        (1 : concreteData.inverse.localization.Localization) * oneOverX +
        (z : concreteData.inverse.localization.Localization) - 1 = 0
    have hz : concreteInverse.rightFraction X xAddOneDenominator *
        (1 + oneOverX) = 1 := by
      have hright' := hright
      rw [hssx, httx, hneg] at hright'
      simpa [oneOverX, xDenominator, sub_neg_eq_add] using hright'
    dsimp [z]
    calc
      concreteInverse.rightFraction X xAddOneDenominator * 1 * oneOverX +
            concreteInverse.rightFraction X xAddOneDenominator - 1 =
          concreteInverse.rightFraction X xAddOneDenominator *
            (1 + oneOverX) - 1 := by noncomm_ring
      _ = 0 := by rw [hz, sub_self]

example : oneOverX ≠ 0 := oneOverX_ne_zero

example : concreteInverse.denominator_degree xDenominator = 1 :=
  denominator_degree_x

abbrev LaurentT := concreteData.inverse.localization.Localization

private abbrev xNumerator : LaurentT :=
  concreteData.inverse.localization.numerator (xDenominator : ℚ[X])

private theorem oneOverX_mul_xNumerator :
    oneOverX * xNumerator = 1 := by
  simpa [oneOverX, xNumerator] using
    (rightFraction_mul_denominator 1 xDenominator)

private theorem xNumerator_mul_oneOverX :
    xNumerator * oneOverX = 1 := by
  apply (concreteInverse.localization.denominator_unit xDenominator).mul_right_cancel
  calc
    (xNumerator * oneOverX) * xNumerator =
        xNumerator * (oneOverX * xNumerator) := by
          simp only [mul_assoc]
    _ = xNumerator * 1 := by rw [oneOverX_mul_xNumerator]
    _ = (1 : LaurentT) * xNumerator := by simp

private theorem xNumerator_mem_one :
    xNumerator ∈ concreteData.fractionFiltration (1 : ℤ) := by
  change concreteInverse.fractionDegreeAtMost (1 : ℤ) xNumerator
  refine Or.inr ⟨(xDenominator : ℚ[X]),
    (1 : concreteInverse.localization.denominators), 1, x_mem, ?_, ?_⟩
  · simp [xNumerator]
  · have hd : (0 : ℤ) ≤
        Int.ofNat (concreteInverse.denominator_degree
          (1 : concreteInverse.localization.denominators)) :=
      Int.natCast_nonneg _
    norm_num only [Nat.cast_one] at *
    omega

private theorem single_x_bounded :
    SymbolFractionRees.Bounded concreteData
      (AddMonoidAlgebra.single (1 : ℤ) xNumerator) := by
  intro z
  rw [AddMonoidAlgebra.coeff_single_apply]
  by_cases hz : (1 : ℤ) = z
  · subst z
    exact xNumerator_mem_one
  · rw [if_neg hz]
    exact (concreteData.fractionFiltration z).zero_mem

private theorem single_inv_bounded :
    SymbolFractionRees.Bounded concreteData
      (AddMonoidAlgebra.single (-1 : ℤ) oneOverX) := by
  intro z
  rw [AddMonoidAlgebra.coeff_single_apply]
  by_cases hz : (-1 : ℤ) = z
  · subst z
    exact oneOverX_mem_minus_one
  · rw [if_neg hz]
    exact (concreteData.fractionFiltration z).zero_mem

def xTerm : SymbolFractionRees.ReesRing concreteData :=
  ⟨AddMonoidAlgebra.single (1 : ℤ) xNumerator, single_x_bounded⟩

def xInverseTerm : SymbolFractionRees.ReesRing concreteData :=
  ⟨AddMonoidAlgebra.single (-1 : ℤ) oneOverX, single_inv_bounded⟩

/-- Independent ambient calculation: the selected degree-one symbol and its
    actual right-localization inverse multiply in both orders. -/
theorem xTerm_mul_inverse :
    (xTerm * xInverseTerm : SymbolFractionRees.ReesRing concreteData) = 1 := by
  apply Subtype.ext
  change AddMonoidAlgebra.single (1 : ℤ) xNumerator *
      AddMonoidAlgebra.single (-1 : ℤ) oneOverX = 1
  rw [AddMonoidAlgebra.single_mul_single]
  rw [xNumerator_mul_oneOverX]
  rfl

theorem inverse_mul_xTerm :
    (xInverseTerm * xTerm : SymbolFractionRees.ReesRing concreteData) = 1 := by
  apply Subtype.ext
  change AddMonoidAlgebra.single (-1 : ℤ) oneOverX *
      AddMonoidAlgebra.single (1 : ℤ) xNumerator = 1
  rw [AddMonoidAlgebra.single_mul_single]
  rw [oneOverX_mul_xNumerator]
  rfl

theorem xTerm_ne_zero : xTerm ≠ (0 : SymbolFractionRees.ReesRing concreteData) := by
  intro h
  have hv := congrArg (fun p : AddMonoidAlgebra LaurentT ℤ => p.coeff 1)
    (congrArg Subtype.val h)
  have hv : xNumerator = 0 := by
    simpa only [xTerm, AddMonoidAlgebra.coeff_single_apply, if_pos rfl,
      ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      ite_true] using hv
  have hnum : concreteInverse.localization.numerator
      (xDenominator : ℚ[X]) = 0 := hv
  have hpoly : (xDenominator : ℚ[X]) = 0 :=
    concreteInverse.localization.numerator_injective (by simpa using hnum)
  simpa [xDenominator] using hpoly

/-- Two distinct negative degrees clear by the same rightmost degree-two
homogeneous denominator; the resulting terms have degrees one and zero. -/
theorem two_term_homogeneous_clearance :
    (AddMonoidAlgebra.single (-1 : ℤ) oneOverX +
      AddMonoidAlgebra.single (-2 : ℤ) (oneOverX ^ 2)) *
        AddMonoidAlgebra.single (2 : ℤ) (xNumerator ^ 2) =
      AddMonoidAlgebra.single (1 : ℤ) xNumerator +
        AddMonoidAlgebra.single (0 : ℤ) (1 : LaurentT) := by
  have hfirst : oneOverX * xNumerator ^ 2 = xNumerator := by
    rw [pow_two, ← mul_assoc, oneOverX_mul_xNumerator, one_mul]
  have hsecond : oneOverX ^ 2 * xNumerator ^ 2 = 1 := by
    calc
      oneOverX ^ 2 * xNumerator ^ 2 =
          oneOverX * (oneOverX * xNumerator) * xNumerator := by noncomm_ring
      _ = 1 := by rw [oneOverX_mul_xNumerator, mul_one, oneOverX_mul_xNumerator]
  rw [add_mul, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single, hfirst, hsecond]
  rfl

end
end SymplecticStaffordTest.SymbolFractionReesOracle

#print axioms
  SymplecticStaffordTest.SymbolFractionReesOracle.one_over_x_subtype_inverse
#print axioms
  SymplecticStaffordTest.SymbolFractionReesOracle.one_plus_x_jacobson_orientation


#print axioms SymplecticStaffordTest.SymbolFractionReesOracle.xTerm_mul_inverse
#print axioms SymplecticStaffordTest.SymbolFractionReesOracle.inverse_mul_xTerm
#print axioms SymplecticStaffordTest.SymbolFractionReesOracle.xTerm_ne_zero

#print axioms SymplecticStaffordTest.SymbolFractionReesOracle.two_term_homogeneous_clearance
