module

public import SymplecticStafford.Filtered.SymbolFractionInverse
public import Mathlib.Algebra.Polynomial.Degree.Defs

@[expose] public section

/- Independent oracle for the lower-perturbation inverse.  The concrete
   calibration uses the degree filtration on `ℚ[X]`; selected symbols are the
   monomials `X^n`, so the resulting denominator submonoid contains exactly
   the monic lower perturbations required by the source theorem. -/

namespace SymplecticStaffordTest.SymbolFractionInverse

open Polynomial
open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.SymbolDenominatorSubmonoid
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
  simp

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
  denominators :=
    SymbolDenominatorSubmonoid.submonoid polyFiltration polySymbols
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

abbrev concreteData : SymbolFractionInverse.Data (ℚ[X]) where
  filtration := polyFiltration
  symbols := polySymbols
  localization := polyLocalization
  denominators_eq_submonoid := rfl

theorem polyDegreeOne : (X : ℚ[X]) ∈ polyFiltration.carrier 1 := by
  change X.natDegree ≤ 1
  simp

theorem polyDegreeZero : (1 : ℚ[X]) ∈ polyFiltration.carrier 0 := by
  change (1 : ℚ[X]).natDegree ≤ 0
  simp

def xDenominator : concreteData.localization.denominators :=
  ⟨X, by
    rw [concreteData.denominators_eq_submonoid]
    have hx : X ∈ concreteData.filtration.carrier 1 := by
      simpa [concreteData] using polyDegreeOne
    have hclass :
        AdditiveFilteredRingData.associatedClass concreteData.filtration 1 X hx ∈
          concreteData.symbols.Sigma 1 := by
      change AdditiveFilteredRingData.associatedClass concreteData.filtration 1 X hx ∈
        {AdditiveFilteredRingData.associatedClass concreteData.filtration 1
          (X ^ 1) (by
            change (X ^ 1).natDegree ≤ 1
            simp)}
      rw [Set.mem_singleton_iff]
      simp [pow_one]
    exact ⟨1, ⟨hx, hclass⟩⟩
  ⟩

def xSubOneDenominator : concreteData.localization.denominators :=
  ⟨X - 1, by
    rw [concreteData.denominators_eq_submonoid]
    have hx : (X : ℚ[X]) ∈ polyFiltration.carrier 1 := polyDegreeOne
    have hclass :
        AdditiveFilteredRingData.associatedClass polyFiltration 1 X hx ∈
          polySymbols.Sigma 1 := by
      simp [polySymbols]
    have hpred : (1 : ℚ[X]) ∈
        AdditiveFilteredRingData.predecessor polyFiltration 1 := by
      rw [AdditiveFilteredRingData.predecessor]
      change (1 : ℚ[X]).natDegree ≤ 0
      simp
    exact sub_mem_of_selected_symbol polyFiltration polySymbols hx hclass hpred
  ⟩

private theorem concrete_rightFraction_mul_denominator
    (a : ℚ[X]) (s : concreteData.localization.denominators) :
    concreteData.rightFraction a s *
        concreteData.localization.numerator (s : ℚ[X]) =
      concreteData.localization.numerator a := by
  letI : OreLocalization.OreSet
      (oppositeSubmonoid concreteData.localization.denominators) :=
    concreteData.localization.ore
  apply MulOpposite.unop_injective
  rw [show concreteData.rightFraction a s = MulOpposite.op
      (OreLocalization.oreDiv (MulOpposite.op a)
        (⟨MulOpposite.op (s : ℚ[X]), s.property⟩ :
          oppositeSubmonoid concreteData.localization.denominators)) by
        rfl]
  exact OreLocalization.mul_cancel
    (R := (ℚ[X])ᵐᵒᵖ)
    (S := oppositeSubmonoid concreteData.localization.denominators)
    (r := MulOpposite.op a)
    (s := (⟨MulOpposite.op (s : ℚ[X]), s.property⟩ :
      oppositeSubmonoid concreteData.localization.denominators))
    (t := (1 : oppositeSubmonoid concreteData.localization.denominators))

private theorem one_over_x_ne_zero :
    concreteData.rightFraction 1 xDenominator ≠ 0 := by
  intro hz
  have hmul := concrete_rightFraction_mul_denominator
    (1 : ℚ[X]) xDenominator
  have hnum : concreteData.localization.numerator (1 : ℚ[X]) = 0 := by
    rw [← hmul, hz, zero_mul]
  have hone : (1 : ℚ[X]) = 0 :=
    concreteData.localization.numerator_injective (by simpa using hnum)
  exact one_ne_zero hone

private theorem one_over_x_ne_one :
    concreteData.rightFraction 1 xDenominator ≠ 1 := by
  intro hone
  have hmul := concrete_rightFraction_mul_denominator
    (1 : ℚ[X]) xDenominator
  have hnum : concreteData.localization.numerator (1 : ℚ[X]) =
      concreteData.localization.numerator X := by
    calc
      concreteData.localization.numerator (1 : ℚ[X]) =
          concreteData.rightFraction 1 xDenominator *
            concreteData.localization.numerator (xDenominator : ℚ[X]) :=
        hmul.symm
      _ = concreteData.localization.numerator X := by
        rw [hone]
        simpa [xDenominator] using
          (concreteData.localization.numerator.map_mul (1 : ℚ[X]) X)
  have hpoly : (1 : ℚ[X]) = X :=
    concreteData.localization.numerator_injective hnum
  have heval := congrArg (fun p : ℚ[X] => p.eval 0) hpoly
  norm_num at heval

private theorem x_over_x_sub_one_ne_one :
    concreteData.rightFraction X xSubOneDenominator ≠ 1 := by
  intro hone
  have hmul := concrete_rightFraction_mul_denominator
    (X : ℚ[X]) xSubOneDenominator
  have hnum : concreteData.localization.numerator (X - 1) =
      concreteData.localization.numerator X := by
    calc
      concreteData.localization.numerator (X - 1) =
          concreteData.localization.numerator
            (xSubOneDenominator : ℚ[X]) := by rfl
      _ = concreteData.rightFraction X xSubOneDenominator *
            concreteData.localization.numerator
              (xSubOneDenominator : ℚ[X]) := by
        rw [hone, one_mul]
      _ = concreteData.localization.numerator X := hmul
  have hpoly : (X - 1 : ℚ[X]) = X :=
    concreteData.localization.numerator_injective hnum
  have heval := congrArg (fun p : ℚ[X] => p.eval 0) hpoly
  norm_num at heval

example :
    concreteData.rightFraction 1 xDenominator ≠ 0 ∧
      concreteData.rightFraction 1 xDenominator ≠ 1 :=
  ⟨one_over_x_ne_zero, one_over_x_ne_one⟩

example : concreteData.rightFraction X xSubOneDenominator ≠ 1 :=
  x_over_x_sub_one_ne_one

example :
    AdditiveFilteredRingData.associatedClass polyFiltration 1 X polyDegreeOne ∈
      polySymbols.Sigma 1 := by
  simp [polySymbols]

example :
    ∃ (ss : concreteData.localization.denominators)
      (tt : concreteData.localization.denominators),
      (ss : ℚ[X]) = X ∧ (tt : ℚ[X]) = X - 1 ∧
      SymbolFractionInverse.Data.rightFraction concreteData (ss : ℚ[X]) tt ∈
        concreteData.degreeZeroFractionSet := by
  let s : concreteData.localization.denominators := xDenominator
  let a : ℚ[X] := 1
  have ha : a ∈ concreteData.filtration.carrier 0 := by
    change a.natDegree ≤ 0
    simp [a]
  have hs : (s : ℚ[X]) ∈ concreteData.filtration.carrier 1 := by
    change X.natDegree ≤ 1
    simp
  have hSigma :
      AdditiveFilteredRingData.associatedClass concreteData.filtration 1
          (s : ℚ[X]) hs ∈ concreteData.symbols.Sigma 1 := by
    dsimp [s, xDenominator]
    change AdditiveFilteredRingData.associatedClass concreteData.filtration 1 X _ ∈
      {AdditiveFilteredRingData.associatedClass concreteData.filtration 1
        (X ^ 1) (by
          change (X ^ 1).natDegree ≤ 1
          simp)}
    rw [Set.mem_singleton_iff]
    simp [pow_one]
  rcases concreteData.inverse_mem_degreeZeroFractionSet hs hSigma ha (by omega) with
    ⟨ss, tt, hss, htt, hmem⟩
  exact ⟨ss, tt, hss, htt, hmem⟩

example :
    ∃ (ss tt : concreteData.localization.denominators),
      (ss : ℚ[X]) = X ∧ (tt : ℚ[X]) = X - 1 ∧
      (1 - concreteData.rightFraction 1 ss) *
          concreteData.rightFraction (ss : ℚ[X]) tt = 1 ∧
      concreteData.rightFraction (ss : ℚ[X]) tt *
          (1 - concreteData.rightFraction 1 ss) = 1 := by
  let s : concreteData.localization.denominators :=
    xDenominator
  have hs : (s : ℚ[X]) ∈ concreteData.filtration.carrier 1 := by
    change X.natDegree ≤ 1
    simp
  have hSigma :
      AdditiveFilteredRingData.associatedClass concreteData.filtration 1
          (s : ℚ[X]) hs ∈ concreteData.symbols.Sigma 1 := by
    dsimp [s, xDenominator]
    change AdditiveFilteredRingData.associatedClass concreteData.filtration 1 X _ ∈
      {AdditiveFilteredRingData.associatedClass concreteData.filtration 1
        (X ^ 1) (by
          change (X ^ 1).natDegree ≤ 1
          simp)}
    rw [Set.mem_singleton_iff]
    simp [pow_one]
  rcases concreteData.one_sub_rightFraction_mul_inverse hs hSigma
      (by
        change (1 : ℚ[X]).natDegree ≤ 0
        simp) (by omega) with
    ⟨ss, tt, hss, htt, hleft, hright⟩
  refine ⟨ss, tt, ?_, ?_, hleft, hright⟩
  · simpa [s, xDenominator] using hss
  · simpa [s, xDenominator] using htt

end
end SymplecticStaffordTest.SymbolFractionInverse

#print axioms SymplecticStaffordTest.SymbolFractionInverse.concreteData
#print axioms
  SymplecticStafford.Filtered.SymbolFractionInverse.Data.one_sub_rightFraction_mul_inverse
