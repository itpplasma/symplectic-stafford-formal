import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations
import SymplecticStafford.Filtered.AssociatedGradedSpecBridge

/-! Independent polynomial oracle for the actual associated-layer/spec bridge. -/

namespace SymplecticStafford.AssociatedGradedSpecBridgeOracle

open SymplecticStafford.Filtered

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
    exact ⟨p.natDegree, by
      change p.natDegree ≤ p.natDegree
      exact le_rfl⟩

def coefficientOne :
    AdditiveFilteredRingData.associatedLayer polynomialFiltration 1 →+ ℚ where
  toFun := Quotient.lift
    (fun p : polynomialFiltration.carrier 1 => p.1.coeff 1)
    (by
      intro p q hpq
      have hq := (Submodule.quotientRel_def
        (AdditiveFilteredRingData.layerSubmodule polynomialFiltration 1)).mp hpq
      have hd : p.1 - q.1 ∈
          AdditiveFilteredRingData.predecessor polynomialFiltration 1 := by
        exact Submodule.mem_comap.mp hq
      have hdeg : (p.1 - q.1).natDegree < 1 := by
        change (p.1 - q.1).natDegree ≤ 0 at hd
        omega
      have hcoeff := Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
      rw [Polynomial.coeff_sub] at hcoeff
      exact sub_eq_zero.mp hcoeff)
  map_zero' := by
    change (Quotient.lift _ _) (Submodule.Quotient.mk
      (0 : polynomialFiltration.carrier 1)) = 0
    rfl
  map_add' := by
    intro x y
    obtain ⟨p, rfl⟩ := Quotient.exists_rep x
    obtain ⟨q, rfl⟩ := Quotient.exists_rep y
    change (p.1 + q.1).coeff 1 = p.1.coeff 1 + q.1.coeff 1
    simp

theorem coefficientOne_surjective : Function.Surjective coefficientOne := by
  intro q
  refine ⟨AdditiveFilteredRingData.associatedClass polynomialFiltration 1
    (Polynomial.C q + Polynomial.C q * Polynomial.X) (by
      change (Polynomial.C q + Polynomial.C q * Polynomial.X).natDegree ≤ 1
      have hmul : (Polynomial.C q * Polynomial.X).natDegree ≤ 1 := by
        calc
          _ ≤ (Polynomial.C q).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 1 := by simp
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (by simp) hmul)), ?_⟩
  change (Polynomial.C q + Polynomial.C q * Polynomial.X).coeff 1 = q
  simp

theorem coefficientOne_eq_zero_iff (x :
    AdditiveFilteredRingData.associatedLayer polynomialFiltration 1) :
    coefficientOne x = 0 ↔ x = 0 := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep x
  constructor
  · intro hp
    apply (Submodule.Quotient.eq
      (AdditiveFilteredRingData.layerSubmodule polynomialFiltration 1)).mpr
    have hdeg : p.1.natDegree ≤ 1 := p.property
    have hcoeff : p.1.coeff 1 = 0 := hp
    have hzero : p.1.natDegree ≤ 0 := by
      apply (Polynomial.natDegree_le_iff_coeff_eq_zero).mpr
      intro n hn
      by_cases hn1 : n = 1
      · simpa [hn1] using hcoeff
      · have hlt : 1 < n := by omega
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt)
    have htop : p.1 = Polynomial.C (p.1.coeff 0) := by
      apply Polynomial.eq_C_of_natDegree_le_zero
      exact hzero
    change p.1 - 0 ∈ AdditiveFilteredRingData.predecessor polynomialFiltration 1
    rw [htop]
    have hc : Polynomial.C (p.1.coeff 0) ∈
        polynomialFiltration.carrier 0 := by
      change (Polynomial.C (p.1.coeff 0)).natDegree ≤ 0
      simp
    simpa [AdditiveFilteredRingData.predecessor] using hc
  · intro hx
    simpa using congrArg coefficientOne hx

def bridge :
    AssociatedGradedSpecBridge polynomialFiltration ℚ ℚ where
  layer := 1
  layerMap := coefficientOne
  surjective := coefficientOne_surjective
  layerMap_eq_zero_iff := coefficientOne_eq_zero_iff

example :
    Module.support ℚ ℚ = ∅ ↔
      ∀ x : polynomialFiltration.carrier bridge.layer,
        (x : Polynomial ℚ) ∈
          AdditiveFilteredRingData.predecessor polynomialFiltration bridge.layer :=
  bridge.specSupport_empty_iff_layer_killed

example :
    (Module.support ℚ ℚ).Nonempty ↔
      ∃ x : polynomialFiltration.carrier bridge.layer,
        (x : Polynomial ℚ) ∉
          AdditiveFilteredRingData.predecessor polynomialFiltration bridge.layer :=
  bridge.specSupport_nonempty_iff_exists_not_mem_predecessor

example : (Module.support ℚ ℚ).Nonempty := by
  apply (bridge.specSupport_nonempty_iff_exists_not_mem_predecessor).mpr
  refine ⟨⟨Polynomial.X, by
    change Polynomial.X.natDegree ≤ 1
    simp⟩, ?_⟩
  intro hx
  change (Polynomial.X : Polynomial ℚ) ∈
    AdditiveFilteredRingData.predecessor polynomialFiltration 1 at hx
  have hx0 : (Polynomial.X : Polynomial ℚ) ∈
      polynomialFiltration.carrier 0 := by
    simpa [AdditiveFilteredRingData.predecessor] using hx
  have hx' : (Polynomial.X : Polynomial ℚ).natDegree ≤ 0 := by
    change (Polynomial.X : Polynomial ℚ).natDegree ≤ 0 at hx0
    exact hx0
  norm_num at hx'

example :
    Module.support ℚ ℚ =
      PrimeSpectrum.zeroLocus (Module.annihilator ℚ ℚ : Set ℚ) :=
  specSupport_eq_zeroLocus_annihilator

end

end SymplecticStafford.AssociatedGradedSpecBridgeOracle

#print axioms SymplecticStafford.AssociatedGradedSpecBridgeOracle.bridge
#print axioms SymplecticStafford.Filtered.AssociatedGradedSpecBridge.specSupport_empty_iff_layer_killed
#print axioms SymplecticStafford.Filtered.specSupport_eq_zeroLocus_annihilator
