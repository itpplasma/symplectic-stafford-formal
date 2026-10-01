import Mathlib.Tactic
import SymplecticStafford.Filtered.ReesNoetherianTransfer

/-!
# A bounded M01 homogeneous-symbol producer

For an actual exhaustive additive filtration, a nonzero original-ring element
has a least filtration degree.  The corresponding quotient class is nonzero,
and the existing coefficient-symbol API identifies its concrete homogeneous
Rees lift, including multiplication by any other homogeneous lift.

This is a bounded structural producer.  It does not assert that the generic
associated graded ring is commutative affine, that homogeneous ideal symbols
lift, or that any localization is Noetherian.  Those remain the first
unsupported M01--M05 bridges.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

open SymplecticStafford
open AdditiveFilteredRingData
open ActualAssociatedGraded
open ReesNoetherianTransfer

variable {R : Type u} [Ring R]

theorem exists_minimal_layer_homogeneous_symbol
    (F : AdditiveFilteredRingData R) {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ F.carrier n,
      (∀ k < n, a ∉ F.carrier k) ∧
      let q := AdditiveFilteredRingData.associatedClass F n a hna
      let x := ActualAssociatedGraded.representative F n q
      let p := ReesNoetherianTransfer.shiftedHomogeneousLift F n 0 q
      q ≠ 0 ∧
      p ≠ 0 ∧
      ((p : ReesPolynomial R).coeff n = (x : R)) ∧
      AdditiveFilteredRingData.associatedClass F n (x : R) x.property = q ∧
      ReesNoetherianTransfer.CoefficientSymbol F n p
        (Finsupp.single 0 q) ∧
      ∀ m y,
        ReesNoetherianTransfer.CoefficientSymbol F (n + m)
          (p * ReesNoetherianTransfer.shiftedHomogeneousLift F m 0 y)
          (Finsupp.single 0
            (AdditiveFilteredRingData.associatedLayerMul F n m q y)) := by
  classical
  let hex : ∃ k : ℕ, a ∈ F.carrier k := F.exhaustive a
  let n : ℕ := Nat.find hex
  have hna : a ∈ F.carrier n := Nat.find_spec hex
  have hmin : ∀ k < n, a ∉ F.carrier k := by
    intro k hkn hk
    exact (not_lt_of_ge (Nat.find_min' hex hk)) hkn
  let q : AdditiveFilteredRingData.associatedLayer F n :=
    AdditiveFilteredRingData.associatedClass F n a hna
  have hq : q ≠ 0 := by
    intro hzero
    have hpred : a ∈ AdditiveFilteredRingData.predecessor F n :=
      (AdditiveFilteredRingData.associatedClass_eq_zero_iff F n a hna).mp
        hzero
    by_cases hn0 : n = 0
    · have hpred0 : a ∈ (⊥ : AddSubgroup R) := by
        rw [hn0] at hpred
        simpa [AdditiveFilteredRingData.predecessor, hn0] using hpred
      exact ha (by simpa using hpred0)
    · have hlt : n - 1 < n :=
        Nat.sub_lt (Nat.zero_lt_of_ne_zero hn0) Nat.zero_lt_one
      exact hmin (n - 1) hlt (by
        simpa [AdditiveFilteredRingData.predecessor, hn0] using hpred)
  let x : F.carrier n := ActualAssociatedGraded.representative F n q
  let p : ReesRing F.toNegFiltrationData :=
    ReesNoetherianTransfer.shiftedHomogeneousLift F n 0 q
  have hxclass :
      AdditiveFilteredRingData.associatedClass F n (x : R) x.property = q := by
    exact ActualAssociatedGraded.associatedClass_representative F n q
  have hx : (x : R) ≠ 0 := by
    intro hxzero
    apply hq
    have hx0 : x = 0 := Subtype.ext hxzero
    rw [← hxclass]
    simp only [hx0]
    exact ReesNoetherianTransfer.associatedClass_zero F n
  have hpcoeff :
      ((p : ReesPolynomial R).coeff n) = (x : R) := by
    dsimp [p, x]
    simpa using ReesNoetherianTransfer.shiftedHomogeneousLift_coeff F n 0 q
  have hp : p ≠ 0 := by
    intro hpzero
    apply hx
    calc
      (x : R) = (p : ReesPolynomial R).coeff n := hpcoeff.symm
      _ = 0 := by simp [hpzero]
  have hsymbol :
      ReesNoetherianTransfer.CoefficientSymbol F n p (Finsupp.single 0 q) := by
    dsimp [p]
    simpa using
      ReesNoetherianTransfer.coefficientSymbol_shiftedHomogeneousLift F n 0 q
  have hmul :
      ∀ m y,
        ReesNoetherianTransfer.CoefficientSymbol F (n + m)
          (p * ReesNoetherianTransfer.shiftedHomogeneousLift F m 0 y)
          (Finsupp.single 0
            (AdditiveFilteredRingData.associatedLayerMul F n m q y)) := by
    intro m y
    dsimp [p]
    simpa using
      ReesNoetherianTransfer.coefficientSymbol_mul_shiftedHomogeneousLift
        F n m 0 0 q y
  refine ⟨n, hna, hmin, ?_⟩
  change q ≠ 0 ∧ p ≠ 0 ∧
    ((p : ReesPolynomial R).coeff n = (x : R)) ∧
    AdditiveFilteredRingData.associatedClass F n (x : R) x.property = q ∧
    ReesNoetherianTransfer.CoefficientSymbol F n p (Finsupp.single 0 q) ∧
    (∀ m y,
      ReesNoetherianTransfer.CoefficientSymbol F (n + m)
        (p * ReesNoetherianTransfer.shiftedHomogeneousLift F m 0 y)
        (Finsupp.single 0
          (AdditiveFilteredRingData.associatedLayerMul F n m q y)))
  exact ⟨hq, hp, hpcoeff, hxclass, hsymbol, hmul⟩

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.exists_minimal_layer_homogeneous_symbol
