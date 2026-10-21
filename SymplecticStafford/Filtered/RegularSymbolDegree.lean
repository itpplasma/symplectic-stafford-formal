module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.M01StructuralClass

@[expose] public section

/-!
# Degree control from a regular associated symbol

Let `s` lie in filtration degree `i`.  If its actual associated symbol acts
injectively on every associated layer, then multiplication by `s` cannot
drop the least filtration degree of a nonzero element.  Consequently a
product in degree `n` has its right factor in degree `n - i` when `i ≤ n`, and
the right factor is zero when `n < i`.

The regularity input is stated on the actual quotient layers.  The proof
chooses the least filtration degree of a nonzero right factor using
exhaustivity, lifts the product to the sum degree, and uses the quotient
zero/predecessor criterion.  No Ore, localization, Rees-Noetherianity, or
paper-specific symbol construction is included here.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford

namespace RegularSymbolDegree

variable {R : Type u} [Ring R]

/- A selected symbol together with exactly the regularity needed below.  The
   first field records that the representative has the advertised exact
   degree; the second is the left-regularity statement on every actual
   associated quotient layer. -/
structure Data (F : AdditiveFilteredRingData R) (i : ℕ) where
  representative : R
  representative_mem : representative ∈ F.carrier i
  symbol_ne_zero :
    AdditiveFilteredRingData.associatedClass F i representative
      representative_mem ≠ 0
  left_regular :
    ∀ j : ℕ, ∀ y : AdditiveFilteredRingData.associatedLayer F j,
      AdditiveFilteredRingData.associatedLayerMul F i j
          (AdditiveFilteredRingData.associatedClass F i representative
            representative_mem) y = 0 →
        y = 0

namespace Data

variable {F : AdditiveFilteredRingData R} {i : ℕ}

/- The least degree of a fixed nonzero element, with its witness retained so
   the dependent associated class can be used without a choice callback. -/
noncomputable def leastDegree (F : AdditiveFilteredRingData R)
    {x : R} (hx : x ≠ 0) : ℕ := by
  classical
  exact Nat.find (show ∃ n : ℕ, x ∈ F.carrier n from F.exhaustive x)

theorem leastDegree_mem (F : AdditiveFilteredRingData R)
    {x : R} (hx : x ≠ 0) : x ∈ F.carrier (leastDegree F hx) := by
  classical
  let hex : ∃ n : ℕ, x ∈ F.carrier n := F.exhaustive x
  change x ∈ F.carrier (Nat.find hex)
  exact Nat.find_spec hex

theorem leastDegree_class_ne_zero (F : AdditiveFilteredRingData R)
    {x : R} (hx : x ≠ 0) :
    AdditiveFilteredRingData.associatedClass F (leastDegree F hx) x
      (leastDegree_mem F hx) ≠ 0 := by
  classical
  intro hzero
  have hpred : x ∈ AdditiveFilteredRingData.predecessor F (leastDegree F hx) :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff F
      (leastDegree F hx) x (leastDegree_mem F hx)).mp hzero
  by_cases hm0 : leastDegree F hx = 0
  · have hbot : x ∈ (⊥ : AddSubgroup R) := by
      rw [hm0] at hpred
      simpa [AdditiveFilteredRingData.predecessor] using hpred
    exact hx (by simpa using hbot)
  · have hprev : x ∈ F.carrier (leastDegree F hx - 1) := by
      simpa [AdditiveFilteredRingData.predecessor, hm0] using hpred
    have hlt : leastDegree F hx - 1 < leastDegree F hx :=
      Nat.sub_lt (Nat.zero_lt_of_ne_zero hm0) zero_lt_one
    have hle : leastDegree F hx ≤ leastDegree F hx - 1 := by
      unfold leastDegree at hlt ⊢
      exact Nat.find_min' (show ∃ n : ℕ, x ∈ F.carrier n from F.exhaustive x)
        hprev
    exact (Nat.not_lt_of_ge hle) hlt

/- A nonzero least-layer class cannot be killed by a regular selected symbol
   if the product has been placed strictly below the sum degree. -/
private theorem no_product_below_sum
    (S : Data F i) {n : ℕ} {x : R}
    (hprod : S.representative * x ∈ F.carrier n)
    {j : ℕ} (hxj : x ∈ F.carrier j)
    (hxclass : AdditiveFilteredRingData.associatedClass F j x hxj ≠ 0)
    (hbelow : n < i + j) : False := by
  have hsum0 : i + j ≠ 0 := by omega
  have hprod_sum : S.representative * x ∈ F.carrier (i + j) :=
    F.mul_mem S.representative_mem hxj
  have hprod_prev : S.representative * x ∈
      AdditiveFilteredRingData.predecessor F (i + j) := by
    rw [AdditiveFilteredRingData.predecessor, if_neg hsum0]
    exact F.monotone (by omega) hprod
  have hprod_class :
      AdditiveFilteredRingData.associatedClass F (i + j)
          (S.representative * x) hprod_sum = 0 :=
    (AdditiveFilteredRingData.associatedClass_eq_zero_iff F
      (i + j) (S.representative * x) hprod_sum).mpr hprod_prev
  have hmul_zero :
      AdditiveFilteredRingData.associatedLayerMul F i j
          (AdditiveFilteredRingData.associatedClass F i S.representative
            S.representative_mem)
          (AdditiveFilteredRingData.associatedClass F j x hxj) = 0 := by
    change AdditiveFilteredRingData.associatedLayerMul F i j
        (Submodule.Quotient.mk ⟨S.representative, S.representative_mem⟩)
        (Submodule.Quotient.mk ⟨x, hxj⟩) = 0
    rw [AdditiveFilteredRingData.associatedLayerMul_mk_mk]
    exact hprod_class
  have hxzero := S.left_regular j
    (AdditiveFilteredRingData.associatedClass F j x hxj) hmul_zero
  exact hxclass hxzero

theorem representative_ne_zero (S : Data F i) :
    S.representative ≠ 0 := by
  intro hs
  have hmem0 : (0 : R) ∈ F.carrier i := by
    simpa [hs] using S.representative_mem
  have hzero0 :
      AdditiveFilteredRingData.associatedClass F i 0 hmem0 = 0 := by
    apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff F i 0
      hmem0).mpr
    exact (AdditiveFilteredRingData.predecessor F i).zero_mem
  apply S.symbol_ne_zero
  simpa [hs] using hzero0

theorem mem_of_mul_mem
    (S : Data F i) {n : ℕ} {x : R}
    (hprod : S.representative * x ∈ F.carrier n)
    (hin : i ≤ n) :
    x ∈ F.carrier (n - i) := by
  by_cases hx0 : x = 0
  · subst x
    exact F.zero_mem _
  · have hjmem := leastDegree_mem F hx0
    have hjclass := leastDegree_class_ne_zero F hx0
    by_contra htarget
    have hjnot : ¬ leastDegree F hx0 ≤ n - i := by
      intro hj
      exact htarget (F.monotone hj hjmem)
    have hjlt : n - i < leastDegree F hx0 :=
      Nat.lt_of_not_ge hjnot
    exact no_product_below_sum S hprod hjmem hjclass (by omega)

theorem eq_zero_of_mul_mem_of_lt
    (S : Data F i) {n : ℕ} {x : R}
    (hprod : S.representative * x ∈ F.carrier n)
    (hlt : n < i) :
    x = 0 := by
  by_contra hx0
  have hjmem := leastDegree_mem F hx0
  have hjclass := leastDegree_class_ne_zero F hx0
  exact no_product_below_sum S hprod hjmem hjclass (by omega)

/- The two branches in one theorem are convenient for fraction-filtration
   consumers: every product bound gives either the shifted bound or a zero
   cofactor. -/
theorem degree_controlled_mul
    (S : Data F i) {n : ℕ} {x : R}
    (hprod : S.representative * x ∈ F.carrier n) :
    (i ≤ n → x ∈ F.carrier (n - i)) ∧
      (n < i → x = 0) := by
  constructor
  · intro hin
    exact mem_of_mul_mem S hprod hin
  · intro hlt
    exact eq_zero_of_mul_mem_of_lt S hprod hlt

end Data

end RegularSymbolDegree

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.RegularSymbolDegree.Data.leastDegree_class_ne_zero
#print axioms
  SymplecticStafford.Filtered.RegularSymbolDegree.Data.mem_of_mul_mem
#print axioms
  SymplecticStafford.Filtered.RegularSymbolDegree.Data.eq_zero_of_mul_mem_of_lt
#print axioms
  SymplecticStafford.Filtered.RegularSymbolDegree.Data.degree_controlled_mul
