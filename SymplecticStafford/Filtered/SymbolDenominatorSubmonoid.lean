module

public import Mathlib.Tactic
public import SymplecticStafford.Filtered.M01StructuralClass

@[expose] public section

/-!
# Denominators selected by actual associated symbols

For an additive filtered ring, a family of nonzero associated-layer symbols
which contains the identity and is closed under the actual layer product gives
an honest submonoid of the original ring.  The construction keeps the
filtered representative and its degree in the membership witness.

This is a denominator producer only.  It does not assert that the resulting
submonoid is Ore, that it is saturated, or that it is the complement of a
prime ideal.  The final lemma records the representative-level reason that a
strictly lower filtered perturbation has the same selected symbol.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford

variable {R : Type u} [Ring R]

namespace SymbolDenominatorSubmonoid

variable (F : AdditiveFilteredRingData R)

/- A selected symbol family, with precisely the graded multiplicative data
   needed for the original-ring submonoid. -/
structure Data where
  Sigma : ∀ n : ℕ, Set (AdditiveFilteredRingData.associatedLayer F n)
  one_mem :
    AdditiveFilteredRingData.associatedClass F 0 1 F.one_mem ∈ Sigma 0
  mul_mem : ∀ {i j : ℕ}
      {x : AdditiveFilteredRingData.associatedLayer F i}
      {y : AdditiveFilteredRingData.associatedLayer F j},
      x ∈ Sigma i → y ∈ Sigma j →
        AdditiveFilteredRingData.associatedLayerMul F i j x y ∈ Sigma (i + j)
  zero_not_mem : ∀ n : ℕ,
    (0 : AdditiveFilteredRingData.associatedLayer F n) ∉ Sigma n

variable (D : Data F)

/- Membership at one selected degree, before existentially quantifying the
   degree. -/
def Admissible (a : R) (n : ℕ) : Prop :=
  ∃ ha : a ∈ F.carrier n,
    AdditiveFilteredRingData.associatedClass F n a ha ∈ D.Sigma n

/- The original-ring denominator set selected by the symbol family. -/
def submonoid : Submonoid R where
  carrier := {a | ∃ n : ℕ, Admissible F D a n}
  one_mem' := by
    exact ⟨0, ⟨F.one_mem, D.one_mem⟩⟩
  mul_mem' := by
    rintro a b ⟨i, ⟨ha, hxa⟩⟩ ⟨j, ⟨hb, hxb⟩⟩
    refine ⟨i + j, F.mul_mem ha hb, ?_⟩
    rw [← AdditiveFilteredRingData.associatedLayerMul_mk_mk F i j
      ⟨a, ha⟩ ⟨b, hb⟩]
    exact D.mul_mem hxa hxb

theorem mem_submonoid_iff (a : R) :
    a ∈ submonoid F D ↔ ∃ n : ℕ, Admissible F D a n :=
  Iff.rfl

theorem associatedClass_ne_zero_of_mem_sigma
    {n : ℕ} {a : R} {ha : a ∈ F.carrier n}
    (hSigma : AdditiveFilteredRingData.associatedClass F n a ha ∈ D.Sigma n) :
    AdditiveFilteredRingData.associatedClass F n a ha ≠ 0 := by
  intro hzero
  exact D.zero_not_mem n (by simpa [hzero] using hSigma)

theorem zero_not_mem : (0 : R) ∉ submonoid F D := by
  intro hz
  rcases (mem_submonoid_iff F D 0).mp hz with ⟨n, hn, hSigma⟩
  have hzero :
      AdditiveFilteredRingData.associatedClass F n 0 hn = 0 := by
    apply (AdditiveFilteredRingData.associatedClass_eq_zero_iff F n 0 hn).mpr
    exact (AdditiveFilteredRingData.predecessor F n).zero_mem
  exact D.zero_not_mem n (by simpa [hzero] using hSigma)

/- The least degree at which a fixed original element has a selected symbol. -/
noncomputable def degree {a : R} (ha : a ∈ submonoid F D) : ℕ := by
  classical
  exact Nat.find (show ∃ n : ℕ, Admissible F D a n from
    (mem_submonoid_iff F D a).mp ha)

theorem degree_spec {a : R} (ha : a ∈ submonoid F D) :
    Admissible F D a (degree F D ha) := by
  classical
  unfold degree
  exact Nat.find_spec _

theorem degree_min {a : R} (ha : a ∈ submonoid F D)
    {n : ℕ} (hn : n < degree F D ha) :
    ¬ Admissible F D a n := by
  classical
  intro hna
  have hle : degree F D ha ≤ n :=
    Nat.find_min' ((mem_submonoid_iff F D a).mp ha) hna
  exact (Nat.not_lt_of_ge hle) hn

theorem degree_eq_of_minimal {a : R} {n : ℕ}
    (hna : Admissible F D a n)
    (hmin : ∀ m < n, ¬ Admissible F D a m) :
    degree F D (show a ∈ submonoid F D from ⟨n, hna⟩) = n := by
  classical
  let ha : a ∈ submonoid F D := ⟨n, hna⟩
  have hle : degree F D ha ≤ n :=
    Nat.find_min' ((mem_submonoid_iff F D a).mp ha) hna
  have hge : n ≤ degree F D ha := by
    by_contra hnot
    have hlt : degree F D ha < n := Nat.lt_of_not_ge hnot
    exact hmin _ hlt (degree_spec F D ha)
  exact le_antisymm hle hge

theorem degree_unique_of_minimal {a : R} {n m : ℕ}
    (hn : Admissible F D a n)
    (hminn : ∀ k < n, ¬ Admissible F D a k)
    (hm : Admissible F D a m)
    (hminm : ∀ k < m, ¬ Admissible F D a k) :
    n = m := by
  have hnm : n ≤ m := by
    by_contra hnot
    exact hminn _ (Nat.lt_of_not_ge hnot) hm
  have hmn : m ≤ n := by
    by_contra hnot
    exact hminm _ (Nat.lt_of_not_ge hnot) hn
  exact le_antisymm hnm hmn

/- The selected symbol at degree `n` survives subtraction by a lower-layer
   element.  The proof is made at the quotient level; no perturbation
   stability assumption is used. -/
theorem associatedClass_sub_eq_of_mem_predecessor
    {n : ℕ} {s u : R} (hs : s ∈ F.carrier n)
    (hu : u ∈ AdditiveFilteredRingData.predecessor F n) :
    let hsu : s - u ∈ F.carrier n :=
      (F.carrier n).sub_mem hs (F.predecessor_le n hu)
    AdditiveFilteredRingData.associatedClass F n (s - u) hsu =
      AdditiveFilteredRingData.associatedClass F n s hs := by
  dsimp
  apply (Submodule.Quotient.eq _).mpr
  change (s - u) - s ∈ AdditiveFilteredRingData.predecessor F n
  have hneg : -u ∈ AdditiveFilteredRingData.predecessor F n :=
    (AdditiveFilteredRingData.predecessor F n).neg_mem hu
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg

theorem sub_mem_of_selected_symbol
    {n : ℕ} {s u : R} (hs : s ∈ F.carrier n)
    (hSigma : AdditiveFilteredRingData.associatedClass F n s hs ∈ D.Sigma n)
    (hu : u ∈ AdditiveFilteredRingData.predecessor F n) :
    s - u ∈ submonoid F D := by
  let hsu : s - u ∈ F.carrier n :=
      (F.carrier n).sub_mem hs (F.predecessor_le n hu)
  refine (mem_submonoid_iff F D (s - u)).mpr ⟨n, hsu, ?_⟩
  have hclass := associatedClass_sub_eq_of_mem_predecessor F hs hu
  rw [hclass]
  exact hSigma

theorem degree_mul {a b : R} (ha : a ∈ submonoid F D)
    (hb : b ∈ submonoid F D) :
    degree F D (show a * b ∈ submonoid F D from
      (submonoid F D).mul_mem ha hb) =
      degree F D ha + degree F D hb := by
  classical
  let i := degree F D ha
  let j := degree F D hb
  rcases degree_spec F D ha with ⟨ha_i, hAi⟩
  rcases degree_spec F D hb with ⟨hb_j, hBj⟩
  let hp : a * b ∈ F.carrier (i + j) := F.mul_mem ha_i hb_j
  have hAB :
      AdditiveFilteredRingData.associatedClass F (i + j) (a * b) hp ∈
        D.Sigma (i + j) := by
    rw [← AdditiveFilteredRingData.associatedLayerMul_mk_mk F i j
      ⟨a, ha_i⟩ ⟨b, hb_j⟩]
    exact D.mul_mem hAi hBj
  have hAB_ne :
      AdditiveFilteredRingData.associatedClass F (i + j) (a * b) hp ≠ 0 := by
    exact associatedClass_ne_zero_of_mem_sigma F D hAB
  have hmin : ∀ m < i + j, ¬ Admissible F D (a * b) m := by
    intro m hlt hm
    rcases hm with ⟨hm, hSm⟩
    have hsum0 : i + j ≠ 0 := by omega
    have hprev : a * b ∈ AdditiveFilteredRingData.predecessor F (i + j) := by
      rw [AdditiveFilteredRingData.predecessor, if_neg hsum0]
      exact F.monotone (by omega) hm
    have hzero :=
      (AdditiveFilteredRingData.associatedClass_eq_zero_iff F (i + j)
        (a * b) hp).mpr hprev
    exact hAB_ne hzero
  exact degree_eq_of_minimal F D ⟨hp, hAB⟩ hmin

end SymbolDenominatorSubmonoid

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.SymbolDenominatorSubmonoid.submonoid
#print axioms
  SymplecticStafford.Filtered.SymbolDenominatorSubmonoid.degree_mul
#print axioms
  SymplecticStafford.Filtered.SymbolDenominatorSubmonoid.sub_mem_of_selected_symbol
