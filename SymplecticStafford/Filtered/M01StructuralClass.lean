import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic.NoncommRing
import SymplecticStafford.Filtered.ReesRing

/-!
# Structural M01 filtered-algebra interface

The historical class stores filtration and associated-graded hypotheses as
propositions.  `RingFiltrationData` is concrete, but its layers are right
ideals, which is too strong for the usual degree filtration on a polynomial
or Weyl algebra.  This file uses additive subgroups for the layers instead.

The associated layer is an actual additive quotient of consecutive layers.
Multiplication of classes is constructed from the original multiplication,
with representative independence proved from the filtration laws.  The
record below deliberately stops before Noetherianity, Ore localization,
support dimension, or source production.
-/

namespace SymplecticStafford.Filtered

universe u v

open SymplecticStafford

section Data

variable {R : Type u} [Ring R]

/- The additive-subgroup version of a multiplicative filtration. -/
structure AdditiveFilteredRingData (R : Type u) [Ring R] where
  carrier : ℕ → AddSubgroup R
  one_mem : (1 : R) ∈ carrier 0
  mul_mem : ∀ {i j : ℕ} {a b : R}, a ∈ carrier i → b ∈ carrier j →
    a * b ∈ carrier (i + j)
  monotone : Monotone carrier
  exhaustive : ∀ a : R, ∃ n : ℕ, a ∈ carrier n

namespace AdditiveFilteredRingData

variable (F : AdditiveFilteredRingData R)

theorem zero_mem (n : ℕ) : (0 : R) ∈ F.carrier n := by
  exact (F.carrier n).zero_mem

theorem add_mem {i j : ℕ} {a b : R}
    (ha : a ∈ F.carrier i) (hb : b ∈ F.carrier j) :
    a + b ∈ F.carrier (max i j) := by
  exact (F.carrier (max i j)).add_mem
    (F.monotone (Nat.le_max_left i j) ha)
    (F.monotone (Nat.le_max_right i j) hb)

theorem neg_mem {n : ℕ} {a : R} (ha : a ∈ F.carrier n) :
    -a ∈ F.carrier n := (F.carrier n).neg_mem ha

/- Bridge to the existing bounded Rees construction. -/
def toNegFiltrationData : NegFiltrationData R where
  toFiltrationData :=
    { carrier := fun n => F.carrier n
      zero_mem := F.zero_mem 0
      one_mem := F.one_mem
      add_mem := F.add_mem
      mul_mem := F.mul_mem
      monotone := F.monotone
      exhaustive := F.exhaustive }
  neg_mem := F.neg_mem

@[simp] theorem toNegFiltrationData_carrier (n : ℕ) :
    (F.toNegFiltrationData.carrier n : Set R) = F.carrier n := rfl

end AdditiveFilteredRingData

end Data

section Layers

variable {R : Type u} [Ring R]

namespace AdditiveFilteredRingData

variable (F : AdditiveFilteredRingData R)

def predecessor (n : ℕ) : AddSubgroup R :=
  if n = 0 then ⊥ else F.carrier (n - 1)

theorem predecessor_le (n : ℕ) :
    predecessor F n ≤ F.carrier n := by
  by_cases hn : n = 0
  · simp [predecessor, hn]
  · rw [predecessor, if_neg hn]
    exact F.monotone (Nat.sub_le n 1)

def layerSubmodule (n : ℕ) : Submodule ℤ (F.carrier n) :=
  (AddSubgroup.toIntSubmodule (predecessor F n)).comap
    (F.carrier n).subtype.toIntLinearMap

abbrev associatedLayer (n : ℕ) :=
  F.carrier n ⧸ layerSubmodule F n

def associatedClass (n : ℕ) (a : R) (ha : a ∈ F.carrier n) :
    associatedLayer F n :=
  Submodule.Quotient.mk (p := layerSubmodule F n) ⟨a, ha⟩

theorem associatedClass_eq_zero_iff
    (n : ℕ) (a : R) (ha : a ∈ F.carrier n) :
    associatedClass F n a ha = 0 ↔ a ∈ predecessor F n := by
  rw [associatedClass, Submodule.Quotient.mk_eq_zero]
  rfl

private theorem lower_mem_target_left {i j : ℕ}
    {a c : R} {b : R} (ha : a ∈ F.carrier i)
    (hc : c ∈ F.carrier i) (hb : b ∈ F.carrier j)
    (h : a - c ∈ predecessor F i) :
    (a - c) * b ∈ predecessor F (i + j) := by
  by_cases hi : i = 0
  · have hz : a - c = 0 := by
      have h' : a - c ∈ (⊥ : AddSubgroup R) := by
        simpa [predecessor, hi] using h
      simpa using h'
    simp [hz]
  · have hprev : a - c ∈ F.carrier (i - 1) := by
      simpa [predecessor, hi] using h
    have hprod : (a - c) * b ∈ F.carrier ((i - 1) + j) :=
      F.mul_mem hprev hb
    have hsum : i + j ≠ 0 := by omega
    rw [predecessor, if_neg hsum]
    exact F.monotone (by omega) hprod

private theorem lower_mem_target_right {i j : ℕ}
    {a : R} {b d : R} (ha : a ∈ F.carrier i)
    (hb : b ∈ F.carrier j) (hd : d ∈ F.carrier j)
    (h : b - d ∈ predecessor F j) :
    a * (b - d) ∈ predecessor F (i + j) := by
  by_cases hj : j = 0
  · have hz : b - d = 0 := by
      have h' : b - d ∈ (⊥ : AddSubgroup R) := by
        simpa [predecessor, hj] using h
      simpa using h'
    simp [hz]
  · have hprev : b - d ∈ F.carrier (j - 1) := by
      simpa [predecessor, hj] using h
    have hprod : a * (b - d) ∈ F.carrier (i + (j - 1)) :=
      F.mul_mem ha hprev
    have hsum : i + j ≠ 0 := by omega
    rw [predecessor, if_neg hsum]
    exact F.monotone (by omega) hprod

private theorem mul_diff_mem_predecessor {i j : ℕ}
    {a c : R} (ha : a ∈ F.carrier i) (hc : c ∈ F.carrier i)
    {b d : R} (hb : b ∈ F.carrier j) (hd : d ∈ F.carrier j)
    (hac : a - c ∈ predecessor F i)
    (hbd : b - d ∈ predecessor F j) :
    a * b - c * d ∈ predecessor F (i + j) := by
  have hleft : (a - c) * b ∈ predecessor F (i + j) :=
    lower_mem_target_left F ha hc hb hac
  have hright : c * (b - d) ∈ predecessor F (i + j) :=
    lower_mem_target_right F hc hb hd hbd
  rw [show a * b - c * d = (a - c) * b + c * (b - d) by
    noncomm_ring]
  exact (predecessor F (i + j)).add_mem hleft hright

def associatedLayerMul (i j : ℕ)
    (x : associatedLayer F i) (y : associatedLayer F j) :
    associatedLayer F (i + j) :=
  Quotient.liftOn₂ x y
    (fun a b => associatedClass F (i + j) (a.1 * b.1)
      (F.mul_mem a.2 b.2))
    (by
      intro a b c d hac hbd
      apply (Submodule.Quotient.eq _).mpr
      change a.1 * b.1 - c.1 * d.1 ∈ predecessor F (i + j)
      apply mul_diff_mem_predecessor F a.2 c.2 b.2 d.2
      · have hac' : a.1 - c.1 ∈
            AddSubgroup.toIntSubmodule (predecessor F i) := by
          have hq := (Submodule.quotientRel_def
            (layerSubmodule F i)).mp hac
          exact (Submodule.mem_comap.mp hq)
        exact hac'
      · have hbd' : b.1 - d.1 ∈
            AddSubgroup.toIntSubmodule (predecessor F j) := by
          have hq := (Submodule.quotientRel_def
            (layerSubmodule F j)).mp hbd
          exact (Submodule.mem_comap.mp hq)
        exact hbd')

@[simp] theorem associatedLayerMul_mk_mk
    (i j : ℕ) (a : F.carrier i) (b : F.carrier j) :
    associatedLayerMul F i j
      (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      associatedClass F (i + j) (a.1 * b.1) (F.mul_mem a.2 b.2) := rfl

theorem exists_associatedClass_ne_zero_of_ne_zero {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ F.carrier n,
      associatedClass F n a hna ≠ 0 := by
  classical
  let hex : ∃ k : ℕ, a ∈ F.carrier k := F.exhaustive a
  let m : ℕ := Nat.find hex
  have hm : a ∈ F.carrier m := Nat.find_spec hex
  have hmin : ∀ k < m, a ∉ F.carrier k := by
    intro k hkm hk
    exact (not_lt_of_ge (Nat.find_min' hex hk)) hkm
  refine ⟨m, hm, ?_⟩
  intro hclass
  have hpred : a ∈ predecessor F m :=
    (associatedClass_eq_zero_iff F m a hm).mp hclass
  by_cases hm0 : m = 0
  · have hpred0 : a ∈ (⊥ : AddSubgroup R) := by
      rw [hm0] at hpred
      simpa [predecessor] using hpred
    exact ha (by simpa using hpred0)
  · have hlt : m - 1 < m :=
      Nat.sub_lt (Nat.zero_lt_of_ne_zero hm0) zero_lt_one
    exact hmin (m - 1) hlt (by simpa [predecessor, hm0] using hpred)

end AdditiveFilteredRingData

end Layers

section Class

variable {K : Type v} {R : Type u}
variable [Field K] [Ring R] [Nontrivial R] [Algebra K R]

/- A structural class for the M01 input.  The degree-zero and centrality
   fields are actual equalities involving the given algebra map. -/
structure M01FilteredAlgebra (K : Type v) (R : Type u)
    [Field K] [Ring R] [Nontrivial R] [Algebra K R] where
  filtration : AdditiveFilteredRingData R
  central : ∀ (k : K) (a : R),
    algebraMap K R k * a = a * algebraMap K R k
  degree_zero :
    (filtration.carrier 0 : Set R) = Set.range (algebraMap K R)

namespace M01FilteredAlgebra

variable (A : M01FilteredAlgebra K R)

def reesRing : Subring (ReesPolynomial R) :=
  SymplecticStafford.Filtered.reesSubring A.filtration.toNegFiltrationData

theorem algebraMap_injective :
    Function.Injective (algebraMap K R) := by
  intro x y hxy
  by_contra hxy'
  have hz : algebraMap K R (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcancel : (x - y)⁻¹ * (x - y) = (1 : K) :=
    inv_mul_cancel₀ (sub_ne_zero.mpr hxy')
  have hbad : (0 : R) = 1 := by
    have hmap := congrArg (algebraMap K R) hcancel
    simpa [map_mul, hz] using hmap
  exact zero_ne_one hbad

theorem degree_zero_mem (k : K) :
    algebraMap K R k ∈ A.filtration.carrier 0 := by
  change algebraMap K R k ∈ (A.filtration.carrier 0 : Set R)
  rw [A.degree_zero]
  exact ⟨k, rfl⟩

theorem separated_detection {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ A.filtration.carrier n,
      AdditiveFilteredRingData.associatedClass A.filtration n a hna ≠ 0 :=
  A.filtration.exists_associatedClass_ne_zero_of_ne_zero ha

end M01FilteredAlgebra

end Class

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.M01FilteredAlgebra.algebraMap_injective
#print axioms SymplecticStafford.Filtered.M01FilteredAlgebra.separated_detection
