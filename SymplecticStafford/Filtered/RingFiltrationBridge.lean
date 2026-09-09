import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic.NormNum
import SymplecticStafford.Filtered.Localization

/-!
# The first filtered/Rees producer boundary

`FiltrationData` is intentionally set-valued and semiring-general.  This file
records the exact missing structure for the M01--M02 producer: layers must be
actual submodules for the opposite action before associated quotients can be
formed.  A concrete exhaustive multiplicative filtration on `ℤ` shows that
the old API does not imply this closure.

The repaired `RingFiltrationData` interface then constructs genuine additive
associated-layer quotients and detects every nonzero original element in one
of them by a least filtration degree.  It does not claim that the layers form
the full commutative Rees algebra, that the Rees ring is Noetherian, or that
its spectrum is the paper's characteristic support.  Those remain separate
producer obligations.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford

section MissingClosure

/-- A valid old-style filtration whose degree-zero set is only the nonnegative
integers.  All higher layers are the whole ring, so it is exhaustive. -/
def nonnegativeStepFiltration : FiltrationData ℤ where
  carrier := fun n => if n = 0 then {z : ℤ | 0 ≤ z} else Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by
    intro i j a b ha hb
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · have ha' : 0 ≤ a := by simpa [hi] using ha
        have hb' : 0 ≤ b := by simpa [hj] using hb
        simpa [hi, hj] using add_nonneg ha' hb'
      · simp [hi, hj]
    · simp [hi]
  mul_mem := by
    intro i j a b ha hb
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · have ha' : 0 ≤ a := by simpa [hi] using ha
        have hb' : 0 ≤ b := by simpa [hj] using hb
        simpa [hi, hj] using mul_nonneg ha' hb'
      · simp [hi, hj]
    · simp [hi]
  monotone := by
    intro i j hij z hz
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simpa [hi, hj] using hz
      · simp [hj]
    ·
      have hj : j ≠ 0 := by
        intro hj0
        subst j
        exact hi (Nat.eq_zero_of_le_zero hij)
      simp [hj]
  exhaustive := by
    intro z
    exact ⟨1, by simp⟩

theorem nonnegativeStepFiltration_degree_zero_not_submodule :
    ¬ ∃ P : Submodule ℤᵐᵒᵖ ℤ,
      (P : Set ℤ) = nonnegativeStepFiltration.carrier 0 := by
  rintro ⟨P, hP⟩
  have h1 : (1 : ℤ) ∈ P := by
    change (1 : ℤ) ∈ (P : Set ℤ)
    rw [hP]
    simp [nonnegativeStepFiltration]
  have hneg : (-1 : ℤ) ∈ P := P.neg_mem h1
  have hneg' : (-1 : ℤ) ∈ nonnegativeStepFiltration.carrier 0 := by
    rw [← hP]
    exact hneg
  have hcontra : (0 : ℤ) ≤ -1 := by
    simpa [nonnegativeStepFiltration] using hneg'
  norm_num at hcontra

end MissingClosure

section RepairedRingFiltration

variable {R : Type u} [Ring R]

/-- A ring filtration with genuine opposite-action submodule layers.  The
`mul_mem` field preserves the original coefficient order `a * b`. -/
structure RingFiltrationData where
  carrier : ℕ → Submodule Rᵐᵒᵖ R
  one_mem : (1 : R) ∈ carrier 0
  mul_mem : ∀ {i j : ℕ} {a b : R}, a ∈ carrier i → b ∈ carrier j →
    a * b ∈ carrier (i + j)
  monotone : Monotone carrier
  exhaustive : ∀ a : R, ∃ n : ℕ, a ∈ carrier n

namespace RingFiltrationData

variable (F : RingFiltrationData (R := R))

/-- Forgetting submodule structure recovers the old set-valued filtration. -/
def toFiltrationData (F : RingFiltrationData (R := R)) : FiltrationData R where
  carrier := fun n => F.carrier n
  zero_mem := (F.carrier 0).zero_mem
  one_mem := F.one_mem
  add_mem := by
    intro i j a b ha hb
    exact (F.carrier (max i j)).add_mem
      (F.monotone (Nat.le_max_left i j) ha)
      (F.monotone (Nat.le_max_right i j) hb)
  mul_mem := F.mul_mem
  monotone := F.monotone
  exhaustive := F.exhaustive

@[simp] theorem toFiltrationData_carrier
    (F : RingFiltrationData (R := R)) (n : ℕ) :
    (toFiltrationData F).carrier n = F.carrier n := rfl

theorem neg_mem (F : RingFiltrationData (R := R)) (n : ℕ)
    {a : R} (ha : a ∈ F.carrier n) :
    -a ∈ F.carrier n := (F.carrier n).neg_mem ha

/-- The lower layer used for the degree-zero associated quotient is zero. -/
def predecessor (F : RingFiltrationData (R := R)) (n : ℕ) :
    Submodule Rᵐᵒᵖ R :=
  if n = 0 then ⊥ else F.carrier (n - 1)

theorem predecessor_le (F : RingFiltrationData (R := R)) (n : ℕ) :
    predecessor F n ≤ F.carrier n := by
  by_cases hn : n = 0
  · simp [predecessor, hn]
  · rw [predecessor, if_neg hn]
    exact F.monotone (Nat.sub_le n 1)

/-- The actual additive quotient of the `n`th layer by its predecessor. -/
def layerSubmodule (F : RingFiltrationData (R := R)) (n : ℕ) :
    Submodule Rᵐᵒᵖ (F.carrier n) :=
  (predecessor F n).comap (F.carrier n).subtype

abbrev associatedLayer (F : RingFiltrationData (R := R)) (n : ℕ) :=
  F.carrier n ⧸ layerSubmodule F n

/-- The class of an element in its genuine associated layer. -/
def associatedClass (F : RingFiltrationData (R := R)) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) : associatedLayer F n :=
  Submodule.Quotient.mk (p := layerSubmodule F n) ⟨a, ha⟩

theorem associatedClass_eq_zero_iff
    (F : RingFiltrationData (R := R))
    (n : ℕ) (a : R) (ha : a ∈ F.carrier n) :
    associatedClass F n a ha = 0 ↔ a ∈ predecessor F n := by
  rw [associatedClass, Submodule.Quotient.mk_eq_zero]
  rfl

theorem exists_associatedClass_ne_zero_of_ne_zero
    (F : RingFiltrationData (R := R))
    {a : R} (ha : a ≠ 0) :
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
  · have hpred0 : a ∈ (⊥ : Submodule Rᵐᵒᵖ R) := by
      rw [hm0] at hpred
      simpa [predecessor] using hpred
    exact ha (by simpa using hpred0)
  · have hlt : m - 1 < m := Nat.sub_lt (Nat.zero_lt_of_ne_zero hm0) zero_lt_one
    exact hmin (m - 1) hlt (by simpa [predecessor, hm0] using hpred)

/-- The support of the genuine associated layers, expressed through actual
nonzero quotient classes rather than a supplied support set. -/
def associatedLayerSupport : Set ℕ :=
  {n | ∃ a : R, ∃ ha : a ∈ F.carrier n,
    associatedClass F n a ha ≠ 0}

theorem associatedLayerSupport_nonempty_iff_exists_ne_zero :
    (associatedLayerSupport F).Nonempty ↔ ∃ a : R, a ≠ 0 := by
  constructor
  · rintro ⟨n, ⟨a, ha, hclass⟩⟩
    refine ⟨a, ?_⟩
    intro hzero
    subst a
    have hz : (0 : associatedLayer F n) = 0 := rfl
    exact hclass hz
  · rintro ⟨a, ha⟩
    obtain ⟨n, hna, hclass⟩ :=
      exists_associatedClass_ne_zero_of_ne_zero F ha
    exact ⟨n, ⟨a, hna, hclass⟩⟩

end RingFiltrationData

end RepairedRingFiltration

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.nonnegativeStepFiltration_degree_zero_not_submodule
#print axioms SymplecticStafford.Filtered.RingFiltrationData.exists_associatedClass_ne_zero_of_ne_zero
#print axioms SymplecticStafford.Filtered.RingFiltrationData.associatedLayerSupport_nonempty_iff_exists_ne_zero
