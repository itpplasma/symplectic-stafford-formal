module

public import Mathlib.Tactic.NoncommRing
public import SymplecticStafford.Filtered.RingFiltrationBridge

@[expose] public section

/-!
# Multiplication on the actual associated layers

`RingFiltrationBridge` constructs the quotient of an increasing ring
filtration in each degree.  This file supplies the next, genuinely
algebraic, part of the associated-graded construction: multiplication of
classes in degrees `i` and `j`.

The order is the original order in `R`.  Independence of representatives is
proved separately in the two variables.  A change in the first representative
is handled by the right-submodule structure of the lower layer; a change in
the second is handled by filtered multiplicativity.  No commutativity,
localization, Rees Noetherianity, or spectrum identification is assumed.
-/

namespace SymplecticStafford.Filtered

universe u

open SymplecticStafford

section

variable {R : Type u} [Ring R]
variable (F : RingFiltrationData (R := R))

namespace RingFiltrationData

private theorem lower_mem_target_left {i j : ℕ} {a c b : R}
    (h : a - c ∈ predecessor F i) (hb : b ∈ F.carrier j) :
    (a - c) * b ∈ predecessor F (i + j) := by
  by_cases hij : i + j = 0
  · have hi : i = 0 := Nat.eq_zero_of_add_eq_zero_right hij
    have hzero : a - c = 0 := by
      have hz : a - c ∈ (⊥ : Submodule Rᵐᵒᵖ R) := by
        simpa [predecessor, hi] using h
      simpa using hz
    simp [predecessor, hij, hzero]
  · rw [predecessor, if_neg hij]
    by_cases hi : i = 0
    · have hzero : a - c = 0 := by
        have hz : a - c ∈ (⊥ : Submodule Rᵐᵒᵖ R) := by
          simpa [predecessor, hi] using h
        simpa using hz
      simp [hzero]
    · have hprev : a - c ∈ F.carrier (i - 1) := by
        simpa [predecessor, hi] using h
      have hright : (a - c) * b ∈ F.carrier (i - 1) := by
        simpa using (F.carrier (i - 1)).smul_mem (MulOpposite.op b) hprev
      exact F.monotone (by omega) hright

private theorem lower_mem_target_right {i j : ℕ} {a b c : R}
    (ha : a ∈ F.carrier i) (h : b - c ∈ predecessor F j) :
    a * (b - c) ∈ predecessor F (i + j) := by
  by_cases hj : j = 0
  · have hzero : b - c = 0 := by
      have hz : b - c ∈ (⊥ : Submodule Rᵐᵒᵖ R) := by
        simpa [predecessor, hj] using h
      simpa using hz
    simp [hzero]
  · have hprev : b - c ∈ F.carrier (j - 1) := by
      simpa [predecessor, hj] using h
    have hprod : a * (b - c) ∈ F.carrier (i + (j - 1)) :=
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
    lower_mem_target_left F hac hb
  have hright : c * (b - d) ∈ predecessor F (i + j) :=
    lower_mem_target_right F hc hbd
  rw [show a * b - c * d = (a - c) * b + c * (b - d) by noncomm_ring]
  exact (predecessor F (i + j)).add_mem hleft hright

/-- Multiplication of two actual associated-layer classes, preserving the
original order of factors. -/
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
      · have hac' : a - c ∈ layerSubmodule F i :=
          (Submodule.quotientRel_def (layerSubmodule F i)).mp hac
        exact (Submodule.mem_comap.mp hac')
      · have hbd' : b - d ∈ layerSubmodule F j :=
          (Submodule.quotientRel_def (layerSubmodule F j)).mp hbd
        exact (Submodule.mem_comap.mp hbd'))

@[simp] theorem associatedLayerMul_mk_mk
    (i j : ℕ) (a : F.carrier i) (b : F.carrier j) :
    associatedLayerMul F i j
      (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      associatedClass F (i + j) (a.1 * b.1) (F.mul_mem a.2 b.2) := rfl

theorem associatedLayerMul_eq_class
    (i j : ℕ) (a : F.carrier i) (b : F.carrier j) :
    associatedLayerMul F i j
      (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      associatedClass F (i + j) (a.1 * b.1) (F.mul_mem a.2 b.2) :=
  associatedLayerMul_mk_mk F i j a b

theorem associatedLayerMul_respects_left
    {i j : ℕ} {x x' : associatedLayer F i} (hx : x = x')
    (y : associatedLayer F j) :
    associatedLayerMul F i j x y = associatedLayerMul F i j x' y := by
  rw [hx]

theorem associatedLayerMul_respects_right
    {i j : ℕ} (x : associatedLayer F i)
    {y y' : associatedLayer F j} (hy : y = y') :
    associatedLayerMul F i j x y = associatedLayerMul F i j x y' := by
  rw [hy]

-- Associativity of the dependent family requires an explicit transport along
-- `Nat.add_assoc`; the representative-independent binary operation above is
-- the M01 boundary used by downstream modules.

end RingFiltrationData

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.RingFiltrationData.associatedLayerMul
#print axioms SymplecticStafford.Filtered.RingFiltrationData.associatedLayerMul_mk_mk
