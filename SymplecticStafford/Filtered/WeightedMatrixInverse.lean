module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-!
# A finite original-ring inverse certificate

The weighted good-module argument needs an actual inverse for `1 - C`, not
just a degree estimate.  This file records the part that is unconditional:
if the strict correction matrix comes with a finite nilpotence certificate,
the inverse is the finite geometric sum.  The proof is valid for matrices
over a noncommutative ring and keeps both multiplication orders.

This is deliberately a bridge, not a completion of M04.  A strict negative
weighted degree in an arbitrary chart does not imply nilpotence (nor that
`1 - c` is a unit); the separate `WeightedInverseBoundary` records that
failure.  A full M04 proof must therefore derive either this certificate or
the corresponding finite Schur-elimination unit certificates in the actual
full-symbol localization.
-/

namespace SymplecticStafford.Filtered

universe u v

namespace WeightedMatrixInverse

open scoped BigOperators

variable {ι : Type u} {R : Type v}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-!
The scalar hypothesis used by a finite Schur argument is stronger than a
strict degree drop.  This record names the exact bounded chart input without
pretending to derive it from an arbitrary filtration.  In particular,
`below_one_inverse` supplies both an actual inverse and the nonpositive degree
bound needed to preserve strictness after Schur complementation.
-/
structure BoundedBelowOneData (A : Type*) [Ring A] where
  /-- `⊥` is the degree of zero, so multiplication by zero is harmless. -/
  degree : A → WithBot Int
  degree_zero : degree 0 = ⊥
  degree_one : degree 1 = 0
  degree_add_le_max : ∀ a b, degree (a + b) ≤ max (degree a) (degree b)
  degree_mul_le_add : ∀ a b, degree (a * b) ≤ degree a + degree b
  below_one_inverse : ∀ c, degree c < 0 →
    ∃ u, (1 - c) * u = 1 ∧ u * (1 - c) = 1 ∧ degree u ≤ 0

namespace BoundedBelowOneData

variable {A : Type*} [Ring A] (D : BoundedBelowOneData A)

theorem isUnit_one_sub_of_negative {c : A} (hc : D.degree c < 0) :
    IsUnit (1 - c) := by
  rcases D.below_one_inverse c hc with ⟨u, hleft, hright, _⟩
  exact ⟨⟨1 - c, u, hleft, hright⟩, rfl⟩

theorem exists_bounded_inverse {c : A} (hc : D.degree c < 0) :
    ∃ u, (1 - c) * u = 1 ∧ u * (1 - c) = 1 ∧ D.degree u ≤ 0 :=
  D.below_one_inverse c hc

end BoundedBelowOneData

private theorem geom_left (C : Matrix ι ι R) (n : ℕ) :
    (1 - C) * (∑ k ∈ Finset.range n, C ^ k) = 1 - C ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      (1 - C) * (∑ k ∈ Finset.range n, C ^ k + C ^ n) =
          (1 - C) * (∑ k ∈ Finset.range n, C ^ k) + (1 - C) * C ^ n := by
            rw [mul_add]
      _ = (1 - C ^ n) + (1 - C) * C ^ n := by rw [ih]
      _ = 1 - C ^ (n + 1) := by
        rw [sub_mul, one_mul, pow_succ]
        have hcomm : C * C ^ n = C ^ n * C := (Commute.self_pow C n).eq
        rw [hcomm]
        noncomm_ring

private theorem geom_right (C : Matrix ι ι R) (n : ℕ) :
    (∑ k ∈ Finset.range n, C ^ k) * (1 - C) = 1 - C ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      (∑ k ∈ Finset.range n, C ^ k + C ^ n) * (1 - C) =
          (∑ k ∈ Finset.range n, C ^ k) * (1 - C) + C ^ n * (1 - C) := by
            rw [add_mul]
      _ = (1 - C ^ n) + C ^ n * (1 - C) := by rw [ih]
      _ = 1 - C ^ (n + 1) := by
        rw [mul_sub, mul_one, pow_succ]
        noncomm_ring

/-- A finite geometric-series inverse for a nilpotent correction matrix. -/
theorem isUnit_one_sub_of_pow_eq_zero (C : Matrix ι ι R) (n : ℕ)
    (hC : C ^ n = 0) : IsUnit (1 - C) := by
  let S : Matrix ι ι R := ∑ k ∈ Finset.range n, C ^ k
  have hleft : (1 - C) * S = 1 := by
    dsimp [S]
    rw [geom_left C n, hC, sub_zero]
  have hright : S * (1 - C) = 1 := by
    dsimp [S]
    rw [geom_right C n, hC, sub_zero]
  refine ⟨⟨1 - C, S, hleft, hright⟩, rfl⟩

/-- The finite sum is an explicit two-sided inverse, useful for a module row. -/
theorem finite_inverse_of_pow_eq_zero (C : Matrix ι ι R) (n : ℕ)
    (hC : C ^ n = 0) :
    ∃ S : Matrix ι ι R, (1 - C) * S = 1 ∧ S * (1 - C) = 1 := by
  refine ⟨∑ k ∈ Finset.range n, C ^ k, ?_, ?_⟩
  · rw [geom_left C n, hC, sub_zero]
  · rw [geom_right C n, hC, sub_zero]

/-- A row killed by the correction matrix is zero once the finite inverse is
    available.  This is the exact module-side use of the inverse certificate.
    The order of the row action is intentional: it is right multiplication. -/
theorem vecMul_eq_zero_of_mul_one_sub_eq_zero (w : ι → R) (C : Matrix ι ι R)
    (n : ℕ) (hC : C ^ n = 0)
    (h : Matrix.vecMul w (1 - C) = 0) : w = 0 := by
  rcases finite_inverse_of_pow_eq_zero C n hC with ⟨S, hleft, _⟩
  have h' := congrArg (fun v => Matrix.vecMul v S) h
  rw [Matrix.vecMul_vecMul] at h'
  rw [hleft] at h'
  simpa using h'

end WeightedMatrixInverse

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.WeightedMatrixInverse.isUnit_one_sub_of_pow_eq_zero
#print axioms SymplecticStafford.Filtered.WeightedMatrixInverse.finite_inverse_of_pow_eq_zero
#print axioms SymplecticStafford.Filtered.WeightedMatrixInverse.vecMul_eq_zero_of_mul_one_sub_eq_zero
#print axioms SymplecticStafford.Filtered.WeightedMatrixInverse.BoundedBelowOneData.isUnit_one_sub_of_negative
