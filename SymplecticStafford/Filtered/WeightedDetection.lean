module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Basic

@[expose] public section

/-!
# Weighted-top detection for finite triangular actions

This is the finite, algebraic core of the weighted-top part of the paper's
M04 boundary.  A weight takes values in `Int`, so negative degrees are allowed
without a shift or truncation.  The coefficient hypotheses say that a row
cannot see a strictly lower-weight input and that equal-weight off-diagonal
entries vanish.  Consequently a nonzero top coordinate survives the action
when the corresponding diagonal coefficient is nonzero.

This file does **not** construct a characteristic support, a good filtration,
an associated graded object, or a localization.  It also does not claim that
an arbitrary filtered module admits such a finite weighted matrix.  Those are
the missing algebraic inputs around M02--M05; the data below must be supplied
by a later construction.
-/

namespace SymplecticStafford.Filtered

universe u v

section

variable {ι : Type u} {K : Type v}
variable [Fintype ι] [DecidableEq ι] [Semiring K]

/-- A finite weighted triangular coefficient system.

The order is on integer weights, rather than on the natural numbers.  Thus
the interface remains meaningful when some homogeneous pieces have negative
degrees.  `lower_vanish` is the weighted-top triangularity condition, while
`same_weight_vanish` makes each equal-weight block diagonal; this latter
hypothesis is explicit and is not inferred from a filtration.
-/
structure WeightedTriangularData where
  weight : ι → Int
  coefficient : ι → ι → K
  lower_vanish : ∀ i j, weight j < weight i → coefficient i j = 0
  same_weight_vanish : ∀ i j, i ≠ j → weight i = weight j → coefficient i j = 0
  diagonal_ne_zero : ∀ i, coefficient i i ≠ 0

namespace WeightedTriangularData

variable (T : WeightedTriangularData (ι := ι) (K := K))

/-- The finite matrix action associated to the coefficient system. -/
def action (v : ι → K) (i : ι) : K :=
  ∑ j, T.coefficient i j * v j

/-- A coordinate is top among the nonzero coordinates of a vector. -/
def IsTop (v : ι → K) (i : ι) : Prop :=
  v i ≠ 0 ∧ ∀ j, v j ≠ 0 → T.weight j ≤ T.weight i

theorem action_at_top
    {v : ι → K} {i : ι} (hi : IsTop T v i) :
    T.action v i = T.coefficient i i * v i := by
  classical
  rw [action]
  apply Finset.sum_eq_single i
  · intro j hj hji
    by_cases hlow : T.weight j < T.weight i
    · simp [T.lower_vanish i j hlow]
    · by_cases heq : T.weight j = T.weight i
      · have hcoef : T.coefficient i j = 0 :=
          T.same_weight_vanish i j (Ne.symm hji) heq.symm
        simp [hcoef]
      · have hile : T.weight i ≤ T.weight j := le_of_not_gt hlow
        have hineq : T.weight i ≠ T.weight j := Ne.symm heq
        have hgt : T.weight i < T.weight j := lt_of_le_of_ne hile hineq
        have hvj : v j = 0 := by
          by_contra hvj
          exact (not_le_of_gt hgt) (hi.2 j hvj)
        simp [hvj]
  · simp

/-- A nonzero top coordinate is detected by the corresponding output row. -/
theorem action_ne_zero_at_top
    [NoZeroDivisors K]
    {v : ι → K} {i : ι} (hi : IsTop T v i) :
    T.action v i ≠ 0 := by
  rw [T.action_at_top hi]
  exact mul_ne_zero (T.diagonal_ne_zero i) hi.1

/-- Every nonzero finite vector has an integer-weight top coordinate.

The proof takes the maximum of the finite set of weights occurring in the
support.  No nonnegativity assumption on `T.weight` is used.
-/
theorem exists_isTop [Nonempty ι] {v : ι → K} (hv : ∃ j, v j ≠ 0) :
    ∃ i, IsTop T v i := by
  classical
  let support : Finset ι := Finset.univ.filter (fun j => v j ≠ 0)
  have hsupport : support.Nonempty := by
    rcases hv with ⟨j, hj⟩
    exact ⟨j, by simp [support, hj]⟩
  let weighted : Finset Int := support.image T.weight
  have hweighted : weighted.Nonempty :=
    (Finset.image_nonempty).mpr hsupport
  let maximum : Int := weighted.max' hweighted
  have hmaxmem : maximum ∈ weighted :=
    Finset.max'_mem weighted hweighted
  rcases Finset.mem_image.mp hmaxmem with ⟨i, hi_support, hi_weight⟩
  refine ⟨i, ?_, ?_⟩
  · simpa [support] using hi_support
  · intro j hj
    have hj_support : j ∈ support := by simp [support, hj]
    have hj_weighted : T.weight j ∈ weighted :=
      Finset.mem_image.mpr ⟨j, hj_support, rfl⟩
    have hle_max : T.weight j ≤ maximum :=
      Finset.le_max' weighted (T.weight j) hj_weighted
    simpa [hi_weight] using hle_max

/-- Nonzero input gives nonzero output for a weighted triangular system. -/
theorem action_ne_zero_of_nonzero [Nonempty ι]
    [NoZeroDivisors K]
    {v : ι → K} (hv : ∃ j, v j ≠ 0) :
    ∃ i, T.action v i ≠ 0 := by
  rcases T.exists_isTop hv with ⟨i, hi⟩
  exact ⟨i, T.action_ne_zero_at_top hi⟩

end WeightedTriangularData

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.WeightedTriangularData.action_at_top
#print axioms SymplecticStafford.Filtered.WeightedTriangularData.action_ne_zero_at_top
#print axioms SymplecticStafford.Filtered.WeightedTriangularData.exists_isTop
#print axioms SymplecticStafford.Filtered.WeightedTriangularData.action_ne_zero_of_nonzero
