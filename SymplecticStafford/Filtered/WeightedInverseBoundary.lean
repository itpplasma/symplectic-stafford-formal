import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Monic

/-!
# A strict-negative-degree inverse boundary

The M04 matrix argument uses more than a strict degree drop: it needs the
chart theorem saying that `1 - c` is an *actual unit* whenever `c` has
negative degree.  This file gives a small kernel-checked obstruction to
silently dropping that unit input.

On `ℤ[X]`, regard a nonzero polynomial of positive `natDegree` as having a
formal negative degree `-natDegree`.  Then `X` is strictly negative-degree,
but `1 - X` is not a unit.  Thus degree inequalities alone, in an arbitrary
ring, cannot justify the inverse step.  The intended full-symbol localization
must separately prove the below-one unit criterion.
-/

namespace SymplecticStafford.Filtered

open scoped Polynomial

/- A deliberately minimal negative-degree predicate; it records only the
  order information used by the failed inference, not a fake localization. -/
def PolynomialNegativeDegree (p : ℤ[X]) : Prop :=
  p = 0 ∨ 0 < p.natDegree

theorem polynomial_X_negativeDegree :
    PolynomialNegativeDegree (Polynomial.X : ℤ[X]) := by
  right
  simp

theorem polynomial_one_sub_X_not_isUnit :
    ¬ IsUnit ((1 : ℤ[X]) - Polynomial.X) := by
  intro h
  have hdeg : 0 < ((1 : ℤ[X]) - Polynomial.X).natDegree := by
    have hEq : ((1 : ℤ[X]) - Polynomial.X).natDegree = 1 := by
      rw [show (1 : ℤ[X]) - Polynomial.X = -(Polynomial.X - 1) by ring,
        Polynomial.natDegree_neg]
      exact Polynomial.natDegree_X_sub_C (R := ℤ) 1
    rw [hEq]
    norm_num
  exact (Polynomial.not_isUnit_of_natDegree_pos _ hdeg) h

/- The exact failed implication is refuted by one concrete coefficient. -/
theorem negativeDegree_does_not_force_one_sub_unit :
    ¬ (∀ c : ℤ[X], PolynomialNegativeDegree c → IsUnit (1 - c)) := by
  intro h
  have hc : IsUnit ((1 : ℤ[X]) - Polynomial.X) :=
    h Polynomial.X polynomial_X_negativeDegree
  exact polynomial_one_sub_X_not_isUnit hc

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.negativeDegree_does_not_force_one_sub_unit
