module

public import SymplecticStafford.Filtered.FullSymbolRightLocalization

@[expose] public section

/-!
# Recombining a localized two-generator certificate in the original ring

An actual right Ore chart can clear finitely many localized coefficients with
one denominator on the right.  This file performs the remaining algebraic
step for the two-generator identity used by the Stafford argument.  After
right multiplication by that common denominator, injectivity of the original
numerator map reflects the result to literal cofactors in the original ring.

The factor order is part of the statement: the returned identity is
`s = d * r + (f * d) * t`.  The theorem does not construct the chart,
denominator submonoid, or any power-Ore/completion comparison.
-/

namespace SymplecticStafford.Filtered.FullSymbolOriginalCofactor

universe u

open FullSymbolRightLocalization

variable {R : Type u} [Ring R]

theorem localized_two_generator_to_original
    (C : FullSymbolRightLocalization.Data R)
    (d f : R) (q₁ q₂ : C.Localization)
    (hidentity : C.numerator d * q₁ +
        (C.numerator f * C.numerator d) * q₂ = 1) :
    ∃ (s r t : R), s ∈ C.denominators ∧
      s = d * r + (f * d) * t := by
  rcases C.common_right_clear [q₁, q₂] with ⟨s, hs⟩
  rcases hs q₁ (by simp) with ⟨r, hr⟩
  rcases hs q₂ (by simp) with ⟨t, ht⟩
  have hmul := congrArg (fun q : C.Localization =>
    q * C.numerator (s : R)) hidentity
  have hlocalized :
      C.numerator d * C.numerator r +
          (C.numerator f * C.numerator d) * C.numerator t =
        C.numerator (s : R) := by
    calc
      C.numerator d * C.numerator r +
          (C.numerator f * C.numerator d) * C.numerator t =
          (C.numerator d * q₁ +
            (C.numerator f * C.numerator d) * q₂) *
              C.numerator (s : R) := by
        rw [add_mul]
        calc
          C.numerator d * C.numerator r +
              (C.numerator f * C.numerator d) * C.numerator t =
              C.numerator d *
                  (q₁ * C.numerator (s : R)) +
                (C.numerator f * C.numerator d) *
                  (q₂ * C.numerator (s : R)) := by rw [hr, ht]
          _ = C.numerator d * q₁ * C.numerator (s : R) +
                C.numerator f * C.numerator d * q₂ *
                  C.numerator (s : R) := by simp only [mul_assoc]
      _ = 1 * C.numerator (s : R) := hmul
      _ = C.numerator (s : R) := one_mul _
  refine ⟨s, r, t, s.property, ?_⟩
  apply C.numerator_injective
  simpa only [map_add, map_mul] using hlocalized.symm

end SymplecticStafford.Filtered.FullSymbolOriginalCofactor

#print axioms
  SymplecticStafford.Filtered.FullSymbolOriginalCofactor.localized_two_generator_to_original
