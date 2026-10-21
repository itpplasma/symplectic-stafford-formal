module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-! Constant right denominator clearing in a noncommutative ambient monoid. -/

namespace SymplecticStafford.Ordered

variable {R S : Type*} [Monoid R] [Monoid S]

/-- An ambient element is right-clearable into the image of a monoid hom by
a power of the fixed base denominator. -/
def RightClearable (ι : R →* S) (f : R) (x : S) : Prop :=
  ∃ n : ℕ, ∃ y : R, x * (ι f) ^ n = ι y

private theorem right_clearable_lift
    (ι : R →* S) (f : R) {x : S} {n : ℕ} {y : R}
    (h : x * (ι f) ^ n = ι y) (m : ℕ) :
    x * (ι f) ^ (n + m) = ι (y * f ^ m) := by
  calc
    x * (ι f) ^ (n + m) = (x * (ι f) ^ n) * (ι f) ^ m := by
      rw [pow_add, mul_assoc]
    _ = ι y * (ι f) ^ m := by rw [h]
    _ = ι (y * f ^ m) := by rw [map_mul, map_pow]

private theorem right_clearable_lift_left
    (ι : R →* S) (f : R) {x : S} {n : ℕ} {y : R}
    (h : x * (ι f) ^ n = ι y) (m : ℕ) :
    x * (ι f) ^ (m + n) = ι (y * f ^ m) := by
  rw [Nat.add_comm m n]
  exact right_clearable_lift ι f h m

/-- A finite list of coefficients has one constant right denominator power
clearing all of them simultaneously. -/
theorem exists_common_right_clear (ι : R →* S) (f : R) :
    ∀ (xs : List S),
      (∀ x ∈ xs, RightClearable ι f x) →
        ∃ n : ℕ, ∀ x ∈ xs, ∃ y : R, x * (ι f) ^ n = ι y
  | [], _ => by
      refine ⟨0, ?_⟩
      intro x hx
      simp at hx
  | x :: xs, h => by
      obtain ⟨n, y, hy⟩ := h x (by simp)
      obtain ⟨m, hm⟩ := exists_common_right_clear ι f xs (by
        intro z hz
        exact h z (by simp [hz]))
      refine ⟨n + m, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨y * f ^ m, right_clearable_lift ι f hy m⟩
      · obtain ⟨w, hw⟩ := hm z hz
        exact ⟨w * f ^ n, right_clearable_lift_left ι f hw n⟩

/-- The common-power result for a finite set of coefficients. -/
theorem exists_finset_common_right_clear [DecidableEq S]
    (ι : R →* S) (f : R) (xs : Finset S)
    (h : ∀ x ∈ xs, RightClearable ι f x) :
    ∃ n : ℕ, ∀ x ∈ xs, ∃ y : R, x * (ι f) ^ n = ι y := by
  obtain ⟨n, hn⟩ := exists_common_right_clear ι f xs.toList (by
    intro x hx
    exact h x (Finset.mem_toList.mp hx))
  refine ⟨n, ?_⟩
  intro x hx
  exact hn x (Finset.mem_toList.mpr hx)

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.exists_common_right_clear
#print axioms SymplecticStafford.Ordered.exists_finset_common_right_clear
