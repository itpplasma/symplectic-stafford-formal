import SymplecticStafford.Ordered.Affine
import SymplecticStafford.Ordered.RightClear
import SymplecticStafford.FiniteLength.Pencil
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
Independent concrete consumers for the ordered and finite-length checkpoint.
These examples compute in `ℕ` and `ℚ`; they are not proofs by replaying the
generic theorem statements with the same variables.
-/

namespace SymplecticStaffordTest

open SymplecticStafford.Ordered
open SymplecticStafford.FiniteLength

example :
    (3 : ℤ) * 11 + (5 + 17 * 7) * 3 * 13 =
      (3 : ℤ) * 11 + 5 * 3 * 13 + 17 * (7 * 3 * 13) := by
  simpa only [mul_add, add_mul] using
    (affine_source_expand (3 : ℤ) 5 7 11 13 17)

example : ∃ n : ℕ, ∀ x ∈ ([2, 3] : List ℕ), ∃ y : ℕ,
    x * ((MonoidHom.id ℕ) 5) ^ n = (MonoidHom.id ℕ) y := by
  have hc : ∀ x ∈ ([2, 3] : List ℕ), RightClearable (MonoidHom.id ℕ) 5 x := by
    intro x hx
    refine ⟨0, x, ?_⟩
    simp
  obtain ⟨n, hn⟩ := exists_common_right_clear (MonoidHom.id ℕ) 5 [2, 3] hc
  exact ⟨n, hn⟩

example : TopGenerator (fun _ : Fin 2 => (1 : ℚ)) := by
  apply (semisimple_top_criterion (fun _ : Fin 2 => (1 : ℚ))).2
  intro i
  exact one_ne_zero

example : ¬ TopGenerator (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1) := by
  intro h
  have hz := (semisimple_top_criterion
    (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)).1 h 0
  exact hz (by simp)

example : Set.Finite ({z : ℚ | ∃ i : Fin 2, (1 : ℚ) + z * 1 = 0} : Set ℚ) := by
  let ιmap : (i : Fin 2) → ℚ →+* ℚ := fun _ => RingHom.id ℚ
  apply finite_pencil_exceptions ιmap (fun _ => (1 : ℚ)) (fun _ => (1 : ℚ))
  · intro i
    exact one_ne_zero
  · intro i
    intro x y h
    exact h

end SymplecticStaffordTest
