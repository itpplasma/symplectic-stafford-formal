import SymplecticStafford.FiniteLength.RepeatedDivisionBlockBoundary
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Rat.Defs

/-!
# Independent oracle for the repeated-block boundary

The oracle expands the concrete rational two-copy zero block and checks both
the finite-module premise and the all-parameter bad set.  It then instantiates
the universal-finiteness refutation with the identity central embedding.
-/

namespace SymplecticStafford.FiniteLength.RepeatedDivisionBlockBoundaryOracle

open SymplecticStafford.FiniteLength

example :
    Module.Finite ℚ (ℚ × ℚ) := by
  infer_instance

example :
    ({z : ℚ | ¬ LinearIndependent ℚ
      (fun _ : Fin 2 => (0 : ℚ × ℚ))} : Set ℚ) = Set.univ := by
  have hzero : ¬ LinearIndependent ℚ
      (fun _ : Fin 2 => (0 : ℚ × ℚ)) := by
    intro h
    have hz := h.ne_zero (0 : Fin 2)
    exact hz (by simp)
  ext z
  simp [hzero]

example :
    ¬ ({z : ℚ | ¬ LinearIndependent ℚ
      (fun _ : Fin 2 => (0 : ℚ × ℚ))}).Finite := by
  exact (repeated_zero_block_bad_set_not_finite (K := ℚ) (E := ℚ)).2

example :
    ¬ (∀ (x y : Fin 2 → (ℚ × ℚ)), Set.Finite
      {z : ℚ | ¬ LinearIndependent ℚ
        (fun i => x i + (RingHom.id ℚ z) • y i)}) := by
  exact no_unconditional_repeated_division_pencil_finiteness
    (K := ℚ) (E := ℚ) (RingHom.id ℚ)

end SymplecticStafford.FiniteLength.RepeatedDivisionBlockBoundaryOracle

#print axioms
  SymplecticStafford.FiniteLength.no_unconditional_repeated_division_pencil_finiteness
