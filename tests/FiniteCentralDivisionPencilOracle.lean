import SymplecticStafford.FiniteLength.FiniteCentralDivisionPencil
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Independent oracle for finite-central division blocks

The one-factor rational block has the unique bad scalar `-1`.  This oracle
checks the new finite-dimensional-over-the-center bridge and its finite-family
wrapper independently of the determinant implementation.
-/

namespace SymplecticStafford.FiniteLength.FiniteCentralDivisionPencilOracle

open SymplecticStafford.FiniteLength

abbrev K := ℚ
abbrev E := ℚ
abbrev V := ℚ

example : Set.Finite ({z : K | ¬ LinearIndependent E
    (fun _ : Fin 1 => (1 + z : V))} : Set K) := by
  have hbad_eq : ({z : K | ¬ LinearIndependent E
      (fun _ : Fin 1 => (1 + z : V))} : Set K) = {-1} := by
    ext z
    change (¬ LinearIndependent E (fun _ : Fin 1 => (1 + z : V))) ↔ z = -1
    rw [linearIndependent_unique_iff]
    constructor
    · intro h
      have hz : (1 + z : K) = 0 := not_ne_iff.mp h
      linarith
    · intro h hz
      apply hz
      linarith
  have h := finite_bad_of_finite_central_division_pencil
    (ιmap := RingHom.id K)
    (central_coeff := by
      intro k e
      simp [Algebra.smul_def])
    (central_embedding := by
      intro k e
      simp [Algebra.smul_def, mul_comm])
    (central_vector := by
      intro k v
      simp [Algebra.smul_def])
    (x := fun _ : Fin 1 => (1 : V))
    (y := fun _ : Fin 1 => (1 : V))
    (by rw [linearIndependent_unique_iff]; norm_num)
  have h' : ({z : K | ¬ LinearIndependent E
      (fun _ : Fin 1 => (1 + z : V))} : Set K).Finite := by
    simpa [RingHom.id_apply, smul_eq_mul] using h
  exact h'

example : Set.Finite ({z : K | ¬ ∀ _ : Unit, LinearIndependent E
    (fun _ : Fin 1 => (1 + z : V))} : Set K) := by
  have h := finite_bad_of_finite_central_division_blocks
    (ιmap := fun _ : Unit => RingHom.id K)
    (central_coeff := by
      intro j k e
      simp [Algebra.smul_def])
    (central_embedding := by
      intro j k e
      simp [Algebra.smul_def, mul_comm])
    (central_vector := by
      intro j k v
      simp [Algebra.smul_def])
    (x := fun _ : Unit => fun _ : Fin 1 => (1 : V))
    (y := fun _ : Unit => fun _ : Fin 1 => (1 : V))
    (hx := by
      intro j
      rw [linearIndependent_unique_iff]
      norm_num)
  simpa [RingHom.id_apply, smul_eq_mul] using h

end SymplecticStafford.FiniteLength.FiniteCentralDivisionPencilOracle

#print axioms SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_pencil
#print axioms SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_blocks
