module

public import SymplecticStafford.FiniteLength.FiniteCentralDivisionLLD
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

/-!
Independent behavioral oracle for the determinant-free finite-central block
theorem.  The one-dimensional block has the expected unique bad scalar -1;
the theorem is also invoked directly, with its split/independence data
constructed rather than supplied through the old determinant bridge.
-/

namespace SymplecticStafford.FiniteLength.FiniteCentralDivisionLLDOracle

abbrev K := ℚ
abbrev E := ℚ
abbrev V := ℚ

example : Set.Finite ({z : K | ¬ LinearIndependent E
    (fun _ : Fin 1 => (1 + z : V))} : Set K) := by
  simpa [RingHom.id_apply, smul_eq_mul] using
    (finite_bad_of_finite_central_division_pencil_spectrum
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
      (by rw [linearIndependent_unique_iff]; norm_num))

example : ({z : K | ¬ LinearIndependent E
    (fun _ : Fin 1 => (1 + z : V))} : Set K) = {-1} := by
  ext z
  change (¬ LinearIndependent E
      (fun _ : Fin 1 => (1 + z : V))) ↔ z = -1
  rw [linearIndependent_unique_iff]
  constructor
  · intro h
    have hz : (1 + z : K) = 0 := not_ne_iff.mp h
    linarith
  · intro h hz
    apply hz
    linarith

end SymplecticStafford.FiniteLength.FiniteCentralDivisionLLDOracle

#print axioms
  SymplecticStafford.FiniteLength.finite_bad_of_split_central_pencil_spectrum
#print axioms
  SymplecticStafford.FiniteLength.finite_bad_of_finite_central_division_pencil_spectrum
