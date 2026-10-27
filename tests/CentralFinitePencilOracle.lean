module

public import SymplecticStafford.FiniteLength.CentralFinitePencil
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Non-vacuous oracle for split central-field pencils

The one-dimensional pencil `1 + z` has exactly one bad parameter, `z = -1`.
The oracle instantiates the positive theorem and proves its realization and
split retraction directly, independently of the determinant implementation.
-/

namespace SymplecticStafford.FiniteLength.CentralFinitePencilOracle

open SymplecticStafford.FiniteLength

example : Set.Finite ({z : ℚ | ¬ LinearIndependent ℚ
    (fun _ : Unit => (1 + z : ℚ))} : Set ℚ) := by
  have hbad_eq : ({z : ℚ | ¬ LinearIndependent ℚ
      (fun _ : Unit => (1 + z : ℚ))} : Set ℚ) = {-1} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [linearIndependent_unique_iff]
    simp only [not_ne_iff]
    change (1 + z = 0) ↔ z = -1
    constructor <;> intro h <;> linarith
  have hfinite : Set.Finite ({z : ℚ | ¬ LinearIndependent ℚ
      (fun _ : Unit => (1 + z : ℚ))} : Set ℚ) := by
    apply finite_bad_of_split_central_pencil
      (K := ℚ) (E := ℚ) (V := ℚ) (P := ℚ)
      (block := fun z (_ : Unit) => (1 + z : ℚ))
      (base := LinearMap.id) (direction := LinearMap.id)
      (retract := LinearMap.id)
    · simp
    · intro z
      rw [linearIndependent_unique_iff]
      constructor
      · intro h
        intro x y hxy
        have hxy' : (1 + z) * x = (1 + z) * y := by
          change x + z * x = y + z * y at hxy
          calc
            (1 + z) * x = x + z * x := by ring
            _ = y + z * y := hxy
            _ = (1 + z) * y := by ring
        exact mul_left_cancel₀ h hxy'
      · intro h
        intro hz
        have hzeroone : (0 : ℚ) = 1 := h (by simp [hz])
        exact zero_ne_one hzeroone
  exact hfinite

end SymplecticStafford.FiniteLength.CentralFinitePencilOracle

#print axioms SymplecticStafford.FiniteLength.finite_bad_of_split_central_pencil
