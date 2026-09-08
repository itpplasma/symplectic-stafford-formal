import SymplecticStafford.FiniteLength.MatrixPencil
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-! The oracle uses two explicit 2-by-2 repeated blocks over `ℚ`, with
nontrivial off-diagonal pencil terms.  It checks determinant-polynomial
avoidance and does not instantiate any noncommutative or finite-length claim. -/

namespace SymplecticStafford.FiniteLength

abbrev K := ℚ
abbrev I := Fin 2
abbrev Block := Matrix I I K

def A₀ : Block := !![1, 0; 0, 1]
def C₀ : Block := !![0, 1; 1, 0]
def A₁ : Block := !![2, 0; 0, 1]
def C₁ : Block := !![1, 1; 0, 1]

example : MatrixTopGenerator A₀ := by
  apply (matrix_top_generator_iff _).2
  norm_num [A₀]

example : ¬ MatrixTopGenerator (!![1, 0; 0, 0] : Block) := by
  intro h
  apply (matrix_top_generator_iff _).1 h
  norm_num

example : Matrix.det A₀ ≠ 0 := by
  norm_num [A₀]

example : Matrix.det A₁ ≠ 0 := by
  norm_num [A₁]

example (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ k : K, k ∉ forbidden ∧
      Matrix.det (A₀ + k • C₀) ≠ 0 ∧
      Matrix.det (A₁ + k • C₁) ≠ 0 := by
  obtain ⟨k, hk, hblocks⟩ :=
    exists_simultaneous_matrix_pencil_avoiding
      (J := Fin 2)
      (fun j => if j = 0 then A₀ else A₁)
      (fun j => if j = 0 then C₀ else C₁)
      (by
        intro j
        fin_cases j <;> simp [A₀, A₁])
      forbidden hforbidden
  refine ⟨k, hk, ?_, ?_⟩
  · simpa using hblocks 0
  · simpa using hblocks 1

end SymplecticStafford.FiniteLength
