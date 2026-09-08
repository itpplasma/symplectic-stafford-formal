import SymplecticStafford.FiniteLength.ActivatedFiniteLength
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Independent M07 finite-length oracle

The first example consumes the actual finite-length activated theorem with a
repeated 2-by-2 matrix top.  The top comparison and the radical-quotient
criterion are explicit hypotheses, while finite exceptional scalars are
proved from the determinant polynomial.  The second block checks genuinely
noncommuting matrix multiplication independently of the pencil calculation.
-/

namespace SymplecticStafford.FiniteLength.ActivatedFiniteLengthOracle

abbrev K := ℚ
abbrev J := Fin 2
abbrev Block := Matrix (Fin 2) (Fin 2) K

def matrixGenerator (x : J → Block) : Prop :=
  ∀ j, MatrixTopGenerator (x j)

section Consumer

variable {R M : Type*} [Ring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Module K M]

/-- The determinant-polynomial proof is supplied independently to the
finite-length consumer, rather than being hidden in its block interface. -/
example {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (top : M →+ (J → Block))
    (top_pencil : ∀ (z : K) (x y : M),
      top (x + z • y) = top x + z • top y)
    (quotient_criterion : ∀ m : M,
      matrixGenerator (top m) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : matrixGenerator (top v)) (forbidden : Set K)
    (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  let T : FiniteLengthTopData (R := R) (M := M) (K := K)
      (J := J) (B := fun _ : J => Block) :=
    { top := top
      generator := matrixGenerator
      finite_nongenerating := by
        intro x y hx
        have hdet : ∀ j, Matrix.det (top x j) ≠ 0 := by
          intro j
          exact (matrix_top_generator_iff _).mp (hx j)
        have hbad : (⋃ j : J, {z : K |
            Matrix.det (top x j + z • top y j) = 0}).Finite := by
          apply Set.finite_iUnion
          intro j
          exact finite_matrix_pencil_exceptions (top x j) (top y j) (hdet j)
        apply hbad.subset
        intro z hz
        by_contra hnot
        apply hz
        intro j
        apply (matrix_top_generator_iff _).2
        rw [top_pencil]
        intro hzero
        apply hnot
        exact Set.mem_iUnion.2 ⟨j, hzero⟩
      quotient_generator_iff := quotient_criterion }
  exact exists_activated_right_cyclic_of_finite_length_top
    F T rightAction rightAction_add central_smul_right v u e b l
    vL_zero e_decomp hv forbidden hforbidden

end Consumer

section NoncommutativeBlock

abbrev Small := Matrix (Fin 2) (Fin 2) (ZMod 2)

def E01 : Small := !![0, 1; 0, 0]
def E10 : Small := !![0, 0; 1, 0]

/- The order of the two matrix factors is observable in the finite ring. -/
example : E01 * E10 ≠ E10 * E01 := by decide

/- A singular noncommutative block is not a right generator, checked by its
finite multiplication table rather than by a commutative determinant. -/
example : ¬ ∀ y : Small, ∃ r : Small, E01 * r = y := by decide

end NoncommutativeBlock

end SymplecticStafford.FiniteLength.ActivatedFiniteLengthOracle
