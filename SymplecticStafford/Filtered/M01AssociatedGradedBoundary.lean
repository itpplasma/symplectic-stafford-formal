module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic
public import SymplecticStafford.Filtered.AssociatedLayerRing

@[expose] public section

/-!
# M01 obstruction: filtered multiplication does not imply a commutative graded ring

`RingFiltrationData` is now an actual submodule-valued, exhaustive,
multiplicative filtration.  Those fields still do not imply that its
associated layers are commutative (nor affine or a domain).  The constant
filtration on `2 × 2` rational matrices is a minimal counterexample: all
filtered products remain in the top layer, while the layer-zero product
retains the noncommutativity of the original ring.

Thus the paper's commutative affine-domain associated graded hypothesis must be
an actual construction/identification, not a conclusion read off from the
filtered carrier fields.
-/

namespace SymplecticStafford.Filtered

open SymplecticStafford
open RingFiltrationData

abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℚ

/-- The constant top filtration satisfies every current concrete ring
    filtration field. -/
def constantMatrixFiltration : RingFiltrationData (R := MatrixRing) where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by intro i j a b ha hb; simp
  monotone := by intro i j hij x hx; simp
  exhaustive := by intro a; exact ⟨0, by simp⟩

def matrixE01 : MatrixRing := !![0, 1; 0, 0]
def matrixE10 : MatrixRing := !![0, 0; 1, 0]

theorem matrixE01_mem_zero : matrixE01 ∈ constantMatrixFiltration.carrier 0 := by
  simp [constantMatrixFiltration]

theorem matrixE10_mem_zero : matrixE10 ∈ constantMatrixFiltration.carrier 0 := by
  simp [constantMatrixFiltration]

theorem matrixE01_mul_E10_mem_zero :
    matrixE01 * matrixE10 ∈ constantMatrixFiltration.carrier 0 := by
  simp [constantMatrixFiltration]

theorem matrixE10_mul_E01_mem_zero :
    matrixE10 * matrixE01 ∈ constantMatrixFiltration.carrier 0 := by
  simp [constantMatrixFiltration]

theorem matrixE01_mul_E10_ne_E10_mul_E01 :
    matrixE01 * matrixE10 ≠ matrixE10 * matrixE01 := by
  intro h
  have hentry := congrArg (fun X : MatrixRing => X 0 0) h
  norm_num [matrixE01, matrixE10, Matrix.mul_apply, Fin.sum_univ_succ] at hentry

theorem constantMatrixFiltration_is_not_commutative :
    ¬ (∀ (a b : MatrixRing), a * b = b * a) := by
  intro h
  exact matrixE01_mul_E10_ne_E10_mul_E01 (h matrixE01 matrixE10)

/- The associated layer at degree zero is an actual quotient with the product
   supplied by `AssociatedLayerRing`; the filtration fields alone provide no
   commutativity theorem for that product. -/
theorem associatedLayerRing_commutativity_is_not_a_filtration_consequence :
    ¬ (∀ (a b : MatrixRing), a * b = b * a) :=
  constantMatrixFiltration_is_not_commutative

def matrixE01Class : associatedLayer constantMatrixFiltration 0 :=
  associatedClass constantMatrixFiltration 0 matrixE01 matrixE01_mem_zero

def matrixE10Class : associatedLayer constantMatrixFiltration 0 :=
  associatedClass constantMatrixFiltration 0 matrixE10 matrixE10_mem_zero

theorem associatedLayerMul_matrixE01_E10_ne_E10_E01 :
    associatedLayerMul constantMatrixFiltration 0 0
        matrixE01Class matrixE10Class ≠
      associatedLayerMul constantMatrixFiltration 0 0
        matrixE10Class matrixE01Class := by
  intro h
  have hclass :
      associatedClass constantMatrixFiltration 0 (matrixE01 * matrixE10)
          matrixE01_mul_E10_mem_zero =
        associatedClass constantMatrixFiltration 0 (matrixE10 * matrixE01)
          matrixE10_mul_E01_mem_zero := by
    change associatedLayerMul constantMatrixFiltration 0 0
        (Submodule.Quotient.mk ⟨matrixE01, matrixE01_mem_zero⟩)
        (Submodule.Quotient.mk ⟨matrixE10, matrixE10_mem_zero⟩) =
      associatedLayerMul constantMatrixFiltration 0 0
        (Submodule.Quotient.mk ⟨matrixE10, matrixE10_mem_zero⟩)
        (Submodule.Quotient.mk ⟨matrixE01, matrixE01_mem_zero⟩) at h
    rw [associatedLayerMul_mk_mk, associatedLayerMul_mk_mk] at h
    exact h
  have hrel := (Submodule.Quotient.eq (layerSubmodule constantMatrixFiltration 0)).mp hclass
  have hentry := congrArg (fun X : MatrixRing => X 0 0) hrel
  norm_num [constantMatrixFiltration, matrixE01, matrixE10,
    Matrix.mul_apply, Fin.sum_univ_succ] at hentry

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.constantMatrixFiltration_is_not_commutative
#print axioms SymplecticStafford.Filtered.associatedLayerRing_commutativity_is_not_a_filtration_consequence
#print axioms SymplecticStafford.Filtered.associatedLayerMul_matrixE01_E10_ne_E10_E01
