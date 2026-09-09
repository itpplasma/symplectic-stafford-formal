import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Boundary for an unstructured finite-length activated pencil

Finite generation (or finite dimension) and generation at the initial
parameter do not by themselves make the exceptional parameter set finite.
The following two-dimensional example over `ℚ` is deliberately not an
affine central pencil: it is the exact boundary showing why the M07
noncommutative theorem must retain an affine/central-action hypothesis (or a
separate finite independent-witness certificate).

At `z = 0` the two vectors are the standard basis.  At every other scalar
both vectors are zero, so the bad set is `ℚ \\ {0}`, which is infinite.  This
does not contradict `Pencil.lean` or `CentralEigenPencil.lean`: those files
prove finiteness only after the scalar action and its centrality/injectivity
have been supplied.
-/

namespace SymplecticStafford.FiniteLength

/-! A finite repeated block with no affine/central-pencil structure attached. -/
def unstructuredPencil (z : ℚ) : Fin 2 → (Fin 2 → ℚ) :=
  if z = 0 then fun i => Pi.single i 1 else fun _ => 0

theorem unstructuredPencil_zero_independent :
    LinearIndependent ℚ (unstructuredPencil 0) := by
  rw [show unstructuredPencil 0 =
      (Pi.basisFun ℚ (Fin 2) : Fin 2 → (Fin 2 → ℚ)) by
    funext i
    simp [unstructuredPencil, Pi.basisFun_apply]]
  exact Module.Basis.linearIndependent (Pi.basisFun ℚ (Fin 2))

theorem unstructuredPencil_nonzero_not_independent {z : ℚ} (hz : z ≠ 0) :
    ¬ LinearIndependent ℚ (unstructuredPencil z) := by
  rw [unstructuredPencil, if_neg hz]
  intro h
  exact h.ne_zero 0 (by simp)

def unstructuredPencilBad : Set ℚ :=
  {z | ¬ LinearIndependent ℚ (unstructuredPencil z)}

theorem unstructuredPencilBad_eq_compl_zero :
    unstructuredPencilBad = ({0} : Set ℚ)ᶜ := by
  ext z
  by_cases hz : z = 0
  · simp [unstructuredPencilBad, hz, unstructuredPencil_zero_independent]
  · simp [unstructuredPencilBad, hz, unstructuredPencil_nonzero_not_independent hz]

theorem unstructuredPencilBad_not_finite :
    ¬ unstructuredPencilBad.Finite := by
  rw [unstructuredPencilBad_eq_compl_zero, Set.not_finite]
  apply (Set.infinite_univ.diff (Set.finite_singleton (0 : ℚ))).mono
  intro z hz
  exact hz.2

/-! The advertised boundary in one conjunction, useful for downstream audits. -/
theorem finite_dimension_and_initial_generation_not_enough :
    LinearIndependent ℚ (unstructuredPencil 0) ∧
      ¬ unstructuredPencilBad.Finite :=
  ⟨unstructuredPencil_zero_independent, unstructuredPencilBad_not_finite⟩

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.finite_dimension_and_initial_generation_not_enough
