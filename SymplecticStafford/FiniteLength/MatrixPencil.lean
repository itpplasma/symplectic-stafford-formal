import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Algebra.Polynomial.Roots

/-!
# Central-field matrix blocks

For a repeated simple factor, a finite semisimple block is represented here
by a square matrix over the central coefficient field.  Its determinant is a
polynomial in the pencil parameter, so finitely many matrix-block failures can
be avoided simultaneously.  This is a genuine matrix-block result, but its
scope is deliberately explicit: it does not construct simple factors,
division-ring coordinates, a radical, or a finite-length quotient.

All matrix products remain matrix products; this file makes no claim that an
ambient noncommutative algebra can be replaced by these central matrices.
-/

namespace SymplecticStafford.FiniteLength

section MatrixBlocks

variable {K : Type*} [Field K] [Infinite K]
variable {r : Nat}

/-! A matrix block is a repeated simple factor at the level of its regular
right module.  We keep the multiplication order explicit: the generator is
on the left and its coefficient is on the right. -/

/-- Right generation of a square matrix block by one matrix. -/
def MatrixTopGenerator (x : Matrix (Fin r) (Fin r) K) : Prop :=
  ∀ y : Matrix (Fin r) (Fin r) K, ∃ z, x * z = y

/-- A matrix block right-generates its full matrix ring exactly when it is
invertible, equivalently when its determinant is nonzero. -/
theorem matrix_top_generator_iff (x : Matrix (Fin r) (Fin r) K) :
    MatrixTopGenerator x ↔ Matrix.det x ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := hx 1
    exact Matrix.det_ne_zero_of_right_inverse hz
  · intro hx y
    have hunit : IsUnit (Matrix.det x) := (isUnit_iff_ne_zero).2 hx
    refine ⟨x⁻¹ * y, ?_⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv x hunit, one_mul]

/-- The determinant polynomial attached to a central-field matrix pencil. -/
noncomputable def matrixPencilPolynomial
    (A C : Matrix (Fin r) (Fin r) K) : Polynomial K :=
  Matrix.det
    (A.map Polynomial.C +
      (Polynomial.X : Polynomial K) • C.map Polynomial.C)

theorem matrixPencilPolynomial_eval
    (A C : Matrix (Fin r) (Fin r) K) (k : K) :
    (matrixPencilPolynomial A C).eval k =
      Matrix.det (A + k • C) := by
  rw [matrixPencilPolynomial, eval_det]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- A non-singular initial block has only finitely many singular members in a
central scalar pencil. -/
theorem finite_matrix_pencil_exceptions
    (A C : Matrix (Fin r) (Fin r) K) (hA : Matrix.det A ≠ 0) :
    Set.Finite {k : K | Matrix.det (A + k • C) = 0} := by
  let p : Polynomial K := matrixPencilPolynomial A C
  have hp : p ≠ 0 := by
    intro hp0
    apply hA
    have he := congrArg (fun q : Polynomial K => q.eval 0) hp0
    simpa [p, matrixPencilPolynomial_eval] using he
  apply Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hp)
  intro k hk
  exact (Polynomial.IsRoot.def.2 (by
    simpa [p, matrixPencilPolynomial_eval] using hk))

/-- A finite family of repeated matrix blocks admits one scalar avoiding all
singular blocks and an arbitrary finite forbidden set. -/
theorem exists_simultaneous_matrix_pencil_avoiding
    {J : Type*} [Fintype J] [DecidableEq J]
    (A C : J → Matrix (Fin r) (Fin r) K)
    (hA : ∀ j, Matrix.det (A j) ≠ 0)
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ k : K, k ∉ forbidden ∧
      ∀ j, Matrix.det (A j + k • C j) ≠ 0 := by
  classical
  let bad : J → Set K := fun j =>
    {k : K | Matrix.det (A j + k • C j) = 0}
  have hbad : (⋃ j : J, bad j).Finite := by
    apply Set.finite_iUnion
    intro j
    exact finite_matrix_pencil_exceptions (A j) (C j) (hA j)
  have hall : (forbidden ∪ ⋃ j : J, bad j).Finite :=
    hforbidden.union hbad
  obtain ⟨k, hk⟩ := (Set.infinite_univ.sdiff hall).nonempty
  refine ⟨k, ?_, ?_⟩
  · intro h
    exact hk.2 (Or.inl h)
  · intro j hzero
    apply hk.2
    right
    exact Set.mem_iUnion.2 ⟨j, hzero⟩

/-- The determinant-avoidance result in the generation language needed by a
finite repeated-block top. -/
theorem exists_simultaneous_matrix_top_generator_avoiding
    {J : Type*} [Fintype J] [DecidableEq J]
    (A C : J → Matrix (Fin r) (Fin r) K)
    (hA : ∀ j, Matrix.det (A j) ≠ 0)
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ k : K, k ∉ forbidden ∧
      ∀ j, MatrixTopGenerator (A j + k • C j) := by
  obtain ⟨k, hk, hdet⟩ := exists_simultaneous_matrix_pencil_avoiding
    A C hA forbidden hforbidden
  refine ⟨k, hk, ?_⟩
  intro j
  exact (matrix_top_generator_iff _).2 (hdet j)

end MatrixBlocks

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.matrixPencilPolynomial_eval
#print axioms SymplecticStafford.FiniteLength.finite_matrix_pencil_exceptions
#print axioms SymplecticStafford.FiniteLength.exists_simultaneous_matrix_pencil_avoiding
#print axioms SymplecticStafford.FiniteLength.matrix_top_generator_iff
#print axioms SymplecticStafford.FiniteLength.exists_simultaneous_matrix_top_generator_avoiding
