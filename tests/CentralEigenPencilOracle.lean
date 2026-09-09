import SymplecticStafford.FiniteLength.CentralEigenPencil

/-!
# Independent oracle for the central eigenvalue pencil

This is a concrete two-dimensional test over `ℚ`: the endomorphism sends
`(u,v)` to `(0,v)`, so `(1,0)` and `(0,1)` are eigenvectors for the distinct
central eigenvalues `0` and `1`.  The oracle checks the division-ring-only
linear-independence theorem without any finite-dimensionality over an
auxiliary scalar field or any determinant argument.
-/

namespace SymplecticStafford.FiniteLength.CentralEigenPencilOracle

def diagonal : Module.End ℚ (ℚ × ℚ) :=
  { toFun := fun p => (0, p.2)
    map_add' := by
      intro p q
      ext <;> simp
    map_smul' := by
      intro a p
      ext <;> simp }

def eigenvector : ℚ → (ℚ × ℚ) := fun z =>
  if z = 0 then (1, 0) else if z = 1 then (0, 1) else 0

def scalarEmbedding : ℚ →+* ℚ := RingHom.id ℚ

theorem central : ∀ k : ℚ, ∀ a : ℚ, scalarEmbedding k * a = a * scalarEmbedding k := by
  intro k a
  exact mul_comm _ _

theorem concrete_two_eigenvectors_independent :
    LinearIndepOn ℚ eigenvector
      (↑([0, 1] : List ℚ).toFinset : Set ℚ) := by
  apply central_eigenvectors_linearIndependent_list
    (ι := scalarEmbedding) (hι := central) diagonal [0, 1] eigenvector
  · norm_num
  · intro k hk
    simp only [List.mem_cons, List.mem_singleton] at hk
    rcases hk with h0 | h1
    · simpa [h0, eigenvector]
    · have h1' : k = 1 := by simpa using h1
      simpa [h1', eigenvector]
  · intro k hk
    simp only [List.mem_cons, List.mem_singleton] at hk
    rcases hk with h0 | h1
    · simpa [h0, diagonal, eigenvector, scalarEmbedding]
    · have h1' : k = 1 := by simpa using h1
      simpa [h1', diagonal, eigenvector, scalarEmbedding]

example : eigenvector 0 ≠ 0 := by simp [eigenvector]

example : eigenvector 1 ≠ 0 := by simp [eigenvector]

end SymplecticStafford.FiniteLength.CentralEigenPencilOracle

#print axioms SymplecticStafford.FiniteLength.CentralEigenPencilOracle.diagonal
#print axioms SymplecticStafford.FiniteLength.CentralEigenPencilOracle.eigenvector
#print axioms SymplecticStafford.FiniteLength.CentralEigenPencilOracle.concrete_two_eigenvectors_independent
