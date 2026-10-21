module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# A strict filtered-chain boundary

Finite length in a graded category does not, by itself, bound chains of
ungraded submodules when the filtration is unbounded below.  The example
below is deliberately a module-level filtration model: it isolates the
strictness implication needed before a `G_{Sigma_p}` graded-length bound can
be transferred to the filtered `T_p` module.  It does not assert that the
actual `T_p` filtration has this pathology.

Take finitely supported Laurent-coordinate vectors indexed by `ℤ`, and put
the usual upper-degree filtration on them.  The sum-zero submodule is proper,
but every filtered layer of the ambient module has a representative in that
submodule: subtract the total sum in the immediately lower coordinate.  Thus
the inclusion is strict while its induced map on every associated layer is
surjective.  A proof of the paper's repair must add hypotheses (for example a
Zariskian strictness theorem) which rule out this model.
-/

namespace SymplecticStafford.FiniteLength

abbrev LaurentVector := ℤ →₀ ℚ

noncomputable def totalLinear : LaurentVector →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun _ : ℤ => (1 : ℚ))

@[simp] theorem totalLinear_single (i : ℤ) (c : ℚ) :
    totalLinear (Finsupp.single i c) = c := by
  simp [totalLinear]

/-- Vectors supported in degrees at most `n`. -/
def upperFiltration (n : ℤ) : Submodule ℚ LaurentVector where
  carrier := {v | ∀ i, n < i → v i = 0}
  zero_mem' := by
    intro i hi
    simp
  add_mem' := by
    intro v w hv hw i hi
    simp only [Finsupp.add_apply]
    rw [hv i hi, hw i hi, add_zero]
  smul_mem' := by
    intro c v hv i hi
    simp only [Finsupp.smul_apply]
    rw [hv i hi, smul_zero]

@[simp] theorem mem_upperFiltration_iff (n : ℤ) (v : LaurentVector) :
    v ∈ upperFiltration n ↔ ∀ i, n < i → v i = 0 := Iff.rfl

/- The total-sum kernel supplies a proper submodule invisible on every layer. -/
noncomputable def sumZero : Submodule ℚ LaurentVector := totalLinear.ker

@[simp] theorem mem_sumZero_iff (v : LaurentVector) :
    v ∈ sumZero ↔ totalLinear v = 0 := Iff.rfl

theorem sumZero_ne_top : sumZero ≠ (⊤ : Submodule ℚ LaurentVector) := by
  intro h
  have hm : Finsupp.single (0 : ℤ) (1 : ℚ) ∈ sumZero := by
    rw [h]
    trivial
  have ht : totalLinear (Finsupp.single (0 : ℤ) (1 : ℚ)) = 0 := hm
  simpa using ht

theorem sumZero_nontrivial : sumZero ≠ (⊥ : Submodule ℚ LaurentVector) := by
  intro h
  have hz : Finsupp.single (0 : ℤ) (1 : ℚ) -
      Finsupp.single (1 : ℤ) (1 : ℚ) ∈ (⊥ : Submodule ℚ LaurentVector) := by
    have hz0 : Finsupp.single (0 : ℤ) (1 : ℚ) -
        Finsupp.single (1 : ℤ) (1 : ℚ) ∈ sumZero := by
      change totalLinear _ = 0
      simp [map_sub]
    exact h ▸ hz0
  have hz' : Finsupp.single (0 : ℤ) (1 : ℚ) -
      Finsupp.single (1 : ℤ) (1 : ℚ) = 0 := hz
  have hv := congrArg (fun f : LaurentVector => f 0) hz'
  norm_num at hv

/-!
`layerSurjective A` says that every class in the `n`th filtered quotient of
the ambient module has a representative in `A` with the induced filtration.
It is a direct, quotient-free spelling of surjectivity on associated layers.
-/
def layerSurjective (A : Submodule ℚ LaurentVector) : Prop :=
  ∀ n : ℤ, ∀ v ∈ upperFiltration n,
    ∃ w, w ∈ A ∧ w ∈ upperFiltration n ∧
      v - w ∈ upperFiltration (n - 1)

theorem sumZero_layerSurjective : layerSurjective sumZero := by
  intro n v hv
  let c : ℚ := totalLinear v
  let w : LaurentVector := v - c • Finsupp.single (n - 1) 1
  refine ⟨w, ?_, ?_, ?_⟩
  · change totalLinear w = 0
    dsimp [w, c]
    rw [map_sub, map_smul, totalLinear_single]
    ring
  · intro i hi
    dsimp [w]
    change v i - (c • Finsupp.single (n - 1) 1) i = 0
    rw [hv i hi]
    by_cases h : i = n - 1
    · subst i
      omega
    · simp [Finsupp.single_apply, h]
  · intro i hi
    dsimp [w]
    by_cases h : i = n - 1
    · subst i
      exact (lt_irrefl _ hi).elim
    · simp [Finsupp.single_apply, h]

theorem strict_inclusion_invisible :
    sumZero < (⊤ : Submodule ℚ LaurentVector) ∧
      layerSurjective sumZero := by
  exact ⟨lt_top_iff_ne_top.mpr sumZero_ne_top, sumZero_layerSurjective⟩

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.sumZero_layerSurjective
#print axioms SymplecticStafford.FiniteLength.strict_inclusion_invisible
