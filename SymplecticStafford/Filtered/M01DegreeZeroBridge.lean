module

public import SymplecticStafford.Filtered.CentralField

@[expose] public section

/-!
# Actual M01 degree-zero bridge

For an actual `CentralFieldFilteredAlgebra`, the degree-zero filtration layer
is the scalar-field image.  Since its predecessor is bottom, its associated
quotient is additively equivalent to the scalar field.  This is a genuine
kernel-checked bridge: it uses the actual filtration and algebra map, not a
proposition-valued label or a supplied graded-ring identification.

The construction stops at degree zero.  It does not assert that all
associated layers assemble into a commutative affine-domain graded ring.
-/

namespace SymplecticStafford.Filtered

universe u v

open SymplecticStafford
open RingFiltrationData

variable {K : Type v} {R : Type u}
variable [Field K] [Ring R] [Nontrivial R] [Algebra K R]

namespace CentralFieldFilteredAlgebra

variable (A : CentralFieldFilteredAlgebra K R)

theorem degreeZeroMem (k : K) :
    algebraMap K R k ∈ A.filtration.carrier 0 :=
  (mem_degree_zero_iff (K := K) (R := R) A (algebraMap K R k)).mpr
    ⟨k, rfl⟩

/-- The scalar class in the actual degree-zero associated quotient. -/
def degreeZeroClass (k : K) : associatedLayer A.filtration 0 :=
  associatedClass A.filtration 0 (algebraMap K R k) (A.degreeZeroMem k)

def degreeZeroMap : K →+ associatedLayer A.filtration 0 where
  toFun := degreeZeroClass A
  map_zero' := by
    apply (Submodule.Quotient.eq (layerSubmodule A.filtration 0)).mpr
    simp [layerSubmodule, predecessor]
  map_add' := by
    intro x y
    apply (Submodule.Quotient.eq (layerSubmodule A.filtration 0)).mpr
    simp [layerSubmodule, predecessor, map_add]

theorem degreeZeroMap_injective :
    Function.Injective (degreeZeroMap A) := by
  intro x y h
  have hrel := (Submodule.Quotient.eq
    (layerSubmodule A.filtration 0)).mp h
  change algebraMap K R x - algebraMap K R y ∈ predecessor A.filtration 0 at hrel
  have hzero : algebraMap K R x - algebraMap K R y = 0 := by
    simpa [predecessor] using hrel
  apply algebraMap_injective K R
  exact sub_eq_zero.mp hzero

theorem degreeZeroMap_surjective :
    Function.Surjective (degreeZeroMap A) := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rcases (mem_degree_zero_iff (K := K) (R := R) A (x : R)).mp
      x.property with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply (Submodule.Quotient.eq (layerSubmodule A.filtration 0)).mpr
  change algebraMap K R k - (x : R) ∈ predecessor A.filtration 0
  rw [hk]
  simp [predecessor]

/-- The actual degree-zero associated quotient is additively equivalent to K. -/
noncomputable def degreeZeroEquiv :
    K ≃+ associatedLayer A.filtration 0 :=
  AddEquiv.ofBijective (degreeZeroMap A)
    ⟨degreeZeroMap_injective A, degreeZeroMap_surjective A⟩

@[simp] theorem degreeZeroEquiv_apply (k : K) :
    degreeZeroEquiv A k = degreeZeroClass A k := rfl

theorem degreeZeroClass_ne_zero {k : K} (hk : k ≠ 0) :
    degreeZeroClass A k ≠ 0 := by
  intro h
  have hmap : degreeZeroMap A k = 0 := by
    change degreeZeroClass A k = 0
    exact h
  have : k = 0 := (degreeZeroMap_injective A) (by
    simpa using hmap)
  exact hk this

end CentralFieldFilteredAlgebra

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.degreeZeroMap_injective
#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.degreeZeroMap_surjective
#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.degreeZeroEquiv
