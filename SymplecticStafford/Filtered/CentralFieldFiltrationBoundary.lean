import SymplecticStafford.Filtered.CentralField

/-!
# Boundary in the current central-field filtration interface

`RingFiltrationData` makes every layer a right submodule over the whole ring,
whereas the degree-zero layer of a filtered algebra is intended to be the
central scalar field.  The two requirements force the scalar map to be
surjective: multiply the degree-zero element `1` on the right by an arbitrary
ring element.  Thus this interface cannot represent an infinite-dimensional
filtered algebra over a proper central field.
-/

namespace SymplecticStafford.Filtered

universe u v

open SymplecticStafford

variable {K : Type v} {R : Type u}
variable [Field K] [Ring R] [Nontrivial R] [Algebra K R]

theorem CentralFieldFilteredAlgebra.algebraMap_surjective
    (A : CentralFieldFilteredAlgebra K R) :
    Function.Surjective (algebraMap K R) := by
  intro a
  have ha0 : a ∈ A.filtration.carrier 0 := by
    have hmul := (A.filtration.carrier 0).smul_mem
      (MulOpposite.op a) A.filtration.one_mem
    simpa using hmul
  rcases (CentralFieldFilteredAlgebra.mem_degree_zero_iff
    (K := K) (R := R) A a).mp ha0 with ⟨k, hk⟩
  exact ⟨k, hk.symm⟩

theorem CentralFieldFilteredAlgebra.degree_zero_forces_top
    (A : CentralFieldFilteredAlgebra K R) :
    (A.filtration.carrier 0 : Set R) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  have ha0 : a ∈ A.filtration.carrier 0 := by
    have hmul := (A.filtration.carrier 0).smul_mem
      (MulOpposite.op a) A.filtration.one_mem
    simpa using hmul
  exact ha0

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.algebraMap_surjective
#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.degree_zero_forces_top
