module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import SymplecticStafford.Filtered.AssociatedLayerRing

@[expose] public section

/-!
# A concrete central-field filtered-algebra boundary

`AdmissibleSymplecticClass` records paper-level structural labels, but it does
not yet expose an actual filtration or identify its degree-zero piece.  This
module supplies that missing M01 interface without asserting any Ore,
Noetherian, support, or same-divisor conclusion.

The filtration is the repaired submodule-valued interface from
`RingFiltrationBridge`.  The degree-zero equality is literal equality of
subsets with the image of a specified scalar field, and centrality is stated
for the actual algebra map.  Consequently downstream code can use scalar
coefficients in the original ring while retaining the original factor order.
The separatedness theorem below is the least-degree associated-layer
detection already available from exhaustiveness, now exposed through this
concrete package.
-/

namespace SymplecticStafford.Filtered

universe u v

open SymplecticStafford

section

variable (K : Type v) (R : Type u)
variable [Field K] [Ring R] [Nontrivial R] [Algebra K R]

/-- Concrete structural data for a filtered algebra over a central field.

The first three fields are the exact algebraic content needed by the M01
degree-zero bridge.  The filtration already includes nonnegative degree
bounds, multiplicativity, monotonicity, and exhaustiveness.  No paper-level
geometric or source-producing assertion is hidden in this record.
-/
structure CentralFieldFilteredAlgebra where
  filtration : RingFiltrationData (R := R)
  central : ∀ (k : K) (a : R),
    algebraMap K R k * a = a * algebraMap K R k
  degree_zero :
    (filtration.carrier 0 : Set R) = Set.range (algebraMap K R)

namespace CentralFieldFilteredAlgebra

variable (A : CentralFieldFilteredAlgebra K R)

/-- The scalar map is faithful because the target ring is nontrivial. -/
theorem algebraMap_injective :
    Function.Injective (algebraMap K R) := by
  intro x y hxy
  by_contra hxy'
  have hz : algebraMap K R (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcancel : (x - y)⁻¹ * (x - y) = (1 : K) :=
    inv_mul_cancel₀ (sub_ne_zero.mpr hxy')
  have hbad : (0 : R) = 1 := by
    have hmap := congrArg (algebraMap K R) hcancel
    simpa [map_mul, hz] using hmap
  exact zero_ne_one hbad

theorem mem_degree_zero_iff (a : R) :
    a ∈ A.filtration.carrier 0 ↔ ∃ k : K, a = algebraMap K R k := by
  change a ∈ (A.filtration.carrier 0 : Set R) ↔
    ∃ k : K, a = algebraMap K R k
  rw [A.degree_zero]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- Both left and right multiplication by a scalar stay in the same layer. -/
theorem scalar_mem_same_layer {n : ℕ} (k : K) {a : R}
    (ha : a ∈ A.filtration.carrier n) :
    algebraMap K R k * a ∈ A.filtration.carrier n ∧
      a * algebraMap K R k ∈ A.filtration.carrier n := by
  have hk : algebraMap K R k ∈ A.filtration.carrier 0 := by
    exact (mem_degree_zero_iff (K := K) (R := R) A
      (algebraMap K R k)).mpr ⟨k, rfl⟩
  have hleft := A.filtration.mul_mem hk ha
  have hright := A.filtration.mul_mem ha hk
  exact ⟨by simpa using hleft, by simpa using hright⟩

theorem scalar_left_eq_right (A : CentralFieldFilteredAlgebra K R)
    (k : K) (a : R) :
    algebraMap K R k * a = a * algebraMap K R k :=
  CentralFieldFilteredAlgebra.central A k a

/-- Every nonzero element has a nonzero class in its least occupied layer. -/
theorem separated_detection {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ hna : a ∈ A.filtration.carrier n,
      RingFiltrationData.associatedClass A.filtration n a hna ≠ 0 :=
  RingFiltrationData.exists_associatedClass_ne_zero_of_ne_zero A.filtration ha

end CentralFieldFilteredAlgebra

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.algebraMap_injective
#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.scalar_mem_same_layer
#print axioms SymplecticStafford.Filtered.CentralFieldFilteredAlgebra.separated_detection
