module

public import Mathlib.Algebra.Algebra.Opposite
public import SymplecticStafford.Filtered.M01StructuralClass

@[expose] public section

/-!
# Opposite of a concrete filtered algebra

The terminal Stafford package is two-sided, so the filtered source class must
be transported to the opposite ring before the left/right endpoint is used.
This file performs that transport on the actual additive-subgroup filtration
and the actual central degree-zero algebra map.  It does not transport any
source theorem or same-divisor certificate.
-/

namespace SymplecticStafford.Filtered

universe u v

open MulOpposite

section Filtration

variable {R : Type u} [Ring R]

/-- Transport an additive filtration across `R ≃+ Rᵐᵒᵖ`.  The reversal of
multiplication is harmless because the filtration degree addition is
commutative. -/
def AdditiveFilteredRingData.opposite
    (F : AdditiveFilteredRingData R) :
    AdditiveFilteredRingData Rᵐᵒᵖ where
  carrier n :=
    { carrier := {x | unop x ∈ F.carrier n}
      zero_mem' := by simpa using F.zero_mem n
      add_mem' := by
        intro x y hx hy
        change unop x + unop y ∈ F.carrier n
        rw [← unop_add]
        exact (F.carrier n).add_mem hx hy
      neg_mem' := by
        intro x hx
        change -unop x ∈ F.carrier n
        rw [← unop_neg]
        exact (F.carrier n).neg_mem hx }
  one_mem := by
    change unop (op (1 : R)) ∈ F.carrier 0
    simpa using F.one_mem
  mul_mem := by
    intro i j a b ha hb
    change unop (a * b) ∈ F.carrier (i + j)
    rw [unop_mul]
    have hba : unop b * unop a ∈ F.carrier (j + i) :=
      F.mul_mem hb ha
    simpa [Nat.add_comm] using hba
  monotone := by
    intro i j hij x hx
    change unop x ∈ F.carrier j
    exact F.monotone hij hx
  exhaustive := by
    intro x
    obtain ⟨n, hn⟩ := F.exhaustive (unop x)
    exact ⟨n, hn⟩

@[simp] theorem opposite_mem_iff
    (F : AdditiveFilteredRingData R) (n : ℕ) (x : Rᵐᵒᵖ) :
    x ∈ (F.opposite.carrier n) ↔ unop x ∈ F.carrier n := Iff.rfl

theorem opposite_opposite_mem
    (F : AdditiveFilteredRingData R) (n : ℕ)
    (x : Rᵐᵒᵖᵐᵒᵖ) :
    x ∈ F.opposite.opposite.carrier n ↔
      unop (unop x) ∈ F.carrier n := Iff.rfl

end Filtration

section Algebra

variable {K : Type v} {R : Type u}
variable [Field K] [Ring R] [Nontrivial R] [Algebra K R]

/-- The concrete M01 filtered-algebra package is preserved by opposite. -/
def M01FilteredAlgebra.opposite
    (A : M01FilteredAlgebra K R) :
    M01FilteredAlgebra K Rᵐᵒᵖ where
  filtration := A.filtration.opposite
  central := by
    intro k a
    apply unop_injective
    simpa only [unop_mul, MulOpposite.algebraMap_apply, unop_op] using
      (A.central k (unop a)).symm
  degree_zero := by
    ext a
    constructor
    · intro ha
      change unop a ∈ A.filtration.carrier 0 at ha
      have ha' : unop a ∈ (A.filtration.carrier 0 : Set R) := ha
      rw [A.degree_zero] at ha'
      obtain ⟨k, hk⟩ := ha'
      refine ⟨k, ?_⟩
      simpa [MulOpposite.algebraMap_apply] using congrArg op hk
    · intro ha
      obtain ⟨k, hk⟩ := ha
      change unop a ∈ (A.filtration.carrier 0 : Set R)
      rw [A.degree_zero]
      refine ⟨k, ?_⟩
      simpa [MulOpposite.algebraMap_apply] using
        congrArg unop hk

@[simp] theorem M01FilteredAlgebra.opposite_filtration_carrier
    (A : M01FilteredAlgebra K R) (n : ℕ) (a : Rᵐᵒᵖ) :
    a ∈ (A.opposite.filtration.carrier n) ↔
      unop a ∈ A.filtration.carrier n := Iff.rfl

end Algebra

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.AdditiveFilteredRingData.opposite
#print axioms SymplecticStafford.Filtered.M01FilteredAlgebra.opposite
