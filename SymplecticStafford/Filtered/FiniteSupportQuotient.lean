import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Quotient.Defs
import SymplecticStafford.Filtered.FiniteSupportDetection

/-!
# Finite support witnesses in actual module quotients

`FiniteSupportDetection` finds a maximal layer for a separated finite
descending filtration of sets.  This file supplies the module bridge needed
by the M04--M05 boundary: when the layers are genuine submodules, the
non-membership in the next layer is witnessed by a nonzero class under the
actual quotient map.  The filtration, exhaustiveness, and separatedness are
all explicit inputs.  No characteristic support, good filtration, Rees
localization, or minimal-prime construction is inferred here.
-/

namespace SymplecticStafford.Filtered

universe u v

section

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]

/-- A finite separated descending filtration by actual module subobjects. -/
structure FiniteFilteredModule where
  height : Nat
  carrier : Nat → Submodule R M
  exhaustive : carrier 0 = ⊤
  descending : ∀ k, carrier (k + 1) ≤ carrier k
  separated : carrier height = ⊥

namespace FiniteFilteredModule

variable (F : FiniteFilteredModule (R := R) (M := M))

/-- Forget the module structure and retain the finite layer membership data. -/
def toSetFiltration : FiniteDescendingFiltration M where
  height := F.height
  carrier := fun k => (F.carrier k : Set M)
  zero_mem := by
    intro k
    exact (F.carrier k).zero_mem
  exhaustive := by
    intro x
    rw [F.exhaustive]
    exact Set.mem_univ x
  descending := by
    intro k x hx
    exact F.descending k hx
  separated := by
    intro x hx
    rw [F.separated] at hx
    simpa using hx

theorem quotient_ne_zero_iff_not_mem (x : M) (k : Nat) :
    Submodule.mkQ (F.carrier (k + 1)) x ≠ 0 ↔
      x ∉ F.carrier (k + 1) := by
  constructor
  · intro hq hmem
    apply hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · intro hnot hzero
    apply hnot
    have hmk :
        (Submodule.Quotient.mk x : M ⧸ F.carrier (k + 1)) = 0 := by
      simpa only [Submodule.mkQ_apply] using hzero
    exact (Submodule.Quotient.mk_eq_zero (F.carrier (k + 1))).mp hmk

theorem exists_associatedTopQuotient_nonzero
    {x : M} (hx : x ≠ 0) :
    ∃ k, k < F.height ∧ x ∈ F.carrier k ∧
      Submodule.mkQ (F.carrier (k + 1)) x ≠ 0 := by
  rcases F.toSetFiltration.exists_detecting_layer hx with
    ⟨k, hk, hxk, hxnext⟩
  refine ⟨k, hk, hxk, ?_⟩
  exact (F.quotient_ne_zero_iff_not_mem x k).mpr hxnext

/-- The selected layer is nonzero as a quotient module. -/
theorem quotient_nontrivial_at_detecting_layer
    {x : M} (hx : x ≠ 0) :
    ∃ k, k < F.height ∧
      Submodule.mkQ (F.carrier (k + 1)) x ≠ 0 := by
  rcases F.exists_associatedTopQuotient_nonzero hx with
    ⟨k, hk, _, hq⟩
  exact ⟨k, hk, hq⟩

end FiniteFilteredModule

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.exists_associatedTopQuotient_nonzero
#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.quotient_ne_zero_iff_not_mem
#print axioms SymplecticStafford.Filtered.FiniteFilteredModule.quotient_nontrivial_at_detecting_layer
