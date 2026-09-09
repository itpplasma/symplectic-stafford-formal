import SymplecticStafford.Filtered.AssociatedGradedSpecBridge

/-!
# Conditional adapter from the structural M01 class to spectrum support

`M01FilteredAlgebra` carries the actual original-ring filtration.  The
commutative associated-graded ring/module and the quotient-to-module map are
still separate construction obligations.  This file packages those supplied
data and specializes the spectrum bridge to `U.filtration`, without adding a
claim that `gr U` has been constructed.
-/

namespace SymplecticStafford.Filtered

universe u v w z

section

variable {K : Type v} {R : Type u}
variable [Field K] [Ring R] [Nontrivial R] [Algebra K R]

variable (U : M01FilteredAlgebra K R)

section Adapter

variable (G : Type w) (N : Type z)
variable [CommRing G] [AddCommGroup N] [Module G N]

/-- Explicit associated-layer/spec data attached to a structural filtered
    algebra.  The associated ring `G` and module `N` are parameters rather
    than inferred constructions. -/
structure M01AssociatedSpecAdapter where
  bridge : AssociatedGradedSpecBridge U.filtration G N

namespace M01AssociatedSpecAdapter

variable (C : M01AssociatedSpecAdapter U G N)

theorem support_empty_iff_layer_killed :
    Module.support G N = ∅ ↔
      ∀ x : U.filtration.carrier C.bridge.layer,
        (x : R) ∈ AdditiveFilteredRingData.predecessor
          U.filtration C.bridge.layer :=
  AssociatedGradedSpecBridge.specSupport_empty_iff_layer_killed
    U.filtration G N C.bridge

theorem support_nonempty_iff_exists_not_mem_predecessor :
    (Module.support G N).Nonempty ↔
      ∃ x : U.filtration.carrier C.bridge.layer,
        (x : R) ∉ AdditiveFilteredRingData.predecessor
          U.filtration C.bridge.layer :=
  AssociatedGradedSpecBridge.specSupport_nonempty_iff_exists_not_mem_predecessor
    U.filtration G N C.bridge

end M01AssociatedSpecAdapter

end Adapter

section ZeroLocus

variable {G : Type w} {N : Type z}
variable [CommRing G] [AddCommGroup N] [Module G N]
variable [Module.Finite G N]

theorem support_eq_zeroLocus_annihilator_of_m01_adapter
    (C : M01AssociatedSpecAdapter U G N) :
    Module.support G N =
      PrimeSpectrum.zeroLocus (Module.annihilator G N : Set G) :=
  specSupport_eq_zeroLocus_annihilator

end ZeroLocus

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.M01AssociatedSpecAdapter.support_empty_iff_layer_killed
#print axioms SymplecticStafford.Filtered.M01AssociatedSpecAdapter.support_nonempty_iff_exists_not_mem_predecessor
#print axioms SymplecticStafford.Filtered.support_eq_zeroLocus_annihilator_of_m01_adapter
