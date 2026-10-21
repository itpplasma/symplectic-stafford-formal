module

public import SymplecticStafford.Ordered.M08ExactSupportBridge

@[expose] public section

/-!
Independent trust-disabled oracle for the M08 exact-support bridge and its
finite-filtered actual-support boundary.  The branch maps are the identity
and zero maps over `ℤ`; the negative example uses the same concrete support
modules as the source boundary and therefore checks that the missing bridge
is substantive.
-/

namespace SymplecticStafford.M08ExactSupportBridgeOracle

open SymplecticStafford.Ordered
open SymplecticStafford.Filtered

def exactData : ExactCharacteristicSupportBridge
    (A := ℤ) (QF := ℤ) (QJ := ℤ) (QG := ZMod 1) where
  left := LinearMap.id
  right := 0
  exact := by
    intro y
    constructor
    · intro h
      exact ⟨y, rfl⟩
    · intro hy
      simp
  left_injective := by
    intro x y h
    simpa using h
  right_surjective := by
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

example :
    Module.support ℤ ℤ =
      Module.support ℤ ℤ ∪ Module.support ℤ (ZMod 1) := by
  exact characteristicSupport_eq_union_of_exact_bridge exactData

example :
    Module.support ℤ ℤ ⊆
      Module.support ℤ ℤ ∪ Module.support ℤ (ZMod 1) := by
  exact characteristicSupport_subset_union_of_exact_bridge exactData

example :
    ¬ (Module.support ℤ ℤ ⊆
      Module.support ℤ (ZMod 1) ∪ Module.support ℤ (ZMod 1)) :=
  finite_filtered_actual_support_union_fails

example :
    (SpecCharacteristicSupport ℤ ℤ).Nonempty := by
  change (Module.support ℤ ℤ).Nonempty
  rw [integer_actual_support_eq_univ]
  simp

example :
    SpecCharacteristicSupport ℤ (ZMod 1) = ∅ := by
  change Module.support ℤ (ZMod 1) = ∅
  exact zero_mod_one_actual_support_eq_empty

end SymplecticStafford.M08ExactSupportBridgeOracle

#print axioms SymplecticStafford.Ordered.characteristicSupport_eq_union_of_exact_bridge
#print axioms SymplecticStafford.Ordered.finite_filtered_actual_support_union_fails
