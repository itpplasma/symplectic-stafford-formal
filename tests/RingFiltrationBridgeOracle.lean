import SymplecticStafford.Filtered.RingFiltrationBridge

/-!
# Independent oracle for the first filtered/Rees producer boundary

The oracle checks both sides of the boundary: the old set-valued filtration
API admits an exhaustive multiplicative filtration with no submodule degree
zero, while the repaired submodule filtration constructs a genuine quotient
class that detects `1 : ℤ`.
-/

namespace SymplecticStafford.RingFiltrationBridgeOracle

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.RingFiltrationData

example :
    ¬ ∃ P : Submodule ℤᵐᵒᵖ ℤ,
      (P : Set ℤ) = nonnegativeStepFiltration.carrier 0 :=
  nonnegativeStepFiltration_degree_zero_not_submodule

def topRingFiltration : RingFiltrationData (R := ℤ) where
  carrier := fun _ => ⊤
  one_mem := by simp
  mul_mem := by
    intro i j a b ha hb
    simp
  monotone := by
    intro i j hij x hx
    simp
  exhaustive := by
    intro x
    exact ⟨0, by simp⟩

example :
    ∃ n : ℕ, ∃ hn : (1 : ℤ) ∈ topRingFiltration.carrier n,
      associatedClass topRingFiltration n 1 hn ≠ 0 := by
  exact exists_associatedClass_ne_zero_of_ne_zero topRingFiltration one_ne_zero

example : (associatedLayerSupport topRingFiltration).Nonempty := by
  apply (associatedLayerSupport_nonempty_iff_exists_ne_zero topRingFiltration).mpr
  exact ⟨1, one_ne_zero⟩

example : (1 : ℤ) ∈ (toFiltrationData topRingFiltration).carrier 0 := by
  exact topRingFiltration.one_mem

example (n : ℕ) (a : ℤ) (ha : a ∈ topRingFiltration.carrier n) :
    associatedClass topRingFiltration n a ha = 0 ↔
      a ∈ predecessor topRingFiltration n :=
  associatedClass_eq_zero_iff topRingFiltration n a ha

end SymplecticStafford.RingFiltrationBridgeOracle

#print axioms SymplecticStafford.RingFiltrationBridgeOracle.topRingFiltration
#print axioms SymplecticStafford.RingFiltrationBridgeOracle.topRingFiltration
