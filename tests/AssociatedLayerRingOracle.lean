import SymplecticStafford.Filtered.AssociatedLayerRing

/-! Independent checks for multiplication on the actual associated layers. -/

namespace SymplecticStafford.AssociatedLayerRingOracle

open SymplecticStafford
open SymplecticStafford.Filtered
open SymplecticStafford.Filtered.RingFiltrationData

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

example (i j : ℕ) (a b : ℤ)
    (ha : a ∈ topRingFiltration.carrier i)
    (hb : b ∈ topRingFiltration.carrier j) :
    associatedLayerMul topRingFiltration i j
      (Submodule.Quotient.mk ⟨a, ha⟩)
      (Submodule.Quotient.mk ⟨b, hb⟩) =
      associatedClass topRingFiltration (i + j) (a * b)
        (topRingFiltration.mul_mem ha hb) := by
  exact associatedLayerMul_mk_mk topRingFiltration i j ⟨a, ha⟩ ⟨b, hb⟩

example (i j : ℕ) (a b c : ℤ)
    (ha : a ∈ topRingFiltration.carrier i)
    (hb : b ∈ topRingFiltration.carrier j)
    (hc : c ∈ topRingFiltration.carrier j)
    (hbc : b - c ∈ predecessor topRingFiltration j) :
    associatedLayerMul topRingFiltration i j
      (Submodule.Quotient.mk ⟨a, ha⟩)
      (Submodule.Quotient.mk ⟨b, hb⟩) =
      associatedLayerMul topRingFiltration i j
        (Submodule.Quotient.mk ⟨a, ha⟩)
        (Submodule.Quotient.mk ⟨c, hc⟩) := by
  apply congrArg (associatedLayerMul topRingFiltration i j
    (Submodule.Quotient.mk ⟨a, ha⟩))
  apply (Submodule.Quotient.eq _).mpr
  exact hbc

end SymplecticStafford.AssociatedLayerRingOracle

#print axioms SymplecticStafford.AssociatedLayerRingOracle.topRingFiltration
