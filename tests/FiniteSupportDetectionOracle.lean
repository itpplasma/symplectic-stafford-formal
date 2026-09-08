import SymplecticStafford.Filtered.FiniteSupportDetection
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

namespace SymplecticStafford.Filtered.FiniteSupportDetectionOracle

open FiniteDescendingFiltration

def scalarFiltration : FiniteDescendingFiltration ℤ where
  height := 2
  carrier := fun k => if k = 0 then Set.univ else {0}
  zero_mem := by
    intro k
    by_cases hk : k = 0 <;> simp [hk]
  exhaustive := by
    intro x
    simp [Set.mem_univ]
  descending := by
    intro k x hx
    by_cases hk : k = 0
    · simp [hk]
    · have hk' : k + 1 ≠ 0 := Nat.succ_ne_zero k
      simpa [hk, hk'] using hx
  separated := by
    intro x hx
    simpa using hx

example : scalarFiltration.AssociatedTopNonzero 7 0 := by
  constructor
  · simp [scalarFiltration]
  · norm_num [scalarFiltration]

example : ∃ k, k < scalarFiltration.height ∧
    scalarFiltration.AssociatedTopNonzero 7 k := by
  apply scalarFiltration.exists_associatedTopNonzero
  norm_num

example : ∃ k, k < scalarFiltration.height ∧
    (7 : ℤ) ∈ scalarFiltration.carrier k ∧
    (7 : ℤ) ∉ scalarFiltration.carrier (k + 1) := by
  apply scalarFiltration.exists_detecting_layer
  norm_num

end SymplecticStafford.Filtered.FiniteSupportDetectionOracle
