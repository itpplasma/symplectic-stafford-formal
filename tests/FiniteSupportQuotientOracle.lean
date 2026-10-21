module

public import SymplecticStafford.Filtered.FiniteSupportQuotient
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace SymplecticStafford.Filtered.FiniteSupportQuotientOracle

def scalarFiltration : FiniteFilteredModule (R := ℤ) (M := ℤ) where
  height := 2
  carrier := fun k => if k = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  separated := by simp

/-- The concrete nonzero integer is detected in the first quotient layer. -/
example : ∃ k, k < scalarFiltration.height ∧
    (7 : ℤ) ∈ scalarFiltration.carrier k ∧
      Submodule.mkQ (scalarFiltration.carrier (k + 1)) (7 : ℤ) ≠ 0 := by
  apply scalarFiltration.exists_associatedTopQuotient_nonzero
  norm_num

/-- The quotient witness has the expected layer, not merely an unspecified one. -/
example : Submodule.mkQ (scalarFiltration.carrier (0 + 1)) (7 : ℤ) ≠ 0 := by
  intro hzero
  have hmk :
      (Submodule.Quotient.mk (7 : ℤ) : ℤ ⧸ scalarFiltration.carrier (0 + 1)) = 0 := by
    simpa only [Submodule.mkQ_apply] using hzero
  have hmem : (7 : ℤ) ∈ scalarFiltration.carrier (0 + 1) :=
    (Submodule.Quotient.mk_eq_zero (scalarFiltration.carrier (0 + 1))).mp hmk
  have hnotmem : ¬ (7 : ℤ) ∈ scalarFiltration.carrier (0 + 1) := by
    simp [scalarFiltration]
  exact hnotmem hmem

example : Submodule.mkQ (scalarFiltration.carrier (0 + 1)) (7 : ℤ) ≠ 0 ↔
    (7 : ℤ) ∉ scalarFiltration.carrier (0 + 1) := by
  exact scalarFiltration.quotient_ne_zero_iff_not_mem 7 0

end SymplecticStafford.Filtered.FiniteSupportQuotientOracle
