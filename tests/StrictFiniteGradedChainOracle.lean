module

public import Mathlib.Tactic.NormNum
public import SymplecticStafford.Filtered.StrictFiniteGradedChain

@[expose] public section

/-!
# Independent oracle for the finite strict graded-chain bridge

The filtration is the two-step filtration `ℚ ⊃ 0`.  The proper filtered
submodule is `0`, so the unique associated-layer map is injective but not
surjective.  This checks the bridge on an actual module, rather than merely
repeating its type under variables.
-/

namespace SymplecticStafford.Filtered.StrictFiniteGradedChainOracle

open FiniteFilteredModule
open StrictFiniteGradedChain

def scalarFiltration : FiniteFilteredModule (R := ℚ) (M := ℚ) where
  height := 1
  carrier := fun n => if n = 0 then ⊤ else ⊥
  exhaustive := by simp
  descending := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · simp [hn]
  separated := by simp

def properSubmodule : Submodule ℚ ℚ := ⊥

example : properSubmodule < (⊤ : Submodule ℚ ℚ) := by
  simp [properSubmodule]

example (k : Fin scalarFiltration.height) :
    Function.Injective
      (layerMap scalarFiltration properSubmodule k) := by
  exact layerMap_injective scalarFiltration properSubmodule k

example : ∃ k : Fin scalarFiltration.height,
    ¬ Function.Surjective (layerMap scalarFiltration properSubmodule k) := by
  exact exists_layerMap_not_surjective_of_lt_top scalarFiltration
    properSubmodule (by simp [properSubmodule])

end SymplecticStafford.Filtered.StrictFiniteGradedChainOracle

#print axioms SymplecticStafford.Filtered.StrictFiniteGradedChainOracle.scalarFiltration
