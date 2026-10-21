module

public import SymplecticStafford.FiniteLength.MinimalPrimeLength

@[expose] public section

/-!
# Explicit right-module finite-length filtrations

This file gives M05 a concrete algebraic input.  A `RightMinimalSupportFiltration`
is a finite filtration by actual submodules of a right module (encoded as a
module over the opposite ring).  Every adjacent factor is an explicit
submodule quotient, supplied as a finite module, and every adjacent inclusion
is maximal.  The latter is exactly the composition-series condition; the
former records the finite quotient data needed by the minimal-support lane.

No localization or characteristic-support construction is asserted here.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section RightFiltration

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {α : Type w} [Preorder α]

/-- A finite minimal-support filtration of a right `R`-module.

The index `0` is the bottom term and `last` is the whole module.  The
quotient at `i` is formed inside the next submodule, so the right-module
orientation is visible in every factor:
`level (i+1) / (level i.comap level (i+1).subtype)`.
-/
structure RightMinimalSupportFiltration (n : Nat) where
  support : Set α
  minimalPoint : MinimalSupportPoint support
  level : Fin (n + 1) → Submodule Rᵐᵒᵖ M
  head : level 0 = ⊥
  last : level (Fin.last n) = ⊤
  step : ∀ i : Fin n, CovBy (level i.castSucc) (level i.succ)
  quotient_finite : ∀ i : Fin n,
    Module.Finite Rᵐᵒᵖ
      ((level i.succ) ⧸
        ((level i.castSucc).comap (level i.succ).subtype))

namespace RightMinimalSupportFiltration

variable {n : Nat}

/-- Forgetting the support labels turns the filtration into a composition
series in the right-module submodule lattice. -/
def compositionSeries (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    CompositionSeries (Submodule Rᵐᵒᵖ M) :=
  { length := n
    toFun := F.level
    step := F.step }

@[simp] theorem compositionSeries_apply
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n)
    (i : Fin (n + 1)) : F.compositionSeries i = F.level i := rfl

theorem isFiniteLength
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    IsFiniteLength Rᵐᵒᵖ M := by
  apply isFiniteLength_of_exists_compositionSeries
  refine ⟨F.compositionSeries, ?_, ?_⟩
  · exact F.head
  · exact F.last

theorem moduleFinite
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    Module.Finite Rᵐᵒᵖ M := by
  have hN : IsNoetherian Rᵐᵒᵖ M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (F.isFiniteLength)).1
  letI : IsNoetherian Rᵐᵒᵖ M := hN
  exact inferInstance

theorem length_ne_top
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    Module.length Rᵐᵒᵖ M ≠ ⊤ :=
  moduleLength_ne_top_of_isFiniteLength F.isFiniteLength

theorem filtration_length_eq
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    (F.compositionSeries).length = Module.length Rᵐᵒᵖ M := by
  exact Module.length_compositionSeries F.compositionSeries F.head F.last

theorem module_length_eq_index
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    Module.length Rᵐᵒᵖ M = n := by
  symm
  exact F.filtration_length_eq

end RightMinimalSupportFiltration

end RightFiltration

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.RightMinimalSupportFiltration.isFiniteLength
#print axioms SymplecticStafford.FiniteLength.RightMinimalSupportFiltration.moduleFinite
#print axioms SymplecticStafford.FiniteLength.RightMinimalSupportFiltration.length_ne_top
#print axioms SymplecticStafford.FiniteLength.RightMinimalSupportFiltration.module_length_eq_index
