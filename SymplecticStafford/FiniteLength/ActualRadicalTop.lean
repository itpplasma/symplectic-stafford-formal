module

public import SymplecticStafford.FiniteLength.RightFiltration
public import SymplecticStafford.FiniteLength.JacobsonTop

@[expose] public section

/-!
# The finite-length output available before division-ring coordinates

An explicit right composition filtration does construct finite generation and
the actual Jacobson top.  This file records that kernel-checked output in one
place.  It deliberately stops at the semisimple radical quotient: obtaining a
finite family of isotypic division-ring coordinates and their scalar pencil is
a separate algebraization/decomposition obligation.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {α : Type w} [Preorder α]

/-- Finite-length and Jacobson-top facts extracted from an actual right
composition filtration.  The quotient and cyclicity statements use the
opposite-ring right-module convention throughout. -/
theorem actual_radical_top_of_right_filtration
    {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := α) n) :
    Module.Finite Rᵐᵒᵖ M ∧
      IsFiniteLength Rᵐᵒᵖ M ∧
      IsSemisimpleModule Rᵐᵒᵖ (M ⧸ Module.jacobson Rᵐᵒᵖ M) ∧
      (∀ v : M,
        RightCyclic (R := R) v ↔
          RightCyclic (R := R)
            ((Module.jacobson Rᵐᵒᵖ M).mkQ v)) := by
  have hfinite : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have hlength : IsFiniteLength Rᵐᵒᵖ M := F.isFiniteLength
  have hsplit : IsNoetherian Rᵐᵒᵖ M ∧ IsArtinian Rᵐᵒᵖ M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength)
  letI : Module.Finite Rᵐᵒᵖ M := hfinite
  letI : IsNoetherian Rᵐᵒᵖ M := hsplit.1
  letI : IsArtinian Rᵐᵒᵖ M := hsplit.2
  exact ⟨hfinite, hlength, jacobson_quotient_isSemisimple,
    fun v => rightCyclic_iff_jacobson_quotient v⟩

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.actual_radical_top_of_right_filtration
