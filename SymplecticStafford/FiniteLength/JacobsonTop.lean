module

public import SymplecticStafford.FiniteLength.PencilBridge
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

/-!
# Actual radical quotients detect right-module generation

The radical here is Mathlib's `Module.jacobson`: the intersection of all
maximal submodules.  For a finitely generated module, a proper generated
submodule lies in a maximal submodule, so generation modulo this radical
reflects actual generation.  No filtration, top coordinates, or generation
reflection certificate is an input.

This proves the radical-lifting step of paper part II.1 for arbitrary rings
and finitely generated right modules, and constructs a simple quotient
detecting every nongenerating vector.  Artinianity additionally makes the
actual radical quotient semisimple.  The division-ring block decomposition,
independence criterion, and activated-pencil argument remain separate work.
-/

namespace SymplecticStafford.FiniteLength

section Radical

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The actual module radical is superfluous in a finitely generated module. -/
theorem sup_jacobson_eq_top_iff [Module.Finite R M] (N : Submodule R M) :
    N ⊔ Module.jacobson R M = ⊤ ↔ N = ⊤ := by
  constructor
  · intro h
    rcases eq_top_or_exists_le_coatom N with hN | ⟨P, hP, hNP⟩
    · exact hN
    · have hrad : Module.jacobson R M ≤ P := sInf_le hP
      exact False.elim (hP.1 (top_le_iff.mp (h ▸ sup_le hNP hrad)))
  · rintro rfl
    exact top_sup_eq _

/-- Generation by any set is detected on the actual radical quotient. -/
theorem span_eq_top_iff_jacobson_quotient [Module.Finite R M] (s : Set M) :
    Submodule.span R s = ⊤ ↔
      Submodule.span R ((Module.jacobson R M).mkQ '' s) = ⊤ := by
  rw [← Submodule.map_span, Submodule.map_mkQ_eq_top, sup_comm]
  exact (sup_jacobson_eq_top_iff _).symm

/-- Artinianity suffices for semisimplicity of the actual radical quotient. -/
theorem jacobson_quotient_isSemisimple [IsArtinian R M] :
    IsSemisimpleModule R (M ⧸ Module.jacobson R M) := by
  exact (IsArtinian.isSemisimpleModule_iff_jacobson R
    (M ⧸ Module.jacobson R M)).mpr (Module.jacobson_quotient_jacobson R M)

end Radical

section RightModule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The existential right-action convention agrees with the literal cyclic span. -/
theorem rightCyclic_iff_span_singleton (v : M) :
    RightCyclic (R := R) v ↔ Submodule.span Rᵐᵒᵖ ({v} : Set M) = ⊤ := by
  simp only [RightCyclic, Submodule.eq_top_iff', Submodule.mem_span_singleton]

/-- A vector generates precisely when its image in the actual radical quotient
generates.  Finite length is stronger than the finite-generation hypothesis. -/
theorem rightCyclic_iff_jacobson_quotient [Module.Finite Rᵐᵒᵖ M] (v : M) :
    RightCyclic (R := R) v ↔
      RightCyclic (R := R) ((Module.jacobson Rᵐᵒᵖ M).mkQ v) := by
  rw [rightCyclic_iff_span_singleton, rightCyclic_iff_span_singleton]
  simpa only [Set.image_singleton] using
    span_eq_top_iff_jacobson_quotient (R := Rᵐᵒᵖ) ({v} : Set M)

/-- Every nongenerating vector has an actual simple quotient in which it
vanishes.  The maximal submodule and the quotient are constructed. -/
theorem exists_simple_quotient_killing_of_not_rightCyclic
    [Module.Finite Rᵐᵒᵖ M] (v : M) (hv : ¬ RightCyclic (R := R) v) :
    ∃ N : Submodule Rᵐᵒᵖ M,
      IsSimpleModule Rᵐᵒᵖ (M ⧸ N) ∧ N.mkQ v = 0 := by
  have hspan : Submodule.span Rᵐᵒᵖ ({v} : Set M) ≠ ⊤ :=
    fun h => hv ((rightCyclic_iff_span_singleton v).mpr h)
  obtain ⟨N, hN, hvN⟩ :=
    (eq_top_or_exists_le_coatom (Submodule.span Rᵐᵒᵖ ({v} : Set M))).resolve_left hspan
  refine ⟨N, isSimpleModule_iff_isCoatom.mpr hN, ?_⟩
  exact (Submodule.Quotient.mk_eq_zero N).mpr
    (hvN (Submodule.mem_span_singleton_self v))

/-- Generation is equivalent to surviving every actual simple quotient.
This is the module-theoretic criterion underlying the simple-block tests. -/
theorem rightCyclic_iff_nonzero_in_simple_quotients
    [Module.Finite Rᵐᵒᵖ M] (v : M) :
    RightCyclic (R := R) v ↔
      ∀ N : Submodule Rᵐᵒᵖ M,
        IsSimpleModule Rᵐᵒᵖ (M ⧸ N) → N.mkQ v ≠ 0 := by
  constructor
  · intro hv N hsimple hzero
    have hvN := (Submodule.Quotient.mk_eq_zero N).mp hzero
    have hspan : Submodule.span Rᵐᵒᵖ ({v} : Set M) ≤ N :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr hvN
    rw [(rightCyclic_iff_span_singleton v).mp hv] at hspan
    exact (isSimpleModule_iff_isCoatom.mp hsimple).1 (top_le_iff.mp hspan)
  · intro h
    by_contra hv
    obtain ⟨N, hsimple, hzero⟩ :=
      exists_simple_quotient_killing_of_not_rightCyclic v hv
    exact h N hsimple hzero

/-- Nongenerating parameters of any family are exactly those seen on the
actual radical quotient; no scalar or pencil assumptions are needed. -/
theorem nongenerating_parameters_eq_jacobson_quotient
    [Module.Finite Rᵐᵒᵖ M] {ι : Type*} (v : ι → M) :
    {i | ¬ RightCyclic (R := R) (v i)} =
      {i | ¬ RightCyclic (R := R) ((Module.jacobson Rᵐᵒᵖ M).mkQ (v i))} := by
  ext i
  exact not_congr (rightCyclic_iff_jacobson_quotient (v i))

end RightModule

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.sup_jacobson_eq_top_iff
#print axioms SymplecticStafford.FiniteLength.span_eq_top_iff_jacobson_quotient
#print axioms SymplecticStafford.FiniteLength.jacobson_quotient_isSemisimple
#print axioms SymplecticStafford.FiniteLength.rightCyclic_iff_jacobson_quotient
#print axioms SymplecticStafford.FiniteLength.exists_simple_quotient_killing_of_not_rightCyclic
#print axioms SymplecticStafford.FiniteLength.rightCyclic_iff_nonzero_in_simple_quotients
#print axioms SymplecticStafford.FiniteLength.nongenerating_parameters_eq_jacobson_quotient
