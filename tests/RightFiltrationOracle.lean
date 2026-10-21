module

public import SymplecticStafford.FiniteLength.RightFiltration

@[expose] public section

namespace SymplecticStafford.FiniteLength.RightFiltrationOracle

open SymplecticStafford.FiniteLength

/- A concrete minimal support point. -/
def support : Set Unit := {()}

def minimalPoint : MinimalSupportPoint support where
  point := ()
  mem_support := by simp [support]
  minimal := by
    intro q hq _
    simpa [support] using hq

/- The regular module over the opposite rational field is a right module over
 `ℚ`; the two-term filtration has one nonzero simple factor. -/
abbrev A := ℚᵐᵒᵖ

def regularFiltration :
    RightMinimalSupportFiltration (R := ℚ) (M := A) (α := Unit) 1 where
  support := support
  minimalPoint := minimalPoint
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp
  step := by
    intro i
    have hi0 : i = 0 := by fin_cases i; rfl
    subst i
    have hP : (⊥ : Submodule A A).comap (⊤ : Submodule A A).subtype = ⊥ := by
      rw [Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _)
    have hsimple :
        IsSimpleModule A
          ((⊤ : Submodule A A) ⧸
            ((⊥ : Submodule A A).comap (⊤ : Submodule A A).subtype)) := by
      let e :
          ((⊤ : Submodule A A) ⧸
              ((⊥ : Submodule A A).comap (⊤ : Submodule A A).subtype)) ≃ₗ[A] A :=
        (Submodule.quotEquivOfEqBot
          ((⊥ : Submodule A A).comap (⊤ : Submodule A A).subtype) hP).trans
          Submodule.topEquiv
      rw [e.isSimpleModule_iff]
      infer_instance
    apply (covBy_iff_quot_is_simple bot_le).2
    simpa using hsimple
  quotient_finite := by
    intro i
    fin_cases i
    infer_instance

example : IsFiniteLength A A := regularFiltration.isFiniteLength

example : Module.Finite A A := regularFiltration.moduleFinite

example : Module.length A A = 1 := regularFiltration.module_length_eq_index

/- Independent check of the same concrete value from the regular simple
 module, rather than through the new filtration theorem. -/
example : Module.length A A = 1 := by
  exact Module.length_eq_one A A

example : Module.length A A ≠ ⊤ := regularFiltration.length_ne_top

/- The quotient recorded by the filtration is not merely a proposition: it
 has an actual finite-module witness supplied by the regular module. -/
example (i : Fin 1) :
    Module.Finite A
      ((regularFiltration.level i.succ) ⧸
        ((regularFiltration.level i.castSucc).comap
          (regularFiltration.level i.succ).subtype)) :=
  regularFiltration.quotient_finite i

end SymplecticStafford.FiniteLength.RightFiltrationOracle
