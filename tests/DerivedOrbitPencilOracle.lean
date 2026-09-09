import SymplecticStafford.FiniteLength.DerivedOrbitPencil
import SymplecticStafford.FiniteLength.RightFiltration
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Independent oracle for the derived finite-dimensional activated pencil

The coefficient ring is the rational field, the module is its opposite
regular module, and the central embedding is the literal opposite map.  The
orbit basis is not supplied: it is obtained by the theorem from finite
`ℚ`-dimension.  The filtration is the concrete one-factor filtration from
`RightFiltrationOracle` reproduced below, and the ordered relation uses
`l = 0`, so all coefficient orders remain visible.
-/

namespace SymplecticStafford.FiniteLength.DerivedOrbitPencilOracle

open SymplecticStafford.FiniteLength

abbrev R := ℚ
abbrev M := ℚᵐᵒᵖ
abbrev K := ℚ

def support : Set Unit := {()}

def minimalPoint : MinimalSupportPoint support where
  point := ()
  mem_support := by simp [support]
  minimal := by
    intro q hq _
    simpa [support] using hq

def regularFiltration :
    RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) 1 where
  support := support
  minimalPoint := minimalPoint
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp
  step := by
    intro i
    have hi0 : i = 0 := by fin_cases i; rfl
    subst i
    have hP : (⊥ : Submodule M M).comap (⊤ : Submodule M M).subtype = ⊥ := by
      rw [Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _)
    have hsimple :
        IsSimpleModule M
          ((⊤ : Submodule M M) ⧸
            ((⊥ : Submodule M M).comap (⊤ : Submodule M M).subtype)) := by
      let e :
          ((⊤ : Submodule M M) ⧸
              ((⊥ : Submodule M M).comap (⊤ : Submodule M M).subtype)) ≃ₗ[M] M :=
        (Submodule.quotEquivOfEqBot
          ((⊥ : Submodule M M).comap (⊤ : Submodule M M).subtype) hP).trans
          Submodule.topEquiv
      rw [e.isSimpleModule_iff]
      infer_instance
    apply (covBy_iff_quot_is_simple bot_le).2
    simpa using hsimple
  quotient_finite := by
    intro i
    fin_cases i
    infer_instance

def oppositeScalars : K →+* Rᵐᵒᵖ :=
  { toFun := MulOpposite.op
    map_one' := rfl
    map_mul' := by
      intro x y
      simpa [mul_comm] using (MulOpposite.op_mul x y)
    map_zero' := rfl
    map_add' := by intro x y; rfl }

example : Function.Injective (oppositeScalars : K →+* Rᵐᵒᵖ) := by
  intro x y h
  exact MulOpposite.op_injective h

example : ∀ (k : K) (m : M), k • m = oppositeScalars k • m := by
  intro k m
  change k • m = (MulOpposite.op k) • m
  rw [Algebra.smul_def]
  rfl

example : Module.Finite K M := by infer_instance

example : ∃ z : K, z ≠ 0 ∧ RightCyclic (R := R) ((1 : M) + z • (0 : M)) := by
  let ι := oppositeScalars
  have hι : ∀ (k : K) (m : M), k • m = ι k • m := by
    intro k m
    change k • m = (MulOpposite.op k) • m
    rw [Algebra.smul_def]
    rfl
  let rightAction : R → M → M := fun r m => (MulOpposite.op r) • m
  have hrightadd : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y := by
    intro r x y
    exact mul_add _ _ _
  have hcentral : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m := by
    intro k m r
    simp only [rightAction]
    exact (smul_comm k (MulOpposite.op r) m).symm
  have hv : RightCyclic (R := R) (1 : M) := by
    intro y
    refine ⟨MulOpposite.op y.unop, ?_⟩
    simp
  obtain ⟨z, hz, hcyc, _hrel⟩ :=
    exists_activated_right_cyclic_of_finiteDimensional_central
      (F := regularFiltration) ι hι rightAction hrightadd hcentral
      (1 : M) (0 : M) (1 : M) (1 : R) (0 : R) (by simp [rightAction])
      (by simp [rightAction]) hv ({0} : Set K) (by simp)
  exact ⟨z, by simpa using hz, by simpa using hcyc⟩

end SymplecticStafford.FiniteLength.DerivedOrbitPencilOracle
