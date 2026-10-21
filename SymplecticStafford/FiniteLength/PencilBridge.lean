module

public import SymplecticStafford.FiniteLength.Pencil
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-!
A conditional bridge from the coordinate pencil to cyclic right modules.
The caller supplies generation reflection from a finite division-ring top.
No finite-length structure theorem, radical lifting, or paper M07 theorem is
asserted here; in particular, constructing this certificate is a separate task.
-/

namespace SymplecticStafford.FiniteLength

/-- Cyclic generation in a right module, expressed as a left action of the
opposite ring. This preserves the intended handedness. -/
def RightCyclic {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module Rᵐᵒᵖ M] (m : M) : Prop :=
  ∀ y : M, ∃ r : Rᵐᵒᵖ, r • m = y

section Bridge

variable {R M K ι : Type*} [Semiring R] [AddCommGroup M]
    [Module Rᵐᵒᵖ M] [Field K] [Module K M]
    [Fintype ι] [DecidableEq ι]
    {D : ι → Type*} [∀ i, DivisionRing (D i)]

/-- A supplied top comparison with scalar compatibility and generation
reflection. These are hypotheses, not consequences of finite length here. -/
structure CyclicTopBridge (ιmap : (i : ι) → K →+* D i) where
  top : M →+ (∀ i, D i)
  map_smul : ∀ (z : K) (m : M) (i : ι),
    top (z • m) i = ιmap i z * top m i
  reflects_generation : ∀ m, TopGenerator (top m) → RightCyclic (R := R) m

variable {ιmap : (i : ι) → K →+* D i}
    (C : CyclicTopBridge (R := R) (M := M) ιmap)

/-- A pencil whose initial top has no zero coordinate fails to generate only
at finitely many scalars, conditional on the supplied top comparison. -/
theorem CyclicTopBridge.finite_nongenerating_scalars
    (hinj : ∀ i, Function.Injective (ιmap i)) (m u : M)
    (hm : ∀ i, C.top m i ≠ 0) :
    Set.Finite {z : K | ¬ RightCyclic (R := R) (m + z • u)} := by
  apply (finite_pencil_exceptions ιmap (C.top m) (C.top u) hm hinj).subset
  intro z hz
  by_contra hbad
  apply hz
  apply C.reflects_generation
  apply (semisimple_top_criterion _).2
  intro i
  have hi : C.top m i + ιmap i z * C.top u i ≠ 0 := by
    intro hi
    exact hbad ⟨i, hi⟩
  simpa only [map_add, Pi.add_apply, C.map_smul] using hi

/-- Over an infinite scalar field one may also avoid any supplied finite
forbidden set while selecting a cyclic member of the pencil. -/
theorem CyclicTopBridge.exists_generating_scalar_avoiding [Infinite K]
    (hinj : ∀ i, Function.Injective (ιmap i)) (m u : M)
    (hm : ∀ i, C.top m i ≠ 0) (forbidden : Set K)
    (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧ RightCyclic (R := R) (m + z • u) := by
  classical
  have hf := hforbidden.union (C.finite_nongenerating_scalars hinj m u hm)
  obtain ⟨z, _, hz⟩ := (Set.infinite_univ.sdiff hf).nonempty
  exact ⟨z, fun h => hz (Or.inl h), by
    by_contra h
    exact hz (Or.inr h)⟩

end Bridge

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.CyclicTopBridge.finite_nongenerating_scalars
#print axioms SymplecticStafford.FiniteLength.CyclicTopBridge.exists_generating_scalar_avoiding
