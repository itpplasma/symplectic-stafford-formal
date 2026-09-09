import SymplecticStafford.FiniteLength.FiniteOrbitPencil
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Activated pencils from finite-dimensional central modules

The finite-orbit interface in `FiniteOrbitPencil` deliberately accepts an
orbit basis as a hypothesis.  This file derives that basis when the module is
finite-dimensional over a central field.  The centrality data are explicit:
the field acts through a ring homomorphism into the opposite ring and this
action agrees with the given field module structure.  Thus the `K`-span of an
`Rᵐᵒᵖ`-orbit is exactly its right-module span; no supplied orbit basis or
commutativity of the coefficient ring is used.

Finite length alone does not imply finite-dimensionality over an unrelated
field, so `Module.Finite K M` is retained as a genuine hypothesis.
-/

namespace SymplecticStafford.FiniteLength

open Module

universe u v w

section OrbitBasis

variable {A Q K : Type*} [AddCommGroup Q] [Field K] [Module K Q]

theorem exists_orbit_basis_of_finiteDimensional
    [Module.Finite K Q]
    (act : A → Q →ₗ[K] Q) (q : Q)
    (hspan : OrbitSpanTop act q) :
    ∃ n : Nat, ∃ b : Module.Basis (Fin n) K Q,
      ∃ c : Fin n → A, ∀ i, act (c i) q = b i := by
  let s : Set Q := Set.range (fun a : A => act a q)
  have hs : Submodule.span K s = ⊤ := hspan
  obtain ⟨f, hfmem, hfspan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K s
  let b : Module.Basis (Fin (Module.finrank K (Submodule.span K s))) K Q :=
    Module.Basis.mk hfli (by
      intro x hx
      have hx' : x ∈ Submodule.span K (Set.range f) := by
        rw [hfspan]
        exact hs ▸ trivial
      exact hx')
  have hbeq : ∀ i, b i = f i := by
    intro i
    exact Module.Basis.mk_apply hfli (by
      intro x hx
      have hx' : x ∈ Submodule.span K (Set.range f) := by
        rw [hfspan]
        exact hs ▸ trivial
      exact hx') i
  choose c hc using hfmem
  refine ⟨Module.finrank K (Submodule.span K s), b, c, ?_⟩
  intro i
  rw [hbeq]
  exact hc i

end OrbitBasis

section CentralOrbit

variable {R M K : Type*} [Ring R] [AddCommGroup M]
variable [Module Rᵐᵒᵖ M] [Field K] [Module K M]
variable [SMulCommClass K Rᵐᵒᵖ M]

/-- The opposite-ring action as a `K`-linear orbit map. -/
def centralOrbitAction (r : Rᵐᵒᵖ) : M →ₗ[K] M :=
  { toFun := fun m => r • m
    map_add' := fun x y => smul_add r x y
    map_smul' := fun k m =>
      ((@smul_comm K Rᵐᵒᵖ M _ _ inferInstance k r m).symm) }

theorem centralOrbitAction_apply (r : Rᵐᵒᵖ) (m : M) :
    centralOrbitAction (K := K) r m = r • m := rfl

theorem rightCyclic_iff_centralOrbitSpan
    (ι : K →+* Rᵐᵒᵖ)
    (hι : ∀ (k : K) (m : M), k • m = ι k • m)
    (m : M) :
    RightCyclic (R := R) m ↔
      OrbitSpanTop (centralOrbitAction (R := R) (M := M) (K := K)) m := by
  constructor
  · intro hm
    unfold OrbitSpanTop
    apply top_unique
    intro y hy
    obtain ⟨r, hr⟩ := hm y
    rw [← hr]
    exact Submodule.subset_span ⟨r, rfl⟩
  · intro hspan y
    have hR : ∀ x : M, x ∈ Submodule.span Rᵐᵒᵖ
        (Set.range (fun r : Rᵐᵒᵖ => r • m)) →
        ∃ r : Rᵐᵒᵖ, r • m = x := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ =>
        ∃ r : Rᵐᵒᵖ, r • m = x) ?_ ?_ ?_ ?_ hx
      · intro x hx
        rcases hx with ⟨r, hr⟩
        exact ⟨r, hr⟩
      · exact ⟨0, by simp⟩
      · intro x y hx hy hxp hyp
        rcases hxp with ⟨r, hr⟩
        rcases hyp with ⟨s, hs⟩
        refine ⟨r + s, ?_⟩
        rw [add_smul, ← hr, ← hs]
      · intro a x hx hxp
        rcases hxp with ⟨r, hr⟩
        refine ⟨a * r, ?_⟩
        rw [mul_smul, ← hr]
    have hKtoR : ∀ x : M, x ∈ Submodule.span K
        (Set.range (fun r : Rᵐᵒᵖ => r • m)) →
        x ∈ Submodule.span Rᵐᵒᵖ
          (Set.range (fun r : Rᵐᵒᵖ => r • m)) := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ =>
        x ∈ Submodule.span Rᵐᵒᵖ
          (Set.range (fun r : Rᵐᵒᵖ => r • m))) ?_ ?_ ?_ ?_ hx
      · intro x hx
        rcases hx with ⟨r, rfl⟩
        exact Submodule.subset_span ⟨r, rfl⟩
      · exact (Submodule.zero_mem _)
      · intro x y hx hy hx' hy'
        exact Submodule.add_mem _ hx' hy'
      · intro k x hx hx'
        have hscalar : ∀ y : M, y ∈ Submodule.span Rᵐᵒᵖ
            (Set.range (fun r : Rᵐᵒᵖ => r • m)) →
            k • y ∈ Submodule.span Rᵐᵒᵖ
              (Set.range (fun r : Rᵐᵒᵖ => r • m)) := by
          intro y hy
          refine Submodule.span_induction (p := fun y _ =>
            k • y ∈ Submodule.span Rᵐᵒᵖ
              (Set.range (fun r : Rᵐᵒᵖ => r • m))) ?_ ?_ ?_ ?_ hy
          · intro y hy
            rcases hy with ⟨r, hr⟩
            apply Submodule.subset_span
            refine ⟨r * ι k, ?_⟩
            dsimp
            calc
              (r * ι k) • m = r • (ι k • m) := mul_smul r (ι k) m
              _ = r • (k • m) := by rw [hι k m]
              _ = k • (r • m) :=
                (@smul_comm K Rᵐᵒᵖ M _ _ inferInstance k r m).symm
              _ = k • y := congrArg (fun q : M => k • q) hr
          · simp
          · intro y z hy hz hy' hz'
            rw [smul_add]
            exact Submodule.add_mem _ hy' hz'
          · intro r y hy hy'
            rw [@smul_comm K Rᵐᵒᵖ M _ _ inferInstance k r y]
            exact Submodule.smul_mem _ r hy'
        exact hscalar x hx'
    apply hR y (hKtoR y ?_)
    have htop : Submodule.span K
        (Set.range (fun r : Rᵐᵒᵖ => r • m)) = ⊤ := by
      simpa [OrbitSpanTop, centralOrbitAction_apply] using hspan
    rw [htop]
    trivial

end CentralOrbit

section DerivedActivated

variable {R M K : Type*} [Ring R] [AddCommGroup M]
variable [Module Rᵐᵒᵖ M] [Field K] [Module K M]
variable [Infinite K] [SMulCommClass K Rᵐᵒᵖ M]

/-- Generic activated-pencil theorem with the orbit basis derived from finite
`K`-dimension and an explicit central scalar embedding. -/
theorem exists_activated_right_cyclic_of_finiteDimensional_central
    [Module.Finite K M]
    {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (ι : K →+* Rᵐᵒᵖ)
    (hι : ∀ (k : K) (m : M), k • m = ι k • m)
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : RightCyclic (R := R) v) (forbidden : Set K)
    (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  let act : (Rᵐᵒᵖ) → M →ₗ[K] M :=
    centralOrbitAction (R := R) (M := M) (K := K)
  have htop : ∀ m : M,
      RightCyclic (R := R) m ↔ OrbitSpanTop act m := by
    intro m
    exact rightCyclic_iff_centralOrbitSpan ι hι m
  have horbit : ∀ m : M, RightCyclic (R := R) m →
      ∃ n : Nat, ∃ basis : Module.Basis (Fin n) K M,
        ∃ c : Fin n → Rᵐᵒᵖ, ∀ i, act (c i) m = basis i := by
    intro m hm
    exact exists_orbit_basis_of_finiteDimensional act m
      ((htop m).mp hm)
  exact exists_activated_right_cyclic_of_finite_orbit_basis
    (F := F) (top := LinearMap.id) act htop horbit
    rightAction rightAction_add central_smul_right v u e b l vL_zero e_decomp
    hv forbidden hforbidden

end DerivedActivated

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.exists_orbit_basis_of_finiteDimensional
#print axioms SymplecticStafford.FiniteLength.rightCyclic_iff_centralOrbitSpan
#print axioms SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_finiteDimensional_central
