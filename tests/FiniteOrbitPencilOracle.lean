module

public import SymplecticStafford.FiniteLength.FiniteOrbitPencil
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic

@[expose] public section

/-!
# Independent oracle for the finite-orbit M07 lane

This replay uses a genuine noncommutative coefficient *type* (`ℚᵐᵒᵖ`) in
the orbit map, while the determinant is taken only in the central scalar
field.  The orbit-basis certificate is constructed from the one-dimensional
top, so finite exceptional scalars are derived rather than supplied.
-/

namespace SymplecticStafford.FiniteLength.FiniteOrbitPencilOracle

abbrev K := ℚ

noncomputable def ratAct (r : ℚᵐᵒᵖ) : ℚ →ₗ[ℚ] ℚ :=
  { toFun := fun x => r.unop * x
    map_add' := by intro x y; ring
    map_smul' := by intro a x; dsimp; ring }

theorem ratAct_apply (r : ℚᵐᵒᵖ) (x : ℚ) : ratAct r x = r.unop * x := rfl

theorem rat_orbit_span_iff (x : ℚ) :
    OrbitSpanTop ratAct x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    subst x
    have hle : Submodule.span ℚ (Set.range (fun r : ℚᵐᵒᵖ => ratAct r 0)) ≤
        (⊥ : Submodule ℚ ℚ) := by
      apply Submodule.span_le.mpr
      rintro y ⟨r, rfl⟩
      simp [ratAct]
    have htopbot : (⊤ : Submodule ℚ ℚ) ≤ ⊥ := by
      rw [← hx]
      exact hle
    have honebot : (1 : ℚ) ∈ (⊥ : Submodule ℚ ℚ) :=
      htopbot (by simp)
    exact one_ne_zero ((Submodule.mem_bot ℚ).mp honebot)
  · intro hx
    unfold OrbitSpanTop
    apply top_unique
    intro y hy
    have h1 : (1 : ℚ) ∈
        Submodule.span ℚ (Set.range (fun r : ℚᵐᵒᵖ => ratAct r x)) := by
      apply Submodule.subset_span
      refine ⟨MulOpposite.op x⁻¹, ?_⟩
      simp [ratAct, hx]
    simpa using (Submodule.smul_mem
      (Submodule.span ℚ (Set.range (fun r : ℚᵐᵒᵖ => ratAct r x))) y h1)

theorem rat_orbit_basis (x : ℚ)
    (hx : RightCyclic (R := ℚ) x) :
    ∃ n : Nat, ∃ b : Module.Basis (Fin n) ℚ ℚ,
      ∃ c : Fin n → ℚᵐᵒᵖ,
        ∀ i, ratAct (c i) x = b i := by
  have hx0 : x ≠ 0 := by
    intro hzero
    obtain ⟨r, hr⟩ := hx 1
    rw [hzero] at hr
    simp at hr
  let b : Module.Basis (Fin 1) ℚ ℚ :=
    (Module.Basis.singleton Unit ℚ).reindex (Fintype.equivFin Unit)
  refine ⟨1, b, (fun _ => MulOpposite.op x⁻¹), ?_⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change x⁻¹ * x = b 0
  have he : (Fintype.equivFin Unit).symm (0 : Fin 1) = () :=
    Subsingleton.elim _ _
  rw [show b 0 = 1 by
    change ((Module.Basis.singleton Unit ℚ).reindex
      (Fintype.equivFin Unit)) 0 = 1
    rw [Module.Basis.reindex_apply, he]
    exact Module.Basis.singleton_apply Unit ℚ ()]
  simp [hx0]

example (v u : ℚ) (hv : RightCyclic (R := ℚ) v) :
    Set.Finite {z : ℚ | ¬ RightCyclic (R := ℚ) (v + z • u)} := by
  exact finite_nongenerating_scalars_of_finite_orbit_basis
    (top := LinearMap.id) (act := ratAct)
    (top_cyclic_iff := by
      intro m
      simpa [rat_orbit_span_iff] using
        (show RightCyclic (R := ℚ) m ↔ m ≠ 0 from by
          constructor
          · intro h hm; obtain ⟨r, hr⟩ := h 1; rw [hm] at hr; simp at hr
          · intro hm y; refine ⟨MulOpposite.op (m⁻¹ * y), ?_⟩
            change m * (m⁻¹ * y) = y
            simp [hm]))
    (orbit_basis := rat_orbit_basis) v u hv

end SymplecticStafford.FiniteLength.FiniteOrbitPencilOracle
