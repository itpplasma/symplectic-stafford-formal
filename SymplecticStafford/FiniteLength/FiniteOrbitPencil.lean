import SymplecticStafford.FiniteLength.ActivatedFiniteLength
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite-orbit pencils for a finite-length top

This file removes one avoidable opacity from the activated-pencil interface.
The exceptional set is derived from a finite orbit basis in the actual top,
rather than being supplied as a `finite_nongenerating` field or as a list of
pre-existing division-ring blocks.  The only top input is an orbit map into a
`K`-linear space, a comparison of top generation with the actual right-cyclic
predicate, and a finite orbit basis for a cyclic vector.  The determinant
calculation is over `K`; all coefficients acting on the module remain in the
original (possibly noncommutative) ring.

The finite-orbit-basis hypothesis is intentional.  Finite length over an
arbitrary ring does not by itself make the top finite-dimensional over the
chosen scalar field, nor does it make an unrelated scalar action central.
Those missing hypotheses cannot be silently inferred here.
-/

namespace SymplecticStafford.FiniteLength

open Module

universe u v w

section Orbit

variable {R : Type u} {M : Type v} {K : Type w}
variable [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [Field K] [Module K M] [Infinite K]

/-- The `K`-linear span of an orbit under a supplied family of linear maps.
The span formulation is what permits a finite orbit basis to be used without
pretending that a noncommutative coefficient ring is a field.
-/
def OrbitSpanTop {A Q : Type*} [AddCommGroup Q] [Module K Q]
    (act : A → Q →ₗ[K] Q) (q : Q) : Prop :=
  Submodule.span K (Set.range (fun a => act a q)) = ⊤

private theorem orbit_span_of_basis
    {A Q : Type*} [AddCommGroup Q] [Module K Q]
    {n : Nat} (b : Basis (Fin n) K Q)
    (act : A → Q →ₗ[K] Q) (q : Q) (c : Fin n → A)
    (hbc : ∀ i, act (c i) q = b i) :
    OrbitSpanTop act q := by
  unfold OrbitSpanTop
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact Submodule.subset_span ⟨c i, hbc i⟩

private theorem finite_orbit_pencil_exceptions
    {A Q : Type*} [AddCommGroup Q] [Module K Q]
    {n : Nat} (b : Basis (Fin n) K Q)
    (act : A → Q →ₗ[K] Q) (q q' : Q) (c : Fin n → A)
    (hbc : ∀ i, act (c i) q = b i) :
    Set.Finite {z : K | ¬ OrbitSpanTop act (q + z • q')} := by
  classical
  let C : Matrix (Fin n) (Fin n) K := fun i j =>
    b.repr (act (c j) q') i
  have hbad : (Set.Finite {z : K |
      Matrix.det ((1 : Matrix (Fin n) (Fin n) K) + z • C) = 0}) := by
    exact finite_matrix_pencil_exceptions
      (1 : Matrix (Fin n) (Fin n) K) C (by simp)
  apply hbad.subset
  intro z hz
  by_contra hdet
  apply hz
  have hvec : ∀ j, act (c j) (q + z • q') =
      b j + z • act (c j) q' := by
    intro j
    rw [map_add, map_smul, hbc]
  have hmat : b.toMatrix
      (fun j => act (c j) (q + z • q')) =
      (1 : Matrix (Fin n) (Fin n) K) + z • C := by
    ext i j
    rw [Basis.toMatrix_apply, hvec j]
    rw [map_add, map_smul, b.repr_self]
    rw [Finsupp.add_apply, Finsupp.smul_apply, Matrix.add_apply,
      Matrix.one_apply, Matrix.smul_apply]
    simp only [C, smul_eq_mul]
    by_cases h : i = j <;> simp [h]
  have hunit : IsUnit (b.det
      (fun j => act (c j) (q + z • q'))) := by
    rw [Basis.det_apply, hmat]
    exact isUnit_iff_ne_zero.mpr hdet
  have hspan : Submodule.span K (Set.range
      (fun j => act (c j) (q + z • q'))) = ⊤ :=
    (b.is_basis_iff_det.mpr hunit).2
  unfold OrbitSpanTop
  apply top_unique
  rw [← hspan]
  exact Submodule.span_mono (by
    rintro x ⟨j, rfl⟩
    exact ⟨c j, rfl⟩)

end Orbit

section Activated

variable {R : Type u} {M : Type v} {K : Type w}
variable [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [Field K] [Module K M] [Infinite K]

/-- A top comparison which derives finite pencil exceptions from actual finite
orbit data.  `Q` need not be commutative or an algebra; only its scalar-field
module structure is used by the determinant calculation. -/
theorem finite_nongenerating_scalars_of_finite_orbit_basis
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (top : M →ₗ[K] Q)
    (act : (Rᵐᵒᵖ) → Q →ₗ[K] Q)
    (top_cyclic_iff : ∀ m : M,
      RightCyclic (R := R) m ↔ OrbitSpanTop act (top m))
    (orbit_basis : ∀ m : M, RightCyclic (R := R) m →
      ∃ n : Nat, ∃ b : Basis (Fin n) K Q,
        ∃ c : Fin n → Rᵐᵒᵖ,
          ∀ i, act (c i) (top m) = b i)
    (v u : M) (hv : RightCyclic (R := R) v) :
    Set.Finite {z : K | ¬ RightCyclic (R := R) (v + z • u)} := by
  obtain ⟨n, b, c, hbc⟩ := orbit_basis v hv
  have hfinite := finite_orbit_pencil_exceptions b act (top v) (top u) c hbc
  apply hfinite.subset
  intro z hz hcyc
  apply hz
  apply (top_cyclic_iff (v + z • u)).2
  simpa only [map_add, map_smul] using hcyc

/-- Full activated conclusion from finite orbit data.  The last conjunct is
the original ordered right-action identity; no commutation of `b` and `l` is
introduced. -/
theorem exists_activated_right_cyclic_of_finite_orbit_basis
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    {n : Nat} (F : RightMinimalSupportFiltration (R := R) (M := M)
      (α := Unit) n)
    (top : M →ₗ[K] Q)
    (act : (Rᵐᵒᵖ) → Q →ₗ[K] Q)
    (top_cyclic_iff : ∀ m : M,
      RightCyclic (R := R) m ↔ OrbitSpanTop act (top m))
    (orbit_basis : ∀ m : M, RightCyclic (R := R) m →
      ∃ n : Nat, ∃ b : Basis (Fin n) K Q,
        ∃ c : Fin n → Rᵐᵒᵖ,
          ∀ i, act (c i) (top m) = b i)
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
  letI : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have hbad := finite_nongenerating_scalars_of_finite_orbit_basis
    top act top_cyclic_iff orbit_basis v u hv
  have hall : (forbidden ∪ {z : K |
      ¬ RightCyclic (R := R) (v + z • u)}).Finite :=
    hforbidden.union hbad
  obtain ⟨z, hz⟩ := (Set.infinite_univ.sdiff hall).nonempty
  refine ⟨z, ?_, ?_, ?_⟩
  · intro h
    exact hz.2 (Or.inl h)
  · by_contra h
    exact hz.2 (Or.inr h)
  · exact pencil_right_action_add rightAction rightAction_add
      central_smul_right v u e b l vL_zero e_decomp z

end Activated

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.finite_nongenerating_scalars_of_finite_orbit_basis
#print axioms SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_finite_orbit_basis
