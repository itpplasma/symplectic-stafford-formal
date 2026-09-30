import SymplecticStafford.Paper.RightFraction
import SymplecticStafford.Paper.DivisionPencil
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Module.Projective

/-!
# No finite-rank trap (paper Lemma 4.2 and Corollary 4.4)

Let `T` be a simple nondivision domain which is a ring of right fractions of a
simple ring `U`, and let `M` be a simple right `T`-module with Schur division
ring `E = End_T(M)`.  Right multiplication by `τ ∈ T` is `E`-linear
(`rmul τ`), and central scalars `λ ∈ k` act through the central embedding
`centralEnd k : k →+* E`.

* `density`: Jacobson density for finitely many vectors.
* `not_finite_end`: `M` is not finite-dimensional over `E`.
* `no_finite_rank_trap` (Lemma 4.2): for `g ≠ 0` and `b ≠ 0`, the vectors
  `g · ι(u b)` never lie in one finite-dimensional `E`-subspace.
* `exists_injective_rmul`, `exists_linearIndependent_rmul` (Corollary 4.4):
  an `E`-independent family stays independent after right multiplication by a
  suitable `ι(u b)`.

Right `T`-modules are `Tᵐᵒᵖ`-modules: `x · τ` is `op τ • x`.
-/

namespace SymplecticStafford.Paper

open MulOpposite Module

section RightAction

variable {T : Type*} [Ring T] {M : Type*} [AddCommGroup M] [Module Tᵐᵒᵖ M]

/-- Right multiplication by `τ`, as a linear map over the endomorphism ring. -/
def rmul (τ : T) : M →ₗ[Module.End Tᵐᵒᵖ M] M where
  toFun x := op τ • x
  map_add' x y := smul_add _ x y
  map_smul' f x := (f.map_smul (op τ) x).symm

@[simp] lemma rmul_apply (τ : T) (x : M) : rmul τ x = op τ • x := rfl

lemma op_mul_smul (τ σ : T) (x : M) : op (τ * σ) • x = op σ • op τ • x := by
  rw [op_mul, mul_smul]

lemma end_smul_comm (f : Module.End Tᵐᵒᵖ M) (τ : T) (x : M) : op τ • f x = f (op τ • x) :=
  (f.map_smul _ _).symm

variable (k : Type*) [Field k] [Algebra k T]

lemma op_algebraMap_comm (c : k) (r : Tᵐᵒᵖ) :
    op (algebraMap k T c) * r = r * op (algebraMap k T c) := by
  rw [← MulOpposite.algebraMap_apply]
  exact Algebra.commutes c r

/-- The central scalars `k → End_T(M)`, acting by right multiplication. -/
def centralEnd : k →+* Module.End Tᵐᵒᵖ M where
  toFun c :=
    { toFun := fun x => op (algebraMap k T c) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [← mul_smul, ← mul_smul, op_algebraMap_comm] }
  map_one' := by
    ext x
    show op (algebraMap k T 1) • x = x
    rw [map_one, op_one, one_smul]
  map_mul' c d := by
    ext x
    show op (algebraMap k T (c * d)) • x = op (algebraMap k T c) • op (algebraMap k T d) • x
    rw [mul_comm c d, map_mul, op_mul_smul]
  map_zero' := by
    ext x
    show op (algebraMap k T 0) • x = 0
    rw [map_zero, op_zero, zero_smul]
  map_add' c d := by
    ext x
    show op (algebraMap k T (c + d)) • x =
      op (algebraMap k T c) • x + op (algebraMap k T d) • x
    rw [map_add, op_add, add_smul]

lemma centralEnd_apply (c : k) (x : M) :
    centralEnd (M := M) k c x = op (algebraMap k T c) • x := rfl

/-- The central scalars are central in `End_T(M)`. -/
lemma centralEnd_comm (c : k) (f : Module.End Tᵐᵒᵖ M) :
    centralEnd k c * f = f * centralEnd k c := by
  ext x
  exact end_smul_comm f _ x

/-- Right multiplication along a pencil `u₀ + λ u`. -/
lemma rmul_pencil {U : Type*} [Ring U] [Algebra k U] (ι : U →ₐ[k] T) (u₀ u b : U) (l : k)
    (x : M) :
    op (ι ((u₀ + algebraMap k U l * u) * b)) • x =
      op (ι (u₀ * b)) • x + centralEnd k l • (op (ι (u * b)) • x) := by
  simp only [add_mul, map_add, op_add, add_smul, mul_assoc]
  rw [map_mul ι (algebraMap k U l), AlgHom.commutes]
  congr 1
  show _ = op (algebraMap k T l) • _
  rw [← mul_smul, ← op_mul, Algebra.commutes]

end RightAction

section Density

variable {T : Type*} [Ring T] {M : Type*} [AddCommGroup M] [Module Tᵐᵒᵖ M]

/-- The right annihilator of an `E`-subspace, as a right ideal of `T`. -/
def annR (X : Submodule (Module.End Tᵐᵒᵖ M) M) : Submodule Tᵐᵒᵖ T where
  carrier := {τ | ∀ x ∈ X, op τ • x = 0}
  add_mem' {a b} ha hb x hx := by
    rw [op_add, add_smul, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by rw [op_zero, zero_smul]
  smul_mem' σ τ hτ x hx := by
    show op (σ • τ) • x = 0
    rw [MulOpposite.smul_eq_mul_unop, op_mul_smul, hτ x hx, smul_zero]

lemma mem_annR {X : Submodule (Module.End Tᵐᵒᵖ M) M} {τ : T} :
    τ ∈ annR X ↔ ∀ x ∈ X, op τ • x = 0 := Iff.rfl

lemma mem_annR_span {s : Set M} {τ : T} :
    τ ∈ annR (Submodule.span (Module.End Tᵐᵒᵖ M) s) ↔ ∀ x ∈ s, op τ • x = 0 := by
  constructor
  · exact fun h x hx => h x (Submodule.subset_span hx)
  · intro h x hx
    have hle : Submodule.span (Module.End Tᵐᵒᵖ M) s ≤ LinearMap.ker (rmul τ) :=
      Submodule.span_le.mpr fun y hy => LinearMap.mem_ker.mpr (h y hy)
    exact LinearMap.mem_ker.mp (hle hx)

/-- Evaluation `τ ↦ z · τ` on a right ideal. -/
def annEval (X : Submodule (Module.End Tᵐᵒᵖ M) M) (z : M) : annR X →ₗ[Tᵐᵒᵖ] M where
  toFun τ := op (τ : T) • z
  map_add' a b := by
    simp only [Submodule.coe_add, op_add, add_smul]
  map_smul' σ τ := by
    simp only [SetLike.val_smul, RingHom.id_apply, MulOpposite.smul_eq_mul_unop, op_mul_smul,
      op_unop]

lemma annEval_apply (X : Submodule (Module.End Tᵐᵒᵖ M) M) (z : M) (τ : annR X) :
    annEval X z τ = op (τ : T) • z := rfl

variable [IsSimpleModule Tᵐᵒᵖ M]

/-- **Jacobson density.**  If `y` is not in the `E`-span of the finite set `s`,
some `τ` kills `s` but not `y`. -/
theorem density (s : Finset M) :
    ∀ y ∉ Submodule.span (Module.End Tᵐᵒᵖ M) (s : Set M),
      ∃ τ ∈ annR (Submodule.span (Module.End Tᵐᵒᵖ M) (s : Set M)), op τ • y ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    refine ⟨1, ?_, ?_⟩
    · intro x hx
      rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
      rw [hx, smul_zero]
    · rw [op_one, one_smul]
      rintro rfl
      exact hy (Submodule.zero_mem _)
  | @insert x s hxs ih =>
    intro y hy
    rw [Finset.coe_insert] at hy ⊢
    by_cases hx : x ∈ Submodule.span (Module.End Tᵐᵒᵖ M) (s : Set M)
    · rw [Submodule.span_insert_eq_span hx] at hy ⊢
      exact ih y hy
    · set X := Submodule.span (Module.End Tᵐᵒᵖ M) (s : Set M) with hX
      have hsurj : Function.Surjective (annEval X x) := by
        rw [← LinearMap.range_eq_top]
        refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ?_
        obtain ⟨τ, hτ, hτx⟩ := ih x hx
        intro hbot
        apply hτx
        have hmem : annEval X x ⟨τ, hτ⟩ ∈ LinearMap.range (annEval X x) :=
          LinearMap.mem_range_self _ _
        rw [hbot, Submodule.mem_bot] at hmem
        exact hmem
      by_contra hcon
      push_neg at hcon
      have hle : LinearMap.ker (annEval X x) ≤ LinearMap.ker (annEval X y) := by
        intro τ hτ
        rw [LinearMap.mem_ker] at hτ ⊢
        apply hcon
        rw [mem_annR_span]
        intro z hz
        rcases hz with rfl | hz
        · exact hτ
        · exact (mem_annR_span.mp τ.2) z hz
      let f : Module.End Tᵐᵒᵖ M :=
        ((LinearMap.ker (annEval X x)).liftQ (annEval X y) hle).comp
          ((annEval X x).quotKerEquivOfSurjective hsurj).symm.toLinearMap
      have hf : ∀ τ : annR X, f (op (τ : T) • x) = op (τ : T) • y := by
        intro τ
        show f (annEval X x τ) = annEval X y τ
        simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
      apply hy
      have hmem : y - f x ∈ X := by
        by_contra hnot
        obtain ⟨τ, hτ, hne⟩ := ih _ hnot
        apply hne
        rw [smul_sub, end_smul_comm, hf ⟨τ, hτ⟩, sub_self]
      rw [Submodule.mem_span_insert]
      exact ⟨f, y - f x, hmem, by rw [Module.End.smul_def]; abel⟩

/-- **Jacobson density, family form.** -/
theorem exists_right_annihilator {ι : Type*} [Finite ι] (x : ι → M) (y : M)
    (hy : y ∉ Submodule.span (Module.End Tᵐᵒᵖ M) (Set.range x)) :
    ∃ τ : T, (∀ i, op τ • x i = 0) ∧ op τ • y ≠ 0 := by
  classical
  haveI := Fintype.ofFinite ι
  have hs : ((Finset.univ.image x : Finset M) : Set M) = Set.range x := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [← hs] at hy
  obtain ⟨τ, hτ, hτy⟩ := density _ y hy
  rw [hs, mem_annR_span] at hτ
  exact ⟨τ, fun i => hτ _ ⟨i, rfl⟩, hτy⟩

/-- A simple ring acts faithfully on a nonzero module. -/
lemma faithful [IsSimpleRing T] {τ : T} (h : ∀ m : M, op τ • m = 0) : τ = 0 := by
  haveI := IsSimpleModule.nontrivial Tᵐᵒᵖ M
  by_contra hτ
  let I : TwoSidedIdeal T := TwoSidedIdeal.mk' {σ | ∀ m : M, op σ • m = 0}
    (fun m => by rw [op_zero, zero_smul])
    (fun ha hb m => by rw [op_add, add_smul, ha m, hb m, add_zero])
    (fun ha m => by rw [op_neg, neg_smul, ha m, neg_zero])
    (fun hb m => by rw [op_mul_smul, hb])
    (fun ha m => by rw [op_mul_smul, ha, smul_zero])
  have h1 := IsSimpleRing.one_mem_of_ne_zero_mem I hτ ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ τ).mpr h)
  rw [TwoSidedIdeal.mem_mk'] at h1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  apply hm
  have := h1 m
  rwa [op_one, one_smul] at this

/-- In a simple module over a nondivision domain every vector has a nonzero
annihilator. -/
lemma exists_ann [IsDomain T] (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) {y : M} (hy : y ≠ 0) :
    ∃ σ : T, σ ≠ 0 ∧ op σ • y = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ₀, hτ₀, hnu⟩ := hnd
  have hne : op τ₀ • y ≠ 0 := hcon τ₀ hτ₀
  have hspan := IsSimpleModule.span_singleton_eq_top Tᵐᵒᵖ hne
  have hy' : y ∈ Submodule.span Tᵐᵒᵖ {op τ₀ • y} := hspan ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hy'
  have h1 : τ₀ * unop r = 1 := by
    by_contra h
    apply hcon (τ₀ * unop r - 1) (sub_ne_zero.mpr h)
    rw [op_sub, sub_smul, op_mul_smul, op_unop, hr, op_one, one_smul, sub_self]
  apply hnu
  have h2 : unop r * τ₀ = 1 := by
    have : τ₀ * (unop r * τ₀ - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, h1, one_mul, mul_one, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ₀)
  exact ⟨⟨τ₀, unop r, h1, h2⟩, rfl⟩

/-- A simple module over a simple nondivision domain is not finite-dimensional
over its Schur division ring. -/
theorem not_finite_end [IsSimpleRing T] [IsDomain T] (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) :
    ¬ Module.Finite (Module.End Tᵐᵒᵖ M) M := by
  classical
  intro hfin
  haveI := IsSimpleModule.nontrivial Tᵐᵒᵖ M
  have hex : ∃ n, ∃ s : Finset M, s.card = n ∧
      Submodule.span (Module.End Tᵐᵒᵖ M) (s : Set M) = ⊤ := by
    obtain ⟨s, hs⟩ := hfin.fg_top
    exact ⟨_, s, rfl, hs⟩
  obtain ⟨s, hs, hspan⟩ := Nat.find_spec hex
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hspan
    exact bot_ne_top hspan
  obtain ⟨x, hx⟩ := hsne
  have hmin : Submodule.span (Module.End Tᵐᵒᵖ M) ((s.erase x : Finset M) : Set M) ≠ ⊤ := by
    intro h
    have h1 := Nat.find_min' hex ⟨s.erase x, rfl, h⟩
    rw [Finset.card_erase_of_mem hx] at h1
    have h2 : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hins : Submodule.span (Module.End Tᵐᵒᵖ M)
      (insert x ((s.erase x : Finset M) : Set M)) = ⊤ := by
    rw [← Finset.coe_insert, Finset.insert_erase hx, hspan]
  have hxs : x ∉ Submodule.span (Module.End Tᵐᵒᵖ M) ((s.erase x : Finset M) : Set M) := by
    intro h
    apply hmin
    rw [← hins, Submodule.span_insert_eq_span h]
  obtain ⟨τ, hτ, hτx⟩ := density (s.erase x) x hxs
  obtain ⟨σ, hσ, hσx⟩ := exists_ann hnd hτx
  have hτσ : τ * σ = 0 := by
    apply faithful (M := M)
    intro m
    have hm : m ∈ Submodule.span (Module.End Tᵐᵒᵖ M)
        (insert x ((s.erase x : Finset M) : Set M)) := by
      rw [hins]; exact Submodule.mem_top
    obtain ⟨f, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hm
    rw [op_mul_smul, smul_add, hτ z hz, add_zero, Module.End.smul_def, end_smul_comm,
      end_smul_comm, hσx, map_zero]
  rcases mul_eq_zero.mp hτσ with h | h
  · apply hτx
    rw [h, op_zero, zero_smul]
  · exact hσ h

end Density

section NoFiniteRank

variable {U : Type*} [Ring U] {T : Type*} [Ring T]
variable {M : Type*} [AddCommGroup M] [Module Tᵐᵒᵖ M] [IsSimpleModule Tᵐᵒᵖ M]

/-- **Lemma 4.2 (no finite-rank trap).**  For `g ≠ 0` and `b ≠ 0`, the vectors
`g · ι(u b)`, `u ∈ U`, do not all lie in a finite-dimensional subspace over the
Schur division ring `End_T(M)`. -/
theorem no_finite_rank_trap [IsSimpleRing U] [IsSimpleRing T] [IsDomain T]
    (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) (ι : U →+* T) {S : Submonoid U}
    (hfrac : IsRightFractions S ι) {g : M} (hg : g ≠ 0) {b : U} (hb : b ≠ 0)
    (Y : Submodule (Module.End Tᵐᵒᵖ M) M) [Module.Finite (Module.End Tᵐᵒᵖ M) Y] :
    ¬ ∀ u : U, op (ι (u * b)) • g ∈ Y := by
  classical
  intro hY
  apply not_finite_end (M := M) hnd
  -- (i) `1` is a sum of products `α b c`.
  have h1 : (1 : U) ∈ AddSubgroup.closure (Set.univ * {b} * Set.univ) :=
    TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure.mp
      (IsSimpleRing.one_mem_of_ne_zero_mem _ hb
        (TwoSidedIdeal.subset_span (Set.mem_singleton b)))
  have key : ∀ y ∈ AddSubgroup.closure (Set.univ * {b} * Set.univ : Set U),
      ∃ W : Submodule (Module.End Tᵐᵒᵖ M) M, Module.Finite (Module.End Tᵐᵒᵖ M) W ∧
        ∀ u, op (ι (u * y)) • g ∈ W := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨p, ⟨α, -, b', hb', rfl⟩, c, -, rfl⟩ := hx
      rw [Set.mem_singleton_iff] at hb'
      subst hb'
      refine ⟨Y.map (rmul (ι c)), inferInstance, fun u => ?_⟩
      refine ⟨op (ι (u * α * b')) • g, hY (u * α), ?_⟩
      simp only [rmul_apply, ← op_mul_smul, ← map_mul, mul_assoc]
    | zero =>
      refine ⟨⊥, inferInstance, fun u => ?_⟩
      rw [mul_zero, map_zero, op_zero, zero_smul]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨W₁, hW₁, h₁⟩ := hx
      obtain ⟨W₂, hW₂, h₂⟩ := hy
      refine ⟨W₁ ⊔ W₂, inferInstance, fun u => ?_⟩
      rw [mul_add, map_add, op_add, add_smul]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ u)) (Submodule.mem_sup_right (h₂ u))
    | neg x _ hx =>
      obtain ⟨W, hW, h⟩ := hx
      refine ⟨W, hW, fun u => ?_⟩
      rw [mul_neg, map_neg, op_neg, neg_smul]
      exact Submodule.neg_mem _ (h u)
  obtain ⟨W₁, hW₁, hW₁g⟩ := key 1 h1
  set W := Submodule.span (Module.End Tᵐᵒᵖ M) (Set.range fun u : U => op (ι u) • g) with hW
  have hWle : W ≤ W₁ := Submodule.span_le.mpr (by
    rintro _ ⟨u, rfl⟩
    simpa using hW₁g u)
  haveI : Module.Finite (Module.End Tᵐᵒᵖ M) W := Submodule.finiteDimensional_of_le hWle
  -- (ii) `W` is stable under `ι U`, then under all of `T`.
  have hWu : ∀ u : U, ∀ w ∈ W, op (ι u) • w ∈ W := by
    intro u
    have : W ≤ W.comap (rmul (ι u)) := Submodule.span_le.mpr (by
      rintro _ ⟨u', rfl⟩
      refine Submodule.mem_comap.mpr (Submodule.subset_span ⟨u' * u, ?_⟩)
      simp only [rmul_apply, map_mul, op_mul_smul])
    exact fun w hw => this hw
  have hWT : ∀ τ : T, ∀ w ∈ W, op τ • w ∈ W := by
    intro τ w hw
    obtain ⟨a, s, hs, hτ⟩ := hfrac.surj τ
    have hunit : IsUnit (op (ι s)) := (hfrac.isUnit s hs).op
    let r : W →ₗ[Module.End Tᵐᵒᵖ M] W := (rmul (ι s)).restrict (fun w hw => hWu s w hw)
    have hrinj : Function.Injective r := by
      intro w₁ w₂ h
      apply Subtype.ext
      have h' : op (ι s) • (w₁ : M) = op (ι s) • (w₂ : M) := congrArg Subtype.val h
      exact hunit.smul_left_cancel.mp h'
    obtain ⟨w', hw'⟩ := (LinearMap.injective_iff_surjective.mp hrinj) ⟨op (ι a) • w, hWu a w hw⟩
    have h2 : op (ι s) • (w' : M) = op (ι a) • w := congrArg Subtype.val hw'
    have : op τ • w = w' := by
      apply hunit.smul_left_cancel.mp
      rw [h2, ← op_mul_smul, hτ]
    rw [this]
    exact w'.2
  let W' : Submodule Tᵐᵒᵖ M :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun r w hw => by
        have := hWT (unop r) w hw
        rwa [op_unop] at this }
  have hgW : g ∈ W' := Submodule.subset_span ⟨1, by simp⟩
  have htop : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left fun h => by
    rw [h, Submodule.mem_bot] at hgW
    exact hg hgW
  refine Module.Finite.of_surjective W.subtype fun m => ⟨⟨m, ?_⟩, rfl⟩
  have : m ∈ W' := htop ▸ Submodule.mem_top
  exact this

variable {k : Type*} [Field k] [Algebra k U] [Algebra k T]

/-- **Corollary 4.4, linear-map form.**  If `P : D → M` is injective with `D`
finite-dimensional over `E = End_T(M)`, then for some `u ∈ U` the map
`d ↦ P(d) · ι(u b)` is still injective. -/
theorem exists_injective_rmul [Infinite k] [IsSimpleRing U] [IsSimpleRing T] [IsDomain T]
    (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) (ι : U →ₐ[k] T) {S : Submonoid U}
    (hfrac : IsRightFractions S (ι : U →+* T))
    {D : Type*} [AddCommGroup D] [Module (Module.End Tᵐᵒᵖ M) D]
    [Module.Finite (Module.End Tᵐᵒᵖ M) D]
    (P : D →ₗ[Module.End Tᵐᵒᵖ M] M) (hP : Function.Injective P) {b : U} (hb : b ≠ 0) :
    ∃ u : U, Function.Injective ((rmul (ι (u * b))).comp P) := by
  classical
  by_contra hcon
  push_neg at hcon
  let Q : U → D →ₗ[Module.End Tᵐᵒᵖ M] M := fun u => (rmul (ι (u * b))).comp P
  let ρ : U → ℕ := fun u => finrank (Module.End Tᵐᵒᵖ M) (LinearMap.range (Q u))
  have hbound : ∀ u, ρ u ≤ finrank (Module.End Tᵐᵒᵖ M) D := fun u => LinearMap.finrank_range_le _
  have step : ∀ u₀, ∃ u', ρ u₀ < ρ u' := by
    intro u₀
    obtain ⟨d₀, hd₀Q, hd₀⟩ : ∃ d₀, Q u₀ d₀ = 0 ∧ d₀ ≠ 0 := by
      have := hcon u₀
      rw [injective_iff_map_eq_zero] at this
      push_neg at this
      exact this
    have hg : P d₀ ≠ 0 := fun h => hd₀ (hP (by rw [map_zero]; exact h))
    set Y₀ := LinearMap.range (Q u₀) with hY₀
    obtain ⟨u, hu⟩ : ∃ u, op (ι (u * b)) • P d₀ ∉ Y₀ := by
      by_contra h
      push_neg at h
      exact no_finite_rank_trap hnd (ι : U →+* T) hfrac hg hb Y₀ h
    set hv := op (ι (u * b)) • P d₀ with hhv
    obtain ⟨s₀, hs₀⟩ := (Q u₀).rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_rangeRestrict _)
    have hs₀' : ∀ y : Y₀, Q u₀ (s₀ y) = y := fun y =>
      congrArg Subtype.val (LinearMap.congr_fun hs₀ y)
    let P' : Y₀ × Module.End Tᵐᵒᵖ M →ₗ[Module.End Tᵐᵒᵖ M] M :=
      Y₀.subtype.coprod (LinearMap.toSpanSingleton _ M hv)
    let W' : Y₀ × Module.End Tᵐᵒᵖ M →ₗ[Module.End Tᵐᵒᵖ M] M :=
      ((Q u).comp s₀).comp (LinearMap.fst _ Y₀ (Module.End Tᵐᵒᵖ M))
    have hP' : Function.Injective P' := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨y, a⟩ hya
      have hya' : (y : M) + a • hv = 0 := hya
      by_cases ha : a = 0
      · rw [ha, zero_smul, add_zero] at hya'
        have hy : y = 0 := Subtype.ext hya'
        rw [hy, ha]
        rfl
      · exfalso
        apply hu
        have : hv = a⁻¹ • -(y : M) := by
          calc hv = a⁻¹ • (a • hv) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
            _ = a⁻¹ • -(y : M) := by rw [eq_neg_of_add_eq_zero_right hya']
        rw [← hhv, this]
        exact Y₀.smul_mem _ (Y₀.neg_mem y.2)
    have hfin := pencil_ker_finite (centralEnd k) (centralEnd_comm k) P' W' hP'
    obtain ⟨l, hl⟩ := (hfin.union (Set.finite_singleton (0 : k))).exists_notMem
    have hl0 : l ≠ 0 := fun h0 => hl (Or.inr h0)
    have hlB : ¬ ∃ d, d ≠ 0 ∧ P' d + centralEnd k l • W' d = 0 := fun h => hl (Or.inl h)
    refine ⟨u₀ + algebraMap k U l * u, ?_⟩
    set u' := u₀ + algebraMap k U l * u
    have hQ' : ∀ d, Q u' d = Q u₀ d + centralEnd k l • Q u d := fun d =>
      rmul_pencil k ι u₀ u b l (P d)
    let L : Y₀ × Module.End Tᵐᵒᵖ M →ₗ[Module.End Tᵐᵒᵖ M] D :=
      s₀.comp (LinearMap.fst _ Y₀ (Module.End Tᵐᵒᵖ M)) +
        (LinearMap.toSpanSingleton _ D (centralEnd k (l⁻¹) • d₀)).comp
          (LinearMap.snd _ Y₀ (Module.End Tᵐᵒᵖ M))
    let F := (Q u').comp L
    have hF : ∀ p, F p = P' p + centralEnd k l • W' p := by
      rintro ⟨y, a⟩
      have e1 : Q u' (s₀ y) = y + centralEnd k l • Q u (s₀ y) := by rw [hQ', hs₀']
      have e2 : Q u' d₀ = centralEnd k l • hv := by rw [hQ', hd₀Q, zero_add]; rfl
      show Q u' (s₀ y + a • (centralEnd k (l⁻¹) • d₀)) =
        ((y : M) + a • hv) + centralEnd k l • Q u (s₀ y)
      rw [map_add, map_smul, map_smul, e1, e2, smul_smul (centralEnd k (l⁻¹)), ← map_mul,
        inv_mul_cancel₀ hl0, map_one, one_smul]
      abel
    have hFinj : Function.Injective F := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra hp0
      exact hlB ⟨p, hp0, by rw [← hF]; exact hp⟩
    let F' := (Q u').rangeRestrict.comp L
    have hF'inj : Function.Injective F' := by
      intro p₁ p₂ h
      exact hFinj (congrArg Subtype.val h)
    have hle := LinearMap.finrank_le_finrank_of_injective hF'inj
    rw [Module.finrank_prod, Module.finrank_self] at hle
    exact Nat.lt_of_succ_le hle
  have hgrow : ∀ n : ℕ, ∃ u, n ≤ ρ u := by
    intro n
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      obtain ⟨u', hu'⟩ := step u
      exact ⟨u', by omega⟩
  obtain ⟨u, hu⟩ := hgrow (finrank (Module.End Tᵐᵒᵖ M) D + 1)
  have := hbound u
  omega

/-- **Corollary 4.4.**  An `E`-linearly independent finite family stays
independent after right multiplication by `ι(u b)` for a suitable `u ∈ U`. -/
theorem exists_linearIndependent_rmul [Infinite k] [IsSimpleRing U] [IsSimpleRing T]
    [IsDomain T] (hnd : ∃ τ : T, τ ≠ 0 ∧ ¬ IsUnit τ) (ι : U →ₐ[k] T) {S : Submonoid U}
    (hfrac : IsRightFractions S (ι : U →+* T)) {n : Type*} [Finite n] (v : n → M)
    (hv : LinearIndependent (Module.End Tᵐᵒᵖ M) v) {b : U} (hb : b ≠ 0) :
    ∃ u : U, LinearIndependent (Module.End Tᵐᵒᵖ M) (fun i => op (ι (u * b)) • v i) := by
  obtain ⟨u, hu⟩ := exists_injective_rmul hnd ι hfrac
    (Finsupp.linearCombination (Module.End Tᵐᵒᵖ M) v) hv hb
  refine ⟨u, ?_⟩
  have : Finsupp.linearCombination (Module.End Tᵐᵒᵖ M) (fun i => op (ι (u * b)) • v i) =
      (rmul (ι (u * b))).comp (Finsupp.linearCombination (Module.End Tᵐᵒᵖ M) v) := by
    ext i
    simp
  show Function.Injective _
  rw [this]
  exact hu

end NoFiniteRank

end SymplecticStafford.Paper
