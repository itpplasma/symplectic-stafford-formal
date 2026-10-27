module

public import SymplecticStafford.FiniteLength.IsotypicBlocks
public import SymplecticStafford.FiniteLength.MatrixPencil
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

/-!
# A positive finite-dimensional central-field pencil theorem

This is a genuine positive replacement for the missing arbitrary division
ring argument.  The block relation is assumed to be represented by a split
`K`-linear pencil on a finite-dimensional coefficient space.  A determinant
over the central field then proves finiteness, while the block coefficients
and the target may still carry an unrelated division-ring structure.

The split realization is the exact extra hypothesis: for a central finite
dimensional division algebra, it is supplied by viewing the coefficient and
block spaces as finite-dimensional `K`-spaces.  No such realization is
asserted for an arbitrary division ring or a noncentral scalar embedding.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section

variable {K : Type u} {E : Type v} {V : Type w} {P : Type*}
variable [Field K] [Infinite K] [DivisionRing E]
variable [AddCommGroup V] [Module K V] [Module E V]
variable [AddCommGroup P] [Module K P] [FiniteDimensional K P]
variable {ι : Type*}

/-- A split finite-dimensional central-field realization of a block pencil.

`realization` identifies block independence with injectivity of the displayed
`K`-linear pencil.  `retract` makes the initial member split-injective; the
same retract detects every singular member after composition.
-/
theorem finite_bad_of_split_central_pencil
    (block : K → ι → V)
    (base : P →ₗ[K] V) (direction : P →ₗ[K] V)
    (retract : V →ₗ[K] P)
    (split : retract.comp base = LinearMap.id)
    (realization : ∀ z : K,
      LinearIndependent E (block z) ↔
        Function.Injective (base + z • direction)) :
    Set.Finite {z : K | ¬ LinearIndependent E (block z)} := by
  classical
  let b : Module.Basis (Fin (Module.finrank K P)) K P := Module.finBasis K P
  let A : Matrix (Fin (Module.finrank K P)) (Fin (Module.finrank K P)) K :=
    LinearMap.toMatrix b b (retract.comp base)
  let C : Matrix (Fin (Module.finrank K P)) (Fin (Module.finrank K P)) K :=
    LinearMap.toMatrix b b (retract.comp direction)
  have hA : Matrix.det A ≠ 0 := by
    have hAid : A = 1 := by
      simp [A, split]
    rw [hAid]
    simp
  have hroot : Set.Finite {z : K | Matrix.det (A + z • C) = 0} :=
    finite_matrix_pencil_exceptions A C hA
  apply hroot.subset
  intro z hz
  by_contra hnot
  apply hz
  have hdet : Matrix.det
      (LinearMap.toMatrix b b (retract.comp (base + z • direction))) ≠ 0 := by
    have hmat : LinearMap.toMatrix b b
        (retract.comp (base + z • direction)) = A + z • C := by
      ext i j
      simp [A, C, LinearMap.toMatrix_apply, LinearMap.comp_apply,
        LinearMap.map_add, Matrix.add_apply, Matrix.smul_apply]
    rw [hmat]
    exact hnot
  have hcompker : (retract.comp (base + z • direction)).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hxne
    have hdet' : LinearMap.det (retract.comp
        (base + z • direction)) ≠ 0 := by
      rw [← LinearMap.det_toMatrix b]
      exact hdet
    have hzero : LinearMap.det (retract.comp
        (base + z • direction)) = 0 :=
      (LinearMap.det_eq_zero_iff_ker_ne_bot).2 (by
        intro hker
        exact hxne ((LinearMap.ker_eq_bot'.mp hker) x hx))
    apply hdet
    rw [LinearMap.det_toMatrix b]
    exact (hdet' hzero).elim
  have hpker : (base + z • direction).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply (LinearMap.ker_eq_bot'.mp hcompker) x
    simp [LinearMap.comp_apply, hx]
  exact (realization z).mpr (LinearMap.ker_eq_bot.mp hpker)

/-! The dependent finite-block form used by the isotypic consumer. -/

section Isotypic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [Module K M]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {EJ : J → Type*} [∀ j, DivisionRing (EJ j)]
variable {QJ PJ : J → Type*}
variable [∀ j, AddCommGroup (QJ j)] [∀ j, Module K (QJ j)]
variable [∀ j, Module (EJ j) (QJ j)]
variable [∀ j, AddCommGroup (PJ j)] [∀ j, Module K (PJ j)]
variable [∀ j, FiniteDimensional K (PJ j)]
variable {r : J → Nat}

/-- Finiteness of repeated-block failures from split central-field
realizations, one finite-dimensional coefficient space for each isotypic
factor. -/
theorem finite_isotypic_bad_of_split_central_pencils
    (top : M →+ ((j : J) → (Fin (r j) → QJ j)))
    (base direction : ∀ j, M → M → (PJ j →ₗ[K] QJ j))
    (retract : ∀ j, M → M → (QJ j →ₗ[K] PJ j))
    (split : ∀ (j : J) (x y : M),
      (retract j x y).comp (base j x y) = LinearMap.id)
    (realization : ∀ (j : J) (x y : M) (z : K),
      LinearIndependent (EJ j) (fun i => top (x + z • y) j i) ↔
        Function.Injective (base j x y + z • direction j x y))
    (x y : M) :
    Set.Finite {z : K | ¬ ∀ j, LinearIndependent (EJ j)
      (fun i => top (x + z • y) j i)} := by
  classical
  have hbad : ∀ j : J, Set.Finite {z : K |
      ¬ LinearIndependent (EJ j) (fun i => top (x + z • y) j i)} := by
    intro j
    exact finite_bad_of_split_central_pencil
      (block := fun z i => top (x + z • y) j i)
      (base j x y) (direction j x y) (retract j x y)
      (split j x y) (fun z => realization j x y z)
  have hall : (⋃ j : J, {z : K |
      ¬ LinearIndependent (EJ j) (fun i => top (x + z • y) j i)}).Finite := by
    exact Set.finite_iUnion hbad
  apply hall.subset
  intro z hz
  rcases not_forall.mp hz with ⟨j, hj⟩
  exact Set.mem_iUnion.2 ⟨j, hj⟩

/-- Activated isotypic generation after supplying split finite-dimensional
central-field realizations.  This is a direct feed into the existing
Jacobian-top/right-action consumer; only the old arbitrary block comparison
remains a hypothesis. -/
theorem exists_activated_right_cyclic_of_split_central_isotypic
    {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (ι : (j : J) → K →+* EJ j)
    (top : M →+ ((j : J) → (Fin (r j) → QJ j)))
    (map_smul : ∀ (z : K) (m : M) (j : J) (i : Fin (r j)),
      top (z • m) j i = (ι j z) • top m j i)
    (block_generator : ∀ (j : J) (x : Fin (r j) → QJ j), Prop)
    (block_generator_iff_linearIndependent : ∀ j x,
      block_generator j x ↔ LinearIndependent (EJ j) x)
    (base direction : ∀ j, M → M → (PJ j →ₗ[K] QJ j))
    (retract : ∀ j, M → M → (QJ j →ₗ[K] PJ j))
    (split : ∀ (j : J) (x y : M),
      (retract j x y).comp (base j x y) = LinearMap.id)
    (realization : ∀ (j : J) (x y : M) (z : K),
      LinearIndependent (EJ j) (fun i => top (x + z • y) j i) ↔
        Function.Injective (base j x y + z • direction j x y))
    (top_generator_iff_jacobson : ∀ m : M,
      (∀ j, block_generator j (top m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (a : R) (x y : M),
      rightAction a (x + y) = rightAction a x + rightAction a y)
    (central_smul_right : ∀ (k : K) (m : M) (a : R),
      rightAction a (k • m) = k • rightAction a m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : ∀ j, block_generator j (top v j))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  have hbad : ∀ (x y : M),
      (∀ j, LinearIndependent (EJ j) (top x j)) →
        Set.Finite {z : K | ¬ ∀ j, LinearIndependent (EJ j)
          (fun i => top x j i + (ι j z) • top y j i)} := by
    intro x y _hx
    have hbad' := finite_isotypic_bad_of_split_central_pencils
      top base direction retract split realization x y
    apply hbad'.subset
    intro z hz
    intro htop
    apply hz
    intro j
    have heq : top (x + z • y) j =
        (fun i => top x j i + (ι j z) • top y j i) := by
      funext i
      calc
        top (x + z • y) j i = (top x + top (z • y)) j i := by rw [map_add]
        _ = top x j i + top (z • y) j i := rfl
        _ = top x j i + (ι j z) • top y j i := by rw [map_smul]
    rw [← heq]
    exact htop j
  exact exists_activated_right_cyclic_of_explicit_isotypic_blocks
    F ι top map_smul block_generator
    block_generator_iff_linearIndependent hbad top_generator_iff_jacobson
    rightAction rightAction_add central_smul_right v u e b l vL_zero e_decomp hv
    forbidden hforbidden

end Isotypic

end

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.finite_bad_of_split_central_pencil
#print axioms SymplecticStafford.FiniteLength.finite_isotypic_bad_of_split_central_pencils
#print axioms SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_split_central_isotypic
