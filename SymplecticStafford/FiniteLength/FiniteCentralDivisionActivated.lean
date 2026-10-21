module

public import SymplecticStafford.FiniteLength.FiniteCentralDivisionPencil
public import SymplecticStafford.FiniteLength.ExplicitBlocks

@[expose] public section

/-!
# Activated pencils for finite-central isotypic blocks

This is the composition step from the finite-dimensional-over-the-center
bridge to the actual finite-length/right-cyclic consumer.  For a finite family
of repeated division-ring blocks, the centrality and finite-dimensionality
fields produce the finite bad set; `ExplicitBlocks` then compares those
blocks with the actual Jacobson quotient and lifts cyclicity to the original
right module.

The ordered identity is retained literally in the output.  No decomposition
of an arbitrary finite-length module, Jacobson-top comparison, or universal
filtered-module construction is inferred: those remain explicit inputs.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section

variable {R : Type u} {M : Type v} {K : Type w} [Ring R]
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Field K] [Module K M] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {r : J → Nat}
    {EJ : J → Type*} [∀ j, DivisionRing (EJ j)]
    {QJ : J → Type*} [∀ j, AddCommGroup (QJ j)]
    [∀ j, Module (EJ j) (QJ j)] [∀ j, Module K (QJ j)]
    [∀ j, Module K (EJ j)] [∀ j, FiniteDimensional K (EJ j)]

/-- Activated right cyclicity for a finite family of repeated division-ring
blocks, assuming each block is finite-dimensional over the central field.

The finite-bad-set calculation is derived, not supplied: it applies
`finite_bad_of_finite_central_division_blocks` to the actual top coordinates.
The remaining top/Jacobson comparison is exactly the explicit hypothesis
required by `exists_activated_right_cyclic_of_explicit_isotypic_blocks`.
-/
theorem exists_activated_right_cyclic_of_finite_central_isotypic
    {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (ι : (j : J) → K →+* EJ j)
    (top : M →+ ((j : J) → (Fin (r j) → QJ j)))
    (map_smul : ∀ (z : K) (m : M) (j : J) (i : Fin (r j)),
      top (z • m) j i = (ι j z) • top m j i)
    (central_coeff : ∀ (j : J) (k : K) (e : EJ j),
      k • e = ι j k * e)
    (central_embedding : ∀ (j : J) (k : K) (e : EJ j),
      ι j k * e = e * ι j k)
    (central_vector : ∀ (j : J) (k : K) (v : QJ j),
      k • v = (ι j k) • v)
    (block_generator : ∀ (j : J) (x : Fin (r j) → QJ j), Prop)
    (block_generator_iff_linearIndependent : ∀ j x,
      block_generator j x ↔ LinearIndependent (EJ j) x)
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
    intro x y hx
    exact finite_bad_of_finite_central_division_blocks
      (ιmap := ι) (central_coeff := central_coeff)
      (central_embedding := central_embedding)
      (central_vector := central_vector)
      (x := fun j => top x j) (y := fun j => top y j) hx
  exact exists_activated_right_cyclic_of_explicit_isotypic_blocks
    F ι top map_smul block_generator
    block_generator_iff_linearIndependent hbad top_generator_iff_jacobson
    rightAction rightAction_add central_smul_right v u e b l vL_zero e_decomp hv
    forbidden hforbidden

end

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_finite_central_isotypic
