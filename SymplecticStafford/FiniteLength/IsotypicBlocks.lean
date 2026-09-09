import SymplecticStafford.FiniteLength.JacobsonTop
import SymplecticStafford.FiniteLength.RadicalLift
import SymplecticStafford.FiniteLength.RightFiltration

/-!
# Repeated simple-factor blocks over division rings

This is the exact noncommutative M07 consumer boundary.  A block is a finite
tuple of vectors in an arbitrary left division-ring module; its generator
criterion is left linear independence, as for an isotypic semisimple block
`S^r`.  The central-pencil exceptional-set statement is an explicit input.
It is the remaining determinant-free theorem for genuinely noncommutative
endomorphism division rings, and is not inferred from a scalar determinant.

The module comparison is nevertheless genuine: the finite composition
filtration supplies `Module.Finite`, and the block criterion is compared to
the actual `Module.jacobson` quotient before cyclicity is concluded.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section

variable {R : Type u} {M : Type v} {K : Type w} [Ring R]
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Field K] [Module K M] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {E : J → Type*} [∀ j, DivisionRing (E j)]
    {Q : J → Type*} [∀ j, AddCommGroup (Q j)]
    [∀ j, Module (E j) (Q j)]
    {r : J → Nat} {n : Nat}

/-- Activated pencil on explicit repeated-simple-factor blocks.

`bad_finite` is intentionally quantified over the exact block tuple and
central scalar action.  A future determinant-free division-ring proof can
instantiate it; no commutativity of the `E j` is present in this theorem.
-/
theorem exists_activated_right_cyclic_of_explicit_isotypic_blocks
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (ι : (j : J) → K →+* E j)
    (top : M →+ ((j : J) → (Fin (r j) → Q j)))
    (map_smul : ∀ (z : K) (m : M) (j : J) (i : Fin (r j)),
      top (z • m) j i = (ι j z) • top m j i)
    (block_generator : ∀ (j : J) (x : Fin (r j) → Q j), Prop)
    (block_generator_iff_linearIndependent : ∀ j x,
      block_generator j x ↔ LinearIndependent (E j) x)
    (bad_finite : ∀ (x y : M),
      (∀ j, LinearIndependent (E j) (top x j)) →
        Set.Finite {z : K |
          ¬ ∀ j, LinearIndependent (E j)
            (fun i => top x j i + (ι j z) • top y j i)})
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
  letI : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have hv_li : ∀ j, LinearIndependent (E j) (top v j) := by
    intro j
    exact (block_generator_iff_linearIndependent j (top v j)).mp (hv j)
  have hbad' := bad_finite v u hv_li
  have hbad : (Set.Finite {z : K |
      ¬ ∀ j, LinearIndependent (E j) (top (v + z • u) j)}) := by
    apply hbad'.subset
    intro z hz
    intro htop
    apply hz
    intro j
    have htop_eq : top (v + z • u) j =
        (fun i => top v j i + (ι j z) • top u j i) := by
      funext i
      calc
        top (v + z • u) j i = (top v + top (z • u)) j i := by rw [map_add]
        _ = top v j i + top (z • u) j i := rfl
        _ = top v j i + (ι j z) • top u j i := by rw [map_smul]
    rw [htop_eq]
    exact htop j
  have hall : (forbidden ∪ {z : K |
      ¬ ∀ j, LinearIndependent (E j) (top (v + z • u) j)}).Finite :=
    hforbidden.union hbad
  obtain ⟨z, hz⟩ := (Set.infinite_univ.sdiff hall).nonempty
  have hz_forbidden : z ∉ forbidden := by
    intro h
    exact hz.2 (Or.inl h)
  have hz_top_li : ∀ j, LinearIndependent (E j) (top (v + z • u) j) := by
    intro j
    by_contra h
    apply hz.2
    right
    intro hgen
    exact h (hgen j)
  have hz_top : ∀ j, block_generator j (top (v + z • u) j) := by
    intro j
    exact (block_generator_iff_linearIndependent j _).mpr (hz_top_li j)
  have hz_jac : RightCyclic (R := R)
      ((Module.jacobson Rᵐᵒᵖ M).mkQ (v + z • u)) :=
    (top_generator_iff_jacobson (v + z • u)).mp hz_top
  refine ⟨z, hz_forbidden,
    (rightCyclic_iff_jacobson_quotient _).mpr hz_jac, ?_⟩
  exact pencil_right_action_add rightAction rightAction_add
    central_smul_right v u e b l vL_zero e_decomp z

end

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_explicit_isotypic_blocks
