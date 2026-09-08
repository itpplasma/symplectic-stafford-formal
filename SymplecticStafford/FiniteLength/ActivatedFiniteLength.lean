import SymplecticStafford.FiniteLength.ActivatedPencil
import SymplecticStafford.FiniteLength.RightFiltration
import SymplecticStafford.FiniteLength.JacobsonTop

/-!
# Activated pencils from an actual finite-length module

This file supplies the missing finite-length consumer for M07.  The block
comparison is deliberately an input: its `generator` predicate may be a
product of division rings, a repeated matrix block, or a mixture of both.
The `finite_nongenerating` field is the precise finite independence statement
needed for the scalar pencil; it does not commute any coefficients or pretend
that a matrix algebra is a division ring.

The module-theoretic part is no longer an opaque `reflects_generation`
hypothesis.  `quotient_generator_iff` identifies the supplied block top with
the *actual* Jacobson quotient, and the theorem below uses the finite
composition filtration to obtain finite generation before applying the
Jacobson lifting theorem.  Thus repeated simple factors and noncommutative
matrix/division blocks are admitted whenever their explicit top comparison
and finite pencil-independence certificates are supplied.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section Data

variable {R : Type u} {M : Type v} {K : Type w} [Ring R]
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Field K] [Module K M] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {B : J → Type*} [∀ j, AddCommGroup (B j)]

/-- A finite-length semisimple-top comparison for an arbitrary family of
blocks.  `B j` is intentionally unconstrained: in particular it may be a
noncommutative matrix ring or a division-ring block.

`finite_nongenerating` is stated for the actual pencil in `M`, so all
right-action and coefficient orders have already been fixed by the caller.
The quotient equivalence is with the actual Jacobson radical, not with a
formal or completed substitute.
-/
structure FiniteLengthTopData where
  top : M →+ ((j : J) → B j)
  generator : ((j : J) → B j) → Prop
  finite_nongenerating : ∀ (v u : M), generator (top v) →
    Set.Finite {z : K | ¬ generator (top (v + z • u))}
  quotient_generator_iff : ∀ m : M,
    generator (top m) ↔
      RightCyclic (R := R) ((Module.jacobson Rᵐᵒᵖ M).mkQ m)

end Data

section Activated

variable {R : Type u} {M : Type v} {K : Type w} [Ring R]
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Field K] [Module K M] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {B : J → Type*} [∀ j, AddCommGroup (B j)]

/-- Generic activated-pencil theorem for an arbitrary finite-length module.

The filtration is an actual finite composition filtration, hence supplies
`Module.Finite` for the right module.  A scalar outside the finite
non-generating set makes the block top generate; the actual Jacobson-top
criterion then lifts this to right cyclicity.  The final conjunct is kept in
the original ordered right-action form, with the hypotheses `vL=0` and
`e=vB+uL`.
-/
theorem exists_activated_right_cyclic_of_finite_length_top
    {n : Nat}
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (T : FiniteLengthTopData (R := R) (M := M) (K := K) (J := J) (B := B))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : T.generator (T.top v)) (forbidden : Set K)
    (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  letI : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have hbad : (Set.Finite {z : K |
      ¬ T.generator (T.top (v + z • u))}) :=
    T.finite_nongenerating v u hv
  have hall : (forbidden ∪ {z : K |
      ¬ T.generator (T.top (v + z • u))}).Finite :=
    hforbidden.union hbad
  obtain ⟨z, hz⟩ := (Set.infinite_univ.sdiff hall).nonempty
  have hzforbidden : z ∉ forbidden := by
    intro h
    exact hz.2 (Or.inl h)
  have hzgen : T.generator (T.top (v + z • u)) := by
    by_contra h
    exact hz.2 (Or.inr h)
  have hq : RightCyclic (R := R)
      ((Module.jacobson Rᵐᵒᵖ M).mkQ (v + z • u)) :=
    (T.quotient_generator_iff (v + z • u)).mp hzgen
  refine ⟨z, hzforbidden, (rightCyclic_iff_jacobson_quotient _).mpr hq, ?_⟩
  exact pencil_right_action_add rightAction rightAction_add
    central_smul_right v u e b l vL_zero e_decomp z

end Activated

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_finite_length_top
