module

public import SymplecticStafford.FiniteLength.ActivatedPencil
public import SymplecticStafford.FiniteLength.JacobsonTop
public import SymplecticStafford.FiniteLength.RightFiltration
public import SymplecticStafford.FiniteLength.MatrixPencil

@[expose] public section

/-!
# Explicit finite-composition block bridges

The finite-length pencil is useful only after two pieces of data have been
made explicit: a finite composition filtration of the actual right module,
and a comparison between its actual Jacobson top and the displayed blocks.
This file packages those data without replacing either one by a formal or
completed surrogate.

The division-block theorem handles a finite product of division-ring factors
(multiplicity one in each factor).  The matrix theorem handles repeated
central-field matrix blocks.  Both use the actual radical quotient through
`rightCyclic_iff_jacobson_quotient`; the filtration is what supplies the
finite-generation hypothesis needed by that theorem.

An arbitrary repeated simple factor with a genuinely noncommutative
endomorphism division ring is intentionally *not* inferred here.  Such a
caller must still provide its block comparison (or a separate
division-coefficient pencil theorem).  This is the exact remaining M07
boundary, rather than an accidental scalarization.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section DivisionBlocks

variable {R : Type u} {M : Type v} {K : Type w} [Ring R]
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Field K] [Module K M] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {ι : J → Type*} [∀ j, Fintype (ι j)]
    [∀ j, DecidableEq (ι j)]
    {D : (j : J) → ι j → Type*}
    [∀ j i, DivisionRing (D j i)]
    {n : Nat}
    (ιmap : (j : J) → (i : ι j) → K →+* D j i)

/--
An activated pencil consuming an actual finite composition filtration and an
explicit product of division-ring blocks.  The displayed equivalence is
deliberately with the *actual* Jacobson quotient, not with an assumed
semisimple model.
-/
theorem exists_activated_right_cyclic_of_explicit_division_blocks
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (top : M →+ ((j : J) → (i : ι j) → D j i))
    (map_smul : ∀ (z : K) (m : M) (j : J) (i : ι j),
      top (z • m) j i = ιmap j i z * top m j i)
    (top_generator_iff_jacobson : ∀ m : M,
      (∀ j, TopGenerator (fun i => top m j i)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : ∀ j i, top v j i ≠ 0)
    (hinj : ∀ j i, Function.Injective (ιmap j i))
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  letI : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have hreflect : ∀ m : M,
      (∀ j, TopGenerator (fun i => top m j i)) →
        RightCyclic (R := R) m := by
    intro m hm
    apply (rightCyclic_iff_jacobson_quotient (R := R) m).mpr
    exact (top_generator_iff_jacobson m).mp hm
  obtain ⟨z, hz, hcyc⟩ := exists_simultaneous_right_cyclic_avoiding
    (ιmap := ιmap) top map_smul hreflect v u hv hinj forbidden hforbidden
  refine ⟨z, hz, hcyc, ?_⟩
  exact pencil_right_action_add rightAction rightAction_add
    central_smul_right v u e b l vL_zero e_decomp z

end DivisionBlocks

section MatrixBlocks

variable {R : Type u} {M : Type v} {K : Type w} [Ring R]
    [AddCommGroup M] [Module Rᵐᵒᵖ M]
    [Field K] [Module K M] [Infinite K]
    {J : Type*} [Fintype J] [DecidableEq J]
    {r n : Nat}

/--
The repeated-matrix specialization of the same bridge.  Matrix blocks are
only used at a central field; the noncommuting products remain in the actual
right action on `M`.
-/
theorem exists_activated_right_cyclic_of_explicit_matrix_blocks
    (F : RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) n)
    (top : M →+ (J → Matrix (Fin r) (Fin r) K))
    (map_smul : ∀ (z : K) (m : M) (j : J),
      top (z • m) j = z • top m j)
    (top_generator_iff_jacobson : ∀ m : M,
      (∀ j, MatrixTopGenerator (top m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m))
    (rightAction : R → M → M)
    (rightAction_add : ∀ (r : R) (x y : M),
      rightAction r (x + y) = rightAction r x + rightAction r y)
    (central_smul_right : ∀ (k : K) (m : M) (r : R),
      rightAction r (k • m) = k • rightAction r m)
    (v u e : M) (b l : R) (vL_zero : rightAction l v = 0)
    (e_decomp : e = rightAction b v + rightAction l u)
    (hv : ∀ j, Matrix.det (top v j) ≠ 0)
    (forbidden : Set K) (hforbidden : forbidden.Finite) :
    ∃ z : K, z ∉ forbidden ∧
      RightCyclic (R := R) (v + z • u) ∧
      rightAction l (v + z • u) + z • rightAction b v = z • e := by
  letI : Module.Finite Rᵐᵒᵖ M := F.moduleFinite
  have hreflect : ∀ m : M,
      (∀ j, MatrixTopGenerator (top m j)) →
        RightCyclic (R := R) m := by
    intro m hm
    apply (rightCyclic_iff_jacobson_quotient (R := R) m).mpr
    exact (top_generator_iff_jacobson m).mp hm
  obtain ⟨z, hz, hgen⟩ := exists_activated_matrix_right_cyclic_avoiding
    (R := R) (M := M) (K := K) top map_smul hreflect
    rightAction rightAction_add central_smul_right v u e b l vL_zero e_decomp
    hv forbidden hforbidden
  exact ⟨z, hz, hgen.1, hgen.2⟩

end MatrixBlocks

end SymplecticStafford.FiniteLength

#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_explicit_division_blocks
#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_explicit_matrix_blocks
