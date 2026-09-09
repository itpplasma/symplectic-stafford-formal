import SymplecticStafford.FiniteLength.FiniteOrbitPencil
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Tactic

/-!
# Independent oracle for the scalar-extension M07 lane

`RatFunc ℚ` is used as the auxiliary orbit field.  It is infinite-dimensional
over `ℚ`, while the regular block is one-dimensional over `RatFunc ℚ`.
The test therefore exercises the extension theorem without accidentally
reintroducing finite central dimension.  The right action is kept in the
opposite-module convention used by the library.
-/

namespace SymplecticStafford.FiniteLength.ScalarExtensionOrbitOracle

open SymplecticStafford.FiniteLength

abbrev K := ℚ
abbrev E := RatFunc ℚ
abbrev R := E
abbrev M := E
abbrev Q := E

/- `E` really is not finite over the parameter field.  This is proved from
the transcendental generator, rather than left as a comment or hidden in a
finite-dimensional typeclass. -/
example : ¬ Module.Finite K E := by
  intro h
  have ha : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  have hx : IsAlgebraic K (RatFunc.X : E) := ha.isAlgebraic _
  have hmap : algebraMap K E = RatFunc.C := by
    ext x
    simp
  rcases hx with ⟨p, hp, hroot⟩
  let algpoly : Algebra K E := RatFunc.instAlgebraOfPolynomial K K
  have hxpoly : @IsAlgebraic K E _ _ algpoly RatFunc.X := by
    refine ⟨p, hp, ?_⟩
    rw [@Polynomial.aeval_def K E _ _ algpoly]
    change Polynomial.eval₂ (RatFunc.C) RatFunc.X p = 0
    rw [@Polynomial.aeval_def K E _ _
      (DivisionRing.toRatAlgebra : Algebra K E)] at hroot
    rw [hmap] at hroot
    exact hroot
  exact (RatFunc.transcendental_X (K := K)) hxpoly

noncomputable def scalarEmbedding : K →+* E := algebraMap K E

example : Function.Injective (scalarEmbedding : K →+* E) := by
  exact (scalarEmbedding : K →+* E).injective

noncomputable def top : M →+ Q := AddMonoidHom.id M

noncomputable def orbitAction (r : Rᵐᵒᵖ) : Q →ₗ[E] Q :=
  { toFun := fun x => x * r.unop
    map_add' := by intro x y; simp [add_mul]
    map_smul' := by intro a x; simp [mul_assoc, mul_comm] }

theorem orbitAction_apply (r : Rᵐᵒᵖ) (x : Q) :
    orbitAction r x = x * r.unop := rfl

theorem rightCyclic_iff_ne_zero (m : M) :
    RightCyclic (R := R) m ↔ m ≠ 0 := by
  constructor
  · intro hm hzero
    obtain ⟨r, hr⟩ := hm 1
    rw [hzero] at hr
    simpa using hr
  · intro hm y
    refine ⟨MulOpposite.op (y * m⁻¹), ?_⟩
    change m * (y * m⁻¹) = y
    -- `RightCyclic` uses the opposite regular action, so the coefficient
    -- witness is chosen on the right.  Commutativity is only for this field
    -- oracle, not an assumption in the library theorem.
    rw [mul_comm m (y * m⁻¹), mul_assoc, inv_mul_cancel₀ hm, mul_one]

theorem orbit_span_iff_ne_zero (m : M) :
    OrbitSpanTop (K := E) orbitAction m ↔ m ≠ 0 := by
  constructor
  · intro hspan hzero
    subst m
    have hle : Submodule.span E (Set.range (fun r : Rᵐᵒᵖ =>
        orbitAction r 0)) ≤ (⊥ : Submodule E E) := by
      apply Submodule.span_le.mpr
      rintro y ⟨r, rfl⟩
      simp [orbitAction]
    have htopbot : (⊤ : Submodule E E) ≤ ⊥ := by
      rw [← hspan]
      exact hle
    have honebot : (1 : E) ∈ (⊥ : Submodule E E) :=
      htopbot (by simp)
    exact one_ne_zero ((Submodule.mem_bot E).mp honebot)
  · intro hm
    unfold OrbitSpanTop
    apply top_unique
    intro y hy
    apply Submodule.subset_span
    refine ⟨MulOpposite.op (y * m⁻¹), ?_⟩
    simp [orbitAction, hm, mul_comm, mul_left_comm, mul_assoc]

theorem orbit_basis (m : M) (hm : RightCyclic (R := R) m) :
    ∃ n : Nat, ∃ b : Module.Basis (Fin n) E Q,
      ∃ c : Fin n → Rᵐᵒᵖ,
        ∀ i, orbitAction (c i) (top m) = b i := by
  have hm0 : m ≠ 0 := (rightCyclic_iff_ne_zero m).mp hm
  let b : Module.Basis (Fin 1) E E :=
    (Module.Basis.singleton Unit E).reindex (Fintype.equivFin Unit)
  refine ⟨1, b, (fun _ => MulOpposite.op m⁻¹), ?_⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change m * m⁻¹ = b 0
  have hb : b 0 = 1 := by
    change ((Module.Basis.singleton Unit E).reindex
      (Fintype.equivFin Unit)) 0 = 1
    have he : (Fintype.equivFin Unit).symm (0 : Fin 1) = () :=
      Subsingleton.elim _ _
    rw [Module.Basis.reindex_apply, he]
    exact Module.Basis.singleton_apply Unit E ()
  rw [hb, mul_inv_cancel₀ hm0]

example (v u : M) (hv : RightCyclic (R := R) v) :
    Set.Finite {z : K | ¬ RightCyclic (R := R)
      (v + (algebraMap K M z) * u)} := by
  exact finite_nongenerating_scalars_of_scalar_extension_orbit_basis
      (K := K) (R := R) (M := M) (E := E) (Q := Q)
      (top := top) (act := orbitAction)
      (ι := scalarEmbedding) (hι := (scalarEmbedding : K →+* E).injective)
    (top_smul := by
      intro z m
      simp [top, Algebra.smul_def])
      (top_cyclic_iff := by
        intro m
        simpa [top, rightCyclic_iff_ne_zero m] using
          (orbit_span_iff_ne_zero m).symm)
      (orbit_basis := orbit_basis) v u hv

end SymplecticStafford.FiniteLength.ScalarExtensionOrbitOracle
