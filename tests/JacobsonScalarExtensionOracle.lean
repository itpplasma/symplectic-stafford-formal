module

public import SymplecticStafford.FiniteLength.JacobsonScalarExtension
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Tactic

@[expose] public section

/-!
# Independent oracle for the Jacobson/auxiliary-field M05--M07 bridge

The coefficient field is `RatFunc ℚ`, while the pencil parameter is `ℚ`.
Thus the top has a finite orbit basis over its block field but is not finite
over the parameter field.  The top comparison in the test goes through the
actual Jacobson quotient, exercising the finite-generation reflection rather
than supplying a direct cyclicity equivalence.
-/

namespace SymplecticStafford.FiniteLength.JacobsonScalarExtensionOracle

open SymplecticStafford.FiniteLength
open Module

abbrev K := ℚ
abbrev E := RatFunc ℚ
abbrev R := E
abbrev M := Eᵐᵒᵖ
abbrev Q := E

def support : Set Unit := {()}

def minimalPoint : MinimalSupportPoint support where
  point := ()
  mem_support := by simp [support]
  minimal := by
    intro q hq _
    simpa [support] using hq

noncomputable def regularFiltration :
    RightMinimalSupportFiltration (R := R) (M := M) (α := Unit) 1 where
  support := support
  minimalPoint := minimalPoint
  level := fun i => if i = 0 then ⊥ else ⊤
  head := by simp
  last := by simp
  step := by
    intro i
    have hi0 : i = 0 := by fin_cases i; rfl
    subst i
    have hP : (⊥ : Submodule Rᵐᵒᵖ M).comap
        (⊤ : Submodule Rᵐᵒᵖ M).subtype = ⊥ := by
      rw [Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _)
    have hsimple :
        IsSimpleModule Rᵐᵒᵖ
          ((⊤ : Submodule Rᵐᵒᵖ M) ⧸
            ((⊥ : Submodule Rᵐᵒᵖ M).comap
              (⊤ : Submodule Rᵐᵒᵖ M).subtype)) := by
      let e :
          ((⊤ : Submodule Rᵐᵒᵖ M) ⧸
              ((⊥ : Submodule Rᵐᵒᵖ M).comap
                (⊤ : Submodule Rᵐᵒᵖ M).subtype)) ≃ₗ[Rᵐᵒᵖ] M :=
        (Submodule.quotEquivOfEqBot
          ((⊥ : Submodule Rᵐᵒᵖ M).comap
            (⊤ : Submodule Rᵐᵒᵖ M).subtype) hP).trans
          Submodule.topEquiv
      rw [e.isSimpleModule_iff]
      infer_instance
    apply (covBy_iff_quot_is_simple bot_le).2
    simpa using hsimple
  quotient_finite := by
    intro i
    fin_cases i
    infer_instance

noncomputable def scalarEmbedding : K →+* E := algebraMap K E

noncomputable def orbitAction (r : Rᵐᵒᵖ) : Q →ₗ[E] Q :=
  { toFun := fun x => x * r.unop
    map_add' := by intro x y; simp [add_mul]
    map_smul' := by intro a x; simp [mul_assoc, mul_comm] }

theorem rightCyclic_iff_ne_zero (m : M) :
    RightCyclic (R := R) m ↔ m ≠ 0 := by
  constructor
  · intro hm hzero
    obtain ⟨r, hr⟩ := hm 1
    rw [hzero] at hr
    simpa using hr
  · intro hm y
    refine ⟨MulOpposite.op (y.unop * m.unop⁻¹), ?_⟩
    change MulOpposite.op (y.unop * m.unop⁻¹) • m = y
    apply MulOpposite.unop_injective
    change m.unop * (y.unop * m.unop⁻¹) = y.unop
    rw [mul_comm m.unop (y.unop * m.unop⁻¹), mul_assoc,
      inv_mul_cancel₀ (by simpa using hm), mul_one]

theorem orbit_span_iff_ne_zero (m : Q) :
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
    ∃ n : Nat, ∃ b : Basis (Fin n) E Q,
      ∃ c : Fin n → Rᵐᵒᵖ,
        ∀ i, orbitAction (c i) m.unop = b i := by
  have hm0 : m ≠ 0 := (rightCyclic_iff_ne_zero m).mp hm
  let b : Basis (Fin 1) E E :=
    (Basis.singleton Unit E).reindex (Fintype.equivFin Unit)
  refine ⟨1, b, (fun _ => MulOpposite.op (m.unop)⁻¹), ?_⟩
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  change m.unop * m.unop⁻¹ = b 0
  have hb : b 0 = 1 := by
    change ((Basis.singleton Unit E).reindex
      (Fintype.equivFin Unit)) 0 = 1
    have he : (Fintype.equivFin Unit).symm (0 : Fin 1) = () :=
      Subsingleton.elim _ _
    rw [Basis.reindex_apply, he]
    exact Basis.singleton_apply Unit E ()
  rw [hb, mul_inv_cancel₀ (by simpa using hm0)]

noncomputable def topData :
    JacobsonScalarExtensionTopData (R := R) (M := M) (K := K)
      (E := E) (Q := Q) where
  top :=
    { toFun := fun m => m.unop
      map_zero' := by simp
      map_add' := by intro x y; simp }
  act := orbitAction
  ι := scalarEmbedding
  ι_injective := scalarEmbedding.injective
  top_smul := by
    intro z m
    simp [Algebra.smul_def, mul_comm]
  top_cyclic_iff := by
    intro m
    letI : Module.Finite Rᵐᵒᵖ M := regularFiltration.moduleFinite
    calc
      RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m) ↔
          RightCyclic (R := R) m :=
        (rightCyclic_iff_jacobson_quotient (R := R) m).symm
      _ ↔ m ≠ 0 := rightCyclic_iff_ne_zero m
      _ ↔ OrbitSpanTop (K := E) orbitAction m.unop :=
        by simpa using (orbit_span_iff_ne_zero m.unop).symm
  orbit_basis := by
    intro m hm
    letI : Module.Finite Rᵐᵒᵖ M := regularFiltration.moduleFinite
    obtain ⟨n, b, c, hbc⟩ := orbit_basis m
      ((rightCyclic_iff_jacobson_quotient (R := R) m).mpr hm)
    refine ⟨n, b, c, ?_⟩
    simpa using hbc

example (u : M) (hv : RightCyclic (R := R) (1 : M)) :
    Set.Finite {z : K | ¬ RightCyclic (R := R)
      (1 + @SMul.smul K M
        ((Module.toDistribMulAction (R := K) (M := M)).toDistribSMul.toSMul)
        z u)} := by
  letI : Module.Finite Rᵐᵒᵖ M := regularFiltration.moduleFinite
  have htop : ∀ m : M,
      RightCyclic (R := R) m ↔
        OrbitSpanTop (K := E) topData.act (topData.top m) := by
    intro m
    exact (rightCyclic_iff_jacobson_quotient (R := R) m).trans
      (topData.top_cyclic_iff m)
  have horbit : ∀ m : M, RightCyclic (R := R) m →
      ∃ n : Nat, ∃ b : Basis (Fin n) E Q,
        ∃ c : Fin n → Rᵐᵒᵖ,
          ∀ i, topData.act (c i) (topData.top m) = b i := by
    intro m hm
    exact topData.orbit_basis m
      ((rightCyclic_iff_jacobson_quotient (R := R) m).mp hm)
  exact finite_nongenerating_scalars_of_scalar_extension_orbit_basis
    (K := K) (R := R) (M := M) (E := E) (Q := Q)
    topData.top topData.act topData.ι topData.ι_injective topData.top_smul
    htop horbit (1 : M) u hv

end SymplecticStafford.FiniteLength.JacobsonScalarExtensionOracle
