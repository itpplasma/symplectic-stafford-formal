module

public import SymplecticStafford.FiniteLength.FiniteCentralDivisionActivated
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Independent oracle for finite-central activated blocks

The regular right module of `ℚ` is given two distinct one-dimensional
isotypic factors.  The source theorem must avoid the finite bad set for both
factors while comparing the resulting block top with the actual Jacobson
quotient.
-/

namespace SymplecticStafford.FiniteLength.FiniteCentralDivisionActivatedOracle

open SymplecticStafford.FiniteLength

abbrev K := ℚ
abbrev R := ℚ
abbrev M := ℚᵐᵒᵖ

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

noncomputable def twoTop : M →+
    ((j : Fin 2) → (Fin 1 → K)) :=
  { toFun := fun m _ _ => m.unop
    map_zero' := by ext j i; simp
    map_add' := by intro x y; ext j i; simp }

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

theorem two_top_li_iff (m : M) (j : Fin 2) :
    LinearIndependent K (twoTop m j) ↔ m.unop ≠ 0 := by
  rw [linearIndependent_unique_iff]
  constructor
  · intro h hm
    exact h (by simp [twoTop, hm])
  · intro hm hzero
    apply hm
    simpa [twoTop] using hzero

example (u : M) :
    ∃ z : K, z ∉ (∅ : Set K) ∧
      RightCyclic (R := R) ((1 : M) + z • u) := by
  letI : Module.Finite Rᵐᵒᵖ M := regularFiltration.moduleFinite
  let ι : (j : Fin 2) → K →+* K := fun _ => RingHom.id K
  have hmap : ∀ (z : K) (m : M) (j : Fin 2) (i : Fin 1),
      twoTop (z • m) j i = (ι j z) • twoTop m j i := by
    intro z m j i
    simp [twoTop, ι, Algebra.smul_def, mul_comm]
  have htop : ∀ m : M,
      (∀ j : Fin 2, LinearIndependent K (twoTop m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m) := by
    intro m
    rw [← rightCyclic_iff_jacobson_quotient (R := R) m]
    constructor
    · intro h
      have hm : m.unop ≠ 0 := by
        intro hm0
        have hz := h 0
        exact (two_top_li_iff m 0).mp hz (by simp [hm0])
      exact (rightCyclic_iff_ne_zero m).mpr (by
        intro hm0
        exact hm (congrArg MulOpposite.unop hm0))
    · intro hm j
      exact (two_top_li_iff m j).mpr
        (by simpa using (rightCyclic_iff_ne_zero m).mp hm)
  have hv : ∀ j : Fin 2, LinearIndependent K (twoTop (1 : M) j) := by
    intro j
    exact (two_top_li_iff _ _).mpr (by simp)
  obtain ⟨z, hz, hcyc, _⟩ :=
    exists_activated_right_cyclic_of_finite_central_isotypic
      (r := fun _ : Fin 2 => 1) regularFiltration ι twoTop hmap
      (central_coeff := by
        intro j k e
        simp [Algebra.smul_def])
      (central_embedding := by
        intro j k e
        simp [Algebra.smul_def, mul_comm])
      (central_vector := by
        intro j k v
        simp [Algebra.smul_def])
      (fun _ x => LinearIndependent K x) (by intro j x; rfl) htop
      (fun r x => MulOpposite.op (x.unop * r))
      (by intro r x y; apply MulOpposite.unop_injective; simp [add_mul])
      (by
        intro k m r
        apply MulOpposite.unop_injective
        simp [Algebra.smul_def, mul_comm, mul_assoc])
      (1 : M) u 1 1 0 (by simp) (by simp) hv ∅ Set.finite_empty
  exact ⟨z, hz, hcyc⟩

end SymplecticStafford.FiniteLength.FiniteCentralDivisionActivatedOracle

#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_finite_central_isotypic
