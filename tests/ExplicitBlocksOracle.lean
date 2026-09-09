import SymplecticStafford.FiniteLength.ExplicitBlocks
import SymplecticStafford.FiniteLength.IsotypicBlocks
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Independent oracle for explicit composition/block bridges

The oracle instantiates the actual finite composition filtration on the
regular right module of `ℚ`.  It consumes both a one-factor division block
and a repeated 2-by-2 matrix block, while the top comparison is checked
against the actual Jacobson quotient by the direct regular-module calculation.
The source theorem remains conditional on this explicit comparison; no
general noncommutative isotypic decomposition is inferred.
-/

namespace SymplecticStafford.FiniteLength.ExplicitBlocksOracle

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

noncomputable def divTop : M →+ (Unit → (Fin 1 → K)) :=
  { toFun := fun m _ _ => m.unop
    map_zero' := by ext j i; simp
    map_add' := by intro x y; ext j i; simp }

noncomputable def matrixTop : M →+ (Unit → Matrix (Fin 2) (Fin 2) K) :=
  { toFun := fun m _ => !![m.unop, 0; 0, m.unop]
    map_zero' := by ext j i k <;> fin_cases i <;> fin_cases k <;> simp
    map_add' := by intro x y; ext j i k <;> fin_cases i <;> fin_cases k <;> simp }

noncomputable def scaleMap (c : K) :
    (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  { toFun := fun x => c • x
    map_add' := by intro x y; rw [smul_add]
    map_smul' := by intro a x; ext i; change c * (a * x i) = a * (c * x i); ring }

noncomputable def isotypicTop : M →+
    (Unit → (Fin 2 → (Fin 2 → K))) :=
  { toFun := fun m _ i => scaleMap m.unop (Pi.basisFun K (Fin 2) i)
    map_zero' := by ext j i k; simp [scaleMap]
    map_add' := by intro x y; ext j i k; simp [scaleMap, add_smul] }

theorem scaleMap_injective {c : K} (hc : c ≠ 0) :
    Function.Injective (scaleMap c) := by
  intro x y hxy
  ext i
  have hi := congrFun hxy i
  change c * x i = c * y i at hi
  exact mul_left_cancel₀ hc hi

theorem isotypic_top_li_iff (m : M) :
    LinearIndependent K (isotypicTop m ()) ↔ m.unop ≠ 0 := by
  constructor
  · intro h hm
    have hz := h.ne_zero (0 : Fin 2)
    simp [isotypicTop, scaleMap, hm] at hz
  · intro hm
    have hb := (Pi.basisFun K (Fin 2)).linearIndependent
    have hi : (scaleMap m.unop).ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr (scaleMap_injective hm)
    have hmap := hb.map' (scaleMap m.unop) hi
    simpa [isotypicTop, Function.comp_def] using hmap

example (u : M) :
    ∃ z : K, z ∉ (∅ : Set K) ∧
      RightCyclic (R := R) ((1 : M) + z • u) := by
  letI : Module.Finite Rᵐᵒᵖ M := regularFiltration.moduleFinite
  let ι : (j : Unit) → K →+* K := fun _ => RingHom.id K
  have hmap : ∀ (z : K) (m : M) (j : Unit) (i : Fin 2),
      isotypicTop (z • m) j i = (ι j z) • isotypicTop m j i := by
    intro z m j i
    simp [isotypicTop, scaleMap, ι, Algebra.smul_def, mul_comm]
    ring
  have hbad : ∀ (x y : M),
      (∀ j : Unit, LinearIndependent K (isotypicTop x j)) →
        Set.Finite {z : K | ¬ ∀ j : Unit,
          LinearIndependent K (fun i =>
            isotypicTop x j i + (ι j z) • isotypicTop y j i)} := by
    intro x y hx
    have hx0 : x.unop ≠ 0 := (isotypic_top_li_iff x).mp (hx ())
    have hfin := finite_pencil_exceptions
      (fun _ : Unit => RingHom.id K)
      (fun _ : Unit => x.unop) (fun _ : Unit => y.unop)
      (fun _ => hx0) (fun _ => RingHom.injective (RingHom.id K))
    apply hfin.subset
    intro z hz
    refine ⟨(), ?_⟩
    by_contra hne
    apply hz
    intro j
    have hzero : (x + z • y).unop ≠ 0 := by
      intro hzero
      apply hne
      simpa [ι, Algebra.smul_def, mul_comm] using hzero
    have hli := (isotypic_top_li_iff (x + z • y)).mpr hzero
    have heq : isotypicTop (x + z • y) j =
        (fun i => isotypicTop x j i + (ι j z) • isotypicTop y j i) := by
      funext i
      calc
        isotypicTop (x + z • y) j i =
            (isotypicTop x + isotypicTop (z • y)) j i := by rw [map_add]
        _ = isotypicTop x j i + isotypicTop (z • y) j i := rfl
        _ = isotypicTop x j i + (ι j z) • isotypicTop y j i := by rw [hmap]
    rw [← heq]
    exact hli
  have htop : ∀ m : M,
      (∀ j : Unit, LinearIndependent K (isotypicTop m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m) := by
    intro m
    rw [← rightCyclic_iff_jacobson_quotient (R := R) m]
    constructor
    · intro h
      have hm : m.unop ≠ 0 := (isotypic_top_li_iff m).mp (h ())
      exact (rightCyclic_iff_ne_zero m).mpr (by
        intro hm0
        exact hm (congrArg MulOpposite.unop hm0))
    · intro hm j
      apply (isotypic_top_li_iff m).mpr
      intro hm0
      apply (rightCyclic_iff_ne_zero m).mp hm
      apply MulOpposite.unop_injective
      simpa using hm0
  have hv : ∀ j : Unit, LinearIndependent K (isotypicTop (1 : M) j) := by
    intro j
    exact (isotypic_top_li_iff _).mpr (by simp)
  obtain ⟨z, hz, hcyc, _⟩ :=
    exists_activated_right_cyclic_of_explicit_isotypic_blocks
      regularFiltration ι isotypicTop hmap
      (fun _ x => LinearIndependent K x) (by intro j x; rfl) hbad htop
      (fun r x => MulOpposite.op (x.unop * r))
      (by intro r x y; apply MulOpposite.unop_injective; simp [add_mul])
      (by
        intro k m r
        apply MulOpposite.unop_injective
        simp [Algebra.smul_def, mul_comm, mul_assoc])
      (1 : M) u 1 1 0 (by simp) (by simp) hv ∅ Set.finite_empty
  exact ⟨z, hz, hcyc⟩

example (u : M) :
    ∃ z : K, z ∉ (∅ : Set K) ∧
      RightCyclic (R := R) ((1 : M) + z • u) := by
  letI : Module.Finite Rᵐᵒᵖ M := regularFiltration.moduleFinite
  let ιmap : (j : Unit) → (i : Fin 1) → K →+* K := fun _ _ => RingHom.id K
  have htop : ∀ m : M,
      (∀ j, TopGenerator (fun i => divTop m j i)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m) := by
    intro m
    rw [← rightCyclic_iff_jacobson_quotient (R := R) m]
    constructor
    · intro h
      have hm : m.unop ≠ 0 := by
        intro hm0
        have hz := h ()
        have hzero : divTop m () 0 = 0 := by simp [divTop, hm0]
        exact (semisimple_top_criterion _).mp hz 0 hzero
      have hm' : m ≠ 0 := by
        intro hm0
        exact hm (congrArg MulOpposite.unop hm0)
      exact (rightCyclic_iff_ne_zero m).mpr hm'
    · intro hm j
      apply (semisimple_top_criterion _).mpr
      intro i
      simpa [divTop] using (rightCyclic_iff_ne_zero m).mp hm
  have hmap : ∀ (z : K) (m : M) (j : Unit) (i : Fin 1),
      divTop (z • m) j i = ιmap j i z * divTop m j i := by
    intro z m j i
    simp [divTop, ιmap, Algebra.smul_def, mul_comm]
  obtain ⟨z, hz, hcyc, hrel⟩ := exists_activated_right_cyclic_of_explicit_division_blocks
    (ιmap := ιmap) regularFiltration divTop hmap htop
    (fun r x => MulOpposite.op (x.unop * r))
    (by intro r x y; apply MulOpposite.unop_injective; simp [add_mul])
    (by intro k m r; apply MulOpposite.unop_injective; simp [Algebra.smul_def, mul_comm, mul_assoc])
    (1 : M) u 1 1 0 (by simp) (by simp)
    (by intro _ _; simp [divTop])
    (by intro j i; exact RingHom.injective (ιmap j i))
    ∅ Set.finite_empty
  exact ⟨z, hz, hcyc⟩

example (u : M) :
    ∃ z : K, z ∉ (∅ : Set K) ∧
      RightCyclic (R := R) ((1 : M) + z • u) := by
  letI : Module Rᵐᵒᵖ M := inferInstance
  have htop : ∀ m : M,
      (∀ j : Unit, MatrixTopGenerator (matrixTop m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ M).mkQ m) := by
    intro m
    rw [← rightCyclic_iff_jacobson_quotient (R := R) m]
    constructor
    · intro h
      have hd := (matrix_top_generator_iff (matrixTop m ())).mp (h ())
      have hm : m.unop ≠ 0 := by
        intro hm0
        apply hd
        simp [matrixTop, hm0, Matrix.det_fin_two]
      have hm' : m ≠ 0 := by
        intro hm0
        exact hm (congrArg MulOpposite.unop hm0)
      exact (rightCyclic_iff_ne_zero m).mpr hm'
    · intro hm j
      apply (matrix_top_generator_iff _).mpr
      simpa [matrixTop, Matrix.det_fin_two] using
        (rightCyclic_iff_ne_zero m).mp hm
  have hmap : ∀ (z : K) (m : M) (j : Unit),
      matrixTop (z • m) j = z • matrixTop m j := by
    intro z m j
    ext i k
    fin_cases i <;> fin_cases k <;> simp [matrixTop, Algebra.smul_def, mul_comm]
  obtain ⟨z, hz, hcyc, hrel⟩ := exists_activated_right_cyclic_of_explicit_matrix_blocks
    regularFiltration matrixTop hmap htop
    (fun r x => MulOpposite.op (x.unop * r))
    (by intro r x y; apply MulOpposite.unop_injective; simp [add_mul])
    (by intro k m r; apply MulOpposite.unop_injective; simp [Algebra.smul_def, mul_comm, mul_assoc])
    (1 : M) u 1 1 0 (by simp) (by simp)
    (by intro j; simp [matrixTop, Matrix.det_fin_two]) ∅ Set.finite_empty
  exact ⟨z, hz, hcyc⟩

end SymplecticStafford.FiniteLength.ExplicitBlocksOracle

#print axioms SymplecticStafford.FiniteLength.ExplicitBlocksOracle.rightCyclic_iff_ne_zero
