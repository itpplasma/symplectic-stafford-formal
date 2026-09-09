import SymplecticStafford.FiniteLength.MinimalPrimeCentralActivated
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Independent oracle for the minimal-prime local activated bridge

The regular right module of `ℚ` is used as both the good source and local
model.  The local certificate is supplied through the Noetherian/Artinian
fields, while the one-dimensional rational block is compared directly with
the actual Jacobson quotient.
-/

namespace SymplecticStafford.FiniteLength.MinimalPrimeCentralActivatedOracle

open SymplecticStafford.FiniteLength

abbrev K := ℚ
abbrev R := ℚ
abbrev G := ℚᵐᵒᵖ
abbrev N := ℚᵐᵒᵖ

def support : Set Unit := {()}

def minimalPoint : MinimalSupportPoint support where
  point := ()
  mem_support := by simp [support]
  minimal := by
    intro q hq _
    simpa [support] using hq

noncomputable def localInput :
    MinimalPrimeLocalInput (R := Rᵐᵒᵖ) G N Unit where
  good_finite := by infer_instance
  support := support
  minimalPoint := minimalPoint
  source := LinearMap.id
  source_surjective := by intro x; exact ⟨x, rfl⟩
  local_noetherian := by infer_instance
  local_artinian := by infer_instance

noncomputable def oneTop : N →+
    ((j : Unit) → (Fin 1 → K)) :=
  { toFun := fun m _ _ => m.unop
    map_zero' := by ext j i; simp
    map_add' := by intro x y; ext j i; simp }

def action : R → N → N := fun r x => MulOpposite.op (x.unop * r)

theorem rightCyclic_iff_ne_zero (m : N) :
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

theorem one_top_li_iff (m : N) (j : Unit) :
    LinearIndependent K (oneTop m j) ↔ m.unop ≠ 0 := by
  rw [linearIndependent_unique_iff]
  constructor
  · intro h hm
    exact h (by simp [oneTop, hm])
  · intro hm hzero
    apply hm
    simpa [oneTop] using hzero

example (u : N) :
    ∃ z : K, z ∉ (∅ : Set K) ∧
      RightCyclic (R := R) ((1 : N) + z • u) ∧
      action 0 ((1 : N) + z • u) + z • action 1 (1 : N) = z • (1 : N) := by
  let ι : (j : Unit) → K →+* K := fun _ => RingHom.id K
  have hmap : ∀ (z : K) (m : N) (j : Unit) (i : Fin 1),
      oneTop (z • m) j i = (ι j z) • oneTop m j i := by
    intro z m j i
    simp [oneTop, ι, Algebra.smul_def, mul_comm]
  have htop : ∀ m : N,
      (∀ j : Unit, LinearIndependent K (oneTop m j)) ↔
        RightCyclic (R := R)
          ((Module.jacobson Rᵐᵒᵖ N).mkQ m) := by
    intro m
    rw [← rightCyclic_iff_jacobson_quotient (R := R) m]
    constructor
    · intro h
      have hm : m.unop ≠ 0 := by
        intro hm0
        have hz := h ()
        exact (one_top_li_iff m ()).mp hz (by simp [hm0])
      exact (rightCyclic_iff_ne_zero m).mpr (by
        intro hm0
        exact hm (congrArg MulOpposite.unop hm0))
    · intro hm j
      exact (one_top_li_iff m j).mpr
        (by simpa using (rightCyclic_iff_ne_zero m).mp hm)
  have hv : ∀ j : Unit, LinearIndependent K (oneTop (1 : N) j) := by
    intro j
    exact (one_top_li_iff _ _).mpr (by simp)
  obtain ⟨z, hz, hcyc, hrel⟩ :=
    exists_activated_right_cyclic_of_minimalPrime_local_finite_central_isotypic
      localInput (ι := ι) oneTop hmap
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
      action
      (by intro r x y; apply MulOpposite.unop_injective; simp [action, add_mul])
      (by
        intro k m r
        apply MulOpposite.unop_injective
        simp [action, Algebra.smul_def, mul_comm, mul_assoc])
      (1 : N) u 1 1 0 (by simp [action]) (by simp [action]) hv ∅
      Set.finite_empty
  have hordered :
      action 0 ((1 : N) + z • u) + z • action 1 (1 : N) = z • (1 : N) := by
    simpa [action, Algebra.smul_def] using hrel
  exact ⟨z, hz, hcyc, hordered⟩

end SymplecticStafford.FiniteLength.MinimalPrimeCentralActivatedOracle

#print axioms
  SymplecticStafford.FiniteLength.right_filtration_of_minimalPrime_local
#print axioms
  SymplecticStafford.FiniteLength.exists_activated_right_cyclic_of_minimalPrime_local_finite_central_isotypic
