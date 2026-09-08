import Mathlib.Data.Fintype.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import SymplecticStafford.Ordered.M08SupportUnion

/-!
# Boundary for the M08 support-union producer

Finite generation, the ordered affine certificate, and an auxiliary-divisor
relation are algebraic inputs.  They do not by themselves imply a support
union: a characteristic-support transfer/exclusion theorem is still needed.
This file gives a finite noncommutative matrix model with the algebraic data
and a support map for which the union conclusion fails.
-/

namespace SymplecticStafford.Ordered

/- Every right ideal in a finite ring has a finite right-generation witness.
This elementary lemma is used only to avoid hiding finite generation in the
matrix boundary example. -/
theorem finite_right_generation_of_fintype
    {R : Type*} [Ring R] [Fintype R] [DecidableEq R]
    (I : RightIdeal (R := R)) :
    Nonempty (FiniteRightGeneration (R := R) I) := by
  classical
  let gs : Finset R := Finset.univ.filter (fun x => x ∈ I)
  refine ⟨{ generators := gs, mem_iff := ?_ }⟩
  intro x
  constructor
  · intro hx
    have hxgs : x ∈ gs := by
      simp [gs, hx]
    refine ⟨fun y => if y = x then 1 else 0, ?_⟩
    simp [hxgs, gs]
  · intro hx
    rcases hx with ⟨c, hc⟩
    have hxspan : x ∈ finiteRightSpan gs := ⟨c, hc⟩
    apply finiteRightSpan_subset_of_mem (gs := gs) (I := I)
    · intro g hg
      have hg' : g ∈ Finset.univ.filter (fun y => y ∈ I) := by
        simpa [gs] using hg
      exact (Finset.mem_filter.1 hg').2
    · exact hxspan

abbrev R := Matrix (Fin 4) (Fin 4) (ZMod 2)
abbrev X := Unit

def d : R := fun i j => if i = 0 ∧ j = 0 then 1 else
  if i = 1 ∧ j = 1 then 1 else 0

def F : R := fun i j =>
  if (i = 2 ∨ i = 3) ∧ (j = 0 ∨ j = 1) then 1 else 0

def G : R := fun i j => if (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) then 1 else 0

def L : R := fun i j => if (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) then 1 else 0

def e : R := fun i j => if (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 0) then 1 else 0

def P : R := fun i j => if i = 0 ∧ j = 0 then 1 else 0

noncomputable def supportMissing (I : RightIdeal (R := R)) : Set X := by
  classical
  exact if e ∈ I.carrier then ∅ else Set.univ

theorem d_ne_zero : d ≠ 0 := by
  intro h
  have := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 4)
  simp [d] at this

theorem common_eq_d_right :
    commonRightIdeal d F G = twoGeneratedRightIdeal d 0 := by
  apply RightIdeal.ext
  intro x
  constructor
  · intro hx
    change ∃ r k : R, k ∈ commonColon d G ∧
      x = d * r + (F * d) * k at hx
    rcases hx with ⟨r, k, hk, hx⟩
    refine ⟨r, 0, ?_⟩
    have hzero : (F * d) * k = 0 := by
      rcases hk with ⟨c, hc⟩
      have hk0 : ∀ j : Fin 4, k 0 j = 0 := by
        intro j
        have h := congrFun (congrFun hc (2 : Fin 4)) j
        simpa [G, d, Matrix.mul_apply, Fin.sum_univ_succ] using h
      have hk1 : ∀ j : Fin 4, k 1 j = 0 := by
        intro j
        have h := congrFun (congrFun hc (3 : Fin 4)) j
        simpa [G, d, Matrix.mul_apply, Fin.sum_univ_succ] using h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [F, d, Matrix.mul_apply, Fin.sum_univ_succ, hk0, hk1]
    rw [hx, hzero]
    simp
  · intro hx
    change ∃ r k : R, k ∈ commonColon d G ∧
      x = d * r + (F * d) * k
    rcases hx with ⟨r, s, hs⟩
    refine ⟨r, 0, commonColon_zero_mem d G, ?_⟩
    simpa using hs

theorem branch_contains_e : e ∈ (twoGeneratedRightIdeal d F).carrier := by
  refine ⟨0, P, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, F, d, P, Matrix.mul_apply, Fin.sum_univ_succ]

theorem common_omits_e : e ∉ (commonRightIdeal d F G).carrier := by
  rw [common_eq_d_right]
  intro h
  rcases h with ⟨r, s, hs⟩
  have hentry := congrFun (congrFun hs (2 : Fin 4)) (0 : Fin 4)
  simp [e, d, Matrix.mul_apply, Fin.sum_univ_succ] at hentry

theorem first_branch_support_empty :
    supportMissing (twoGeneratedRightIdeal d F) = (∅ : Set X) := by
  classical
  unfold supportMissing
  rw [if_pos branch_contains_e]

theorem common_support_full :
    supportMissing (commonRightIdeal d F G) = Set.univ := by
  classical
  unfold supportMissing
  rw [if_neg common_omits_e]

def aux_relation :
    AuxiliaryDivisorRelation (R := R) d F G L :=
  ⟨0, by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [F, d, L, Matrix.mul_apply, Fin.sum_univ_succ] <;> decide⟩

theorem second_branch_support_empty :
    supportMissing (twoGeneratedRightIdeal (d * L) G) = (∅ : Set X) := by
  classical
  unfold supportMissing
  apply if_pos
  refine ⟨0, ?_, ?_⟩
  · exact P
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, G, d, L, P, Matrix.mul_apply, Fin.sum_univ_succ]

theorem support_union_conclusion_fails :
    ¬ (supportMissing (commonRightIdeal d F G) ⊆
      supportMissing (twoGeneratedRightIdeal d F) ∪
        supportMissing (twoGeneratedRightIdeal (d * L) G)) := by
  rw [common_support_full, first_branch_support_empty,
    second_branch_support_empty]
  simp

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.support_union_conclusion_fails
