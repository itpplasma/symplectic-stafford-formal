import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.RingTheory.Noetherian.Basic
import SymplecticStafford.Ordered.M08SupportUnion

/-!
# The actual finite-generation part of M08

The common-colon construction is a right ideal in the original ring.  The
older M08 files accepted a finite-generation witness as an input.  This file
constructs that witness from the actual right-Noetherian hypothesis, by
viewing a right ideal as a submodule over the opposite ring.  It also records
the whole source-pencil certificate for every element of the common ideal.

No localization or support theorem is hidden here: those remain separate
inputs to `CharacteristicSupportProducer`.  In particular, this file does
not turn a local source into a global source by an existential axiom.
-/

namespace SymplecticStafford.Ordered

universe u

section RightNoetherian

variable {R : Type u} [Ring R]

/- A custom right ideal is an honest opposite-ring submodule.  The scalar
action is right multiplication after unwrapping the opposite element. -/
def rightIdealSubmodule (I : RightIdeal (R := R)) : Submodule Rᵐᵒᵖ R where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' := by
    intro a b ha hb
    exact I.add_mem ha hb
  smul_mem' := by
    intro q x hx
    change x * MulOpposite.unop q ∈ I
    exact I.right_mul_mem hx (MulOpposite.unop q)

@[simp] theorem mem_rightIdealSubmodule_iff
    (I : RightIdeal (R := R)) (x : R) :
    x ∈ rightIdealSubmodule I ↔ x ∈ I := Iff.rfl

/- The explicit finite right span is also an opposite-ring submodule. -/
def finiteRightSpanSubmodule (gs : Finset R) : Submodule Rᵐᵒᵖ R where
  carrier := finiteRightSpan gs
  zero_mem' := finiteRightSpan_zero_mem gs
  add_mem' := by
    intro a b ha hb
    exact finiteRightSpan_add_mem ha hb
  smul_mem' := by
    intro q x hx
    change x * MulOpposite.unop q ∈ finiteRightSpan gs
    exact finiteRightSpan_right_mul_mem (q := MulOpposite.unop q) hx

@[simp] theorem mem_finiteRightSpanSubmodule_iff
    (gs : Finset R) (x : R) :
    x ∈ finiteRightSpanSubmodule gs ↔ x ∈ finiteRightSpan gs := Iff.rfl

theorem finiteRightSpanSubmodule_eq_span (gs : Finset R) :
    finiteRightSpanSubmodule gs =
      Submodule.span Rᵐᵒᵖ (gs : Set R) := by
  classical
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨c, hc⟩
    rw [hc]
    apply Submodule.sum_mem (Submodule.span Rᵐᵒᵖ (gs : Set R))
    intro g hg
    change g * c g ∈ Submodule.span Rᵐᵒᵖ (gs : Set R)
    have h := Submodule.smul_mem (Submodule.span Rᵐᵒᵖ (gs : Set R))
      (MulOpposite.op (c g))
      (Submodule.subset_span (by simpa using hg))
    change g * c g ∈ Submodule.span Rᵐᵒᵖ (gs : Set R) at h
    exact h
  · apply Submodule.span_le.2
    intro g hg
    have hgs : g ∈ gs := by simpa using hg
    refine ⟨fun x => if x = g then 1 else 0, ?_⟩
    simp [hgs]

theorem finiteRightGeneration_of_rightNoetherian
    [IsNoetherian Rᵐᵒᵖ R] (I : RightIdeal (R := R)) :
    Nonempty (FiniteRightGeneration (R := R) I) := by
  obtain ⟨S, hSfinite, hSspan⟩ := (Submodule.fg_def.mp
    (IsNoetherian.noetherian (rightIdealSubmodule I)))
  let gs : Finset R := hSfinite.toFinset
  have hS_eq : (S : Set R) = (gs : Set R) := by
    exact (Set.Finite.coe_toFinset hSfinite).symm
  have hspan : Submodule.span Rᵐᵒᵖ (gs : Set R) =
      rightIdealSubmodule I := by
    rw [← hSspan, ← hS_eq]
  refine ⟨⟨gs, ?_⟩⟩
  intro x
  constructor
  · intro hx
    have hx' : x ∈ rightIdealSubmodule I := hx
    have hx'' : x ∈ Submodule.span Rᵐᵒᵖ (gs : Set R) := by
      rw [hspan]
      exact hx'
    have hx''' : x ∈ finiteRightSpanSubmodule gs := by
      rw [finiteRightSpanSubmodule_eq_span]
      exact hx''
    exact hx'''
  · intro hx
    have hx' : x ∈ finiteRightSpanSubmodule gs := hx
    rw [finiteRightSpanSubmodule_eq_span gs] at hx'
    rw [hspan] at hx'
    exact hx'

theorem finiteCommonRightGeneration_of_rightNoetherian
    [IsNoetherian Rᵐᵒᵖ R] (d F G : R) :
    Nonempty (FiniteRightGeneration (R := R)
      (commonRightIdeal d F G)) :=
  finiteRightGeneration_of_rightNoetherian (commonRightIdeal d F G)

end RightNoetherian

section Pencil

variable {R : Type u} [Ring R]

/- The polynomial containment is an actual theorem in the original ring.  It
 is stated for a finite-generation witness constructed above, but does not
 need a hidden polynomial ring or a commutative coefficient assumption. -/
theorem finite_commonIdeal_generators_have_affine_certificates
    (d F G t : R)
    (W : FiniteRightGeneration (R := R) (commonRightIdeal d F G))
    (hcentral : ∀ x : R, t * x = x * t) :
    ∀ g ∈ W.generators, ∃ r s : R,
      g = d * r + (F + t * G) * d * s := by
  intro g hg
  exact affine_certificate_for_common_generator d F G W g hg t hcentral

theorem finite_commonIdeal_is_contained_in_every_affine_ideal
    (d F G t : R)
    (W : FiniteRightGeneration (R := R) (commonRightIdeal d F G))
    (hcentral : ∀ x : R, t * x = x * t) :
    commonIdeal d F G ⊆
      (twoGeneratedRightIdeal d (F + t * G)).carrier := by
  exact commonIdeal_subset_affineRightIdeal d F G t hcentral

end Pencil

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.finiteRightGeneration_of_rightNoetherian
#print axioms SymplecticStafford.Ordered.finiteCommonRightGeneration_of_rightNoetherian
#print axioms SymplecticStafford.Ordered.finite_commonIdeal_is_contained_in_every_affine_ideal
