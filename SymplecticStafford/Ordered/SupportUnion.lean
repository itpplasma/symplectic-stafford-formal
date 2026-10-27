module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Defs
public import SymplecticStafford.Ordered.CommonColon
public import SymplecticStafford.Ordered.RightClear

@[expose] public section

/-!
# Finite generators and the conditional M08 support-union interface

This file adds the finite-generator and denominator-clearing boundary around
the ordered common-colon construction.  `K` and `J` remain the definitions in
`Ordered.CommonColon`; no factor is commuted, and no source or characteristic
support is constructed here.

The support-union consumer is intentionally a supplied hypothesis.  Its
purpose is to make the exact geometric input and the algebraic output visible
to later work, rather than silently turning a support slogan into a theorem.
-/

namespace SymplecticStafford.Ordered

universe u v

variable {R : Type u} [Semiring R]

open BigOperators

/- A finite right span uses finite sums of right multiples.  This is the
   correct finite-generator notion for a possibly noncommutative right ideal;
   membership is not incorrectly reduced to one generator times one scalar. -/
def finiteRightSpan (gs : Finset R) : Set R :=
  {x | ∃ c : R → R, x = ∑ g ∈ gs, g * c g}

theorem mem_finiteRightSpan_iff (gs : Finset R) (x : R) :
    x ∈ finiteRightSpan gs ↔ ∃ c : R → R, x = ∑ g ∈ gs, g * c g := Iff.rfl

theorem finiteRightSpan_zero_mem (gs : Finset R) :
    (0 : R) ∈ finiteRightSpan gs := by
  refine ⟨fun _ => 0, ?_⟩
  simp

theorem finiteRightSpan_add_mem {gs : Finset R} {x y : R}
    (hx : x ∈ finiteRightSpan gs) (hy : y ∈ finiteRightSpan gs) :
    x + y ∈ finiteRightSpan gs := by
  rcases hx with ⟨cx, hcx⟩
  rcases hy with ⟨cy, hcy⟩
  refine ⟨fun g => cx g + cy g, ?_⟩
  rw [hcx, hcy]
  simp only [Finset.sum_add_distrib, mul_add]

theorem finiteRightSpan_right_mul_mem {gs : Finset R} {x q : R}
    (hx : x ∈ finiteRightSpan gs) :
    x * q ∈ finiteRightSpan gs := by
  rcases hx with ⟨c, hc⟩
  refine ⟨fun g => c g * q, ?_⟩
  rw [hc]
  simp only [Finset.sum_mul, mul_assoc]

/- The finite span itself is a right ideal.  This packages the preceding set
   closure proofs without identifying it with any geometric or localized
   ideal. -/
def finiteRightSpanRightIdeal (gs : Finset R) : RightIdeal (R := R) where
  carrier := finiteRightSpan gs
  zero_mem := finiteRightSpan_zero_mem gs
  add_mem := by
    intro a b ha hb
    exact finiteRightSpan_add_mem ha hb
  right_mul_mem := by
    intro a ha q
    exact finiteRightSpan_right_mul_mem ha

theorem mem_finiteRightSpanRightIdeal_iff (gs : Finset R) (x : R) :
    x ∈ finiteRightSpanRightIdeal gs ↔ x ∈ finiteRightSpan gs := Iff.rfl

/- A finite-generation witness is data, not an assumption hidden in a
   characteristic-support definition. -/
structure FiniteRightGeneration (I : RightIdeal (R := R)) where
  generators : Finset R
  mem_iff : ∀ x : R, x ∈ I ↔ x ∈ finiteRightSpan generators

theorem finiteRightSpan_subset_of_mem
    {gs : Finset R} {I : RightIdeal (R := R)}
    (hgen : ∀ g ∈ gs, g ∈ I) :
    finiteRightSpan gs ⊆ I.carrier := by
  classical
  intro x hx
  rcases hx with ⟨c, rfl⟩
  induction gs using Finset.induction_on with
  | empty => exact I.zero_mem
  | @insert a gs ha ih =>
      simp only [Finset.sum_insert ha]
      apply I.add_mem
      · exact I.right_mul_mem (hgen a (by simp)) (c a)
      · apply ih
        intro g hg
        exact hgen g (by simp [hg])

theorem finiteRightGeneration_generator_mem
    (W : FiniteRightGeneration (R := R) I) :
    ∀ g ∈ W.generators, g ∈ I := by
  classical
  intro g hg
  apply (W.mem_iff g).mpr
  refine ⟨fun h => if h = g then 1 else 0, ?_⟩
  simp [hg]

theorem finiteRightGeneration_span_eq
    (W : FiniteRightGeneration (R := R) I) :
    finiteRightSpan W.generators = I.carrier := by
  ext x
  exact (W.mem_iff x).symm

section Ring

variable {R : Type u} [Ring R]

theorem finite_commonIdeal_subset_affine
    (d F G t : R)
    (W : FiniteRightGeneration (R := R) (commonRightIdeal d F G))
    (hcentral : ∀ x : R, t * x = x * t) :
    finiteRightSpan W.generators ⊆
      (twoGeneratedRightIdeal d (F + t * G)).carrier := by
  rw [finiteRightGeneration_span_eq W]
  exact commonIdeal_subset_affineRightIdeal d F G t hcentral

end Ring

/- The source-side auxiliary relation used by the paper's second support
   branch.  The equality is retained in original `R`; it is not a completed or
   localized relation. -/
structure AuxiliaryDivisorRelation (d F G L : R) where
  C : R
  relation : F * d * L = d * C

def supportUnionInput {X : Type v} (support : RightIdeal (R := R) → Set X)
    (d F G L : R) : Prop :=
  ∃ C : R, F * d * L = d * C ∧
    support (commonRightIdeal d F G) ⊆
      support (twoGeneratedRightIdeal d F) ∪
        support (twoGeneratedRightIdeal (d * L) G)

theorem supportUnionInput_of_relation_and_support
    {X : Type v} (support : RightIdeal (R := R) → Set X)
    (d F G L : R) (A : AuxiliaryDivisorRelation d F G L)
    (hsupport : support (commonRightIdeal d F G) ⊆
      support (twoGeneratedRightIdeal d F) ∪
        support (twoGeneratedRightIdeal (d * L) G)) :
    supportUnionInput support d F G L :=
  ⟨A.C, A.relation, hsupport⟩

theorem support_union_of_input
    {X : Type v} (support : RightIdeal (R := R) → Set X)
    (d F G L : R) (h : supportUnionInput support d F G L) :
    support (commonRightIdeal d F G) ⊆
      support (twoGeneratedRightIdeal d F) ∪
        support (twoGeneratedRightIdeal (d * L) G) := by
  exact h.choose_spec.2

/- A finite set of ambient coefficients can be cleared by one constant right
   denominator power.  The per-element clearability is explicit and the
   conclusion keeps the multiplication on the right. -/
def FiniteRightClearance {S : Type v} [Monoid S]
    (ι : R →* S) (f : R) (xs : Finset S) : Prop :=
  ∃ n : ℕ, ∀ x ∈ xs, ∃ y : R, x * (ι f) ^ n = ι y

theorem finiteRightClearance_of_pointwise
    {S : Type v} [Monoid S] [DecidableEq S]
    (ι : R →* S) (f : R) (xs : Finset S)
    (h : ∀ x ∈ xs, RightClearable ι f x) :
    FiniteRightClearance ι f xs := by
  exact exists_finset_common_right_clear ι f xs h

theorem finiteRightClearance_mem
    {S : Type v} [Monoid S] [DecidableEq S]
    {ι : R →* S} {f : R} {xs : Finset S}
    (hclear : FiniteRightClearance ι f xs) :
    ∃ n : ℕ, ∀ x ∈ xs, ∃ y : R, x * (ι f) ^ n = ι y :=
  hclear

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.finiteRightSpan_subset_of_mem
#print axioms SymplecticStafford.Ordered.finite_commonIdeal_subset_affine
#print axioms SymplecticStafford.Ordered.support_union_of_input
#print axioms SymplecticStafford.Ordered.finiteRightClearance_of_pointwise
