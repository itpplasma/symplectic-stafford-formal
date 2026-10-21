module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import SymplecticStafford.Ordered.SupportUnion

@[expose] public section

/-!
# The finite-generation bridge for the ordered common-colon ideal

`SupportUnion.lean` provides the finite-span and conditional support boundary.
This file records the exact bridge between a finite generator membership
witness and actual membership in a right ideal.  It is useful to consumers
which have generators from a localization or finite-module argument: the
bridge still requires the generators and the span-covering inclusion as
explicit data.

No characteristic support, localization theorem, source producer, or
universal M08 conclusion is asserted here.
-/

namespace SymplecticStafford.Ordered

universe u

variable {R : Type u} [Semiring R]

open BigOperators

/- A generator membership/cover datum is deliberately weaker than a hidden
   finite-generation typeclass.  The first field is checked in the actual
   right ideal and the second covers every actual ideal element. -/
def FiniteGeneratorData (I : RightIdeal (R := R)) : Prop :=
  ∃ gs : Finset R,
    (∀ g ∈ gs, g ∈ I) ∧ I.carrier ⊆ finiteRightSpan gs

theorem finite_span_mem_of_generator_mem
    {I : RightIdeal (R := R)} {gs : Finset R}
    (hgen : ∀ g ∈ gs, g ∈ I) {c : R → R} :
    (∑ g ∈ gs, g * c g) ∈ I := by
  apply finiteRightSpan_subset_of_mem hgen
  exact ⟨c, rfl⟩

theorem finite_generator_data_of_generation
    {I : RightIdeal (R := R)}
    (W : FiniteRightGeneration (R := R) I) :
    FiniteGeneratorData I := by
  refine ⟨W.generators, finiteRightGeneration_generator_mem W, ?_⟩
  intro x hx
  exact (W.mem_iff x).mp hx

theorem generation_of_finite_generator_data
    {I : RightIdeal (R := R)}
    (hdata : FiniteGeneratorData I) :
    Nonempty (FiniteRightGeneration (R := R) I) := by
  rcases hdata with ⟨gs, hgen, hcover⟩
  refine ⟨⟨gs, ?_⟩⟩
  intro x
  constructor
  · intro hx
    exact hcover hx
  · intro hx
    exact finiteRightSpan_subset_of_mem hgen hx

theorem finiteRightGeneration_iff_generator_data
    (I : RightIdeal (R := R)) :
    Nonempty (FiniteRightGeneration (R := R) I) ↔ FiniteGeneratorData I := by
  constructor
  · rintro ⟨W⟩
    exact finite_generator_data_of_generation W
  · exact generation_of_finite_generator_data

/- An ideal inclusion transports a finite generator datum to finite-span
   containment in the target.  This is the set/ideal bridge used by the
   affine-pencil consumer. -/
theorem finite_span_subset_of_ideal_subset
    {I J : RightIdeal (R := R)} {gs : Finset R}
    (hgen : ∀ g ∈ gs, g ∈ I) (hIJ : I.carrier ⊆ J.carrier) :
    finiteRightSpan gs ⊆ J.carrier := by
  intro x hx
  apply hIJ
  exact finiteRightSpan_subset_of_mem hgen hx

section Ring

variable {R : Type u} [Ring R]

theorem common_generator_mem_affine
    (d F G t : R)
    (W : FiniteRightGeneration (R := R) (commonRightIdeal d F G))
    (hcentral : ∀ x : R, t * x = x * t) :
    ∀ g ∈ W.generators,
      g ∈ (twoGeneratedRightIdeal d (F + t * G)).carrier := by
  intro g hg
  apply commonIdeal_subset_affineRightIdeal d F G t hcentral
  exact finiteRightGeneration_generator_mem W g hg

theorem common_generator_data_affine_span
    (d F G t : R)
    (W : FiniteRightGeneration (R := R) (commonRightIdeal d F G))
    (hcentral : ∀ x : R, t * x = x * t) :
    finiteRightSpan W.generators ⊆
      (twoGeneratedRightIdeal d (F + t * G)).carrier := by
  exact finite_span_subset_of_ideal_subset
    (finiteRightGeneration_generator_mem W)
    (commonIdeal_subset_affineRightIdeal d F G t hcentral)

end Ring

end SymplecticStafford.Ordered

#print axioms SymplecticStafford.Ordered.finite_span_mem_of_generator_mem
#print axioms SymplecticStafford.Ordered.finiteRightGeneration_iff_generator_data
#print axioms SymplecticStafford.Ordered.finite_span_subset_of_ideal_subset
#print axioms SymplecticStafford.Ordered.common_generator_data_affine_span
