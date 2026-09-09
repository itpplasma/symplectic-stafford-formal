import SymplecticStafford.Filtered.BoundedReesBridge
import SymplecticStafford.Filtered.M01StructuralClass

/-!
# Explicit filtered-to-Rees Noetherian transfer

`AdditiveFilteredRingData` is the natural structural filtration interface,
while `ReesRing` consumes its set-valued `NegFiltrationData` projection.  This
file packages the exact additional M02 input needed to transfer finite
homogeneous generation to the bounded Rees ring: each actual ideal has a
finite set of generators, and every homogeneous component of each element of
that ideal lies in the corresponding generator span after lifting.

The component hypothesis is deliberately element-dependent.  Requiring all
homogeneous terms of the ambient ring to lie in the span of generators of an
arbitrary ideal would incorrectly force every ideal to be the whole ring.
Noetherianity of the associated graded object, or its identification with
this bounded Rees ring, is not inferred here.
-/

namespace SymplecticStafford.Filtered

universe u

noncomputable section

variable {R : Type u} [Ring R]

namespace AdditiveFilteredRingData

variable (F : AdditiveFilteredRingData R)

abbrev boundedReesRing := ReesRing F.toNegFiltrationData

structure HomogeneousIdealLifting where
  generators : ∀ _I : Ideal (boundedReesRing F), Finset (boundedReesRing F)
  generators_mem : ∀ (I : Ideal (boundedReesRing F)) {x : boundedReesRing F},
    x ∈ generators I → x ∈ I
  component_mem_span : ∀ (I : Ideal (boundedReesRing F))
    (p : boundedReesRing F), p ∈ I → ∀ n : ℕ,
      ReesRing.homogeneousLift F.toNegFiltrationData n
          ((p : ReesPolynomial R).coeff n) (p.property n) ∈
        Ideal.span (generators I : Set (boundedReesRing F))

theorem ideal_eq_span_of_homogeneous_lifting
    (H : HomogeneousIdealLifting F) (I : Ideal (boundedReesRing F)) :
    I = Ideal.span (H.generators I : Set (boundedReesRing F)) := by
  apply ReesRing.ideal_eq_span_of_homogeneous_mem F.toNegFiltrationData I
    (H.generators I) (by
      intro x hx
      exact H.generators_mem I hx) (H.component_mem_span I)

theorem isNoetherianRing_of_homogeneous_lifting
    (H : HomogeneousIdealLifting F) :
    IsNoetherianRing (boundedReesRing F) := by
  apply isNoetherianRing_of_finite_homogeneous_ideal_generators
    F.toNegFiltrationData
  intro I
  refine ⟨H.generators I, ?_, ?_⟩
  · intro x hx
    exact H.generators_mem I hx
  exact H.component_mem_span I

end AdditiveFilteredRingData

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.AdditiveFilteredRingData.ideal_eq_span_of_homogeneous_lifting
#print axioms SymplecticStafford.Filtered.AdditiveFilteredRingData.isNoetherianRing_of_homogeneous_lifting
