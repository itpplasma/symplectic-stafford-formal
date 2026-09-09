import SymplecticStafford.Filtered.BoundedReesBridge
import SymplecticStafford.Filtered.M01StructuralClass
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Basic
import SymplecticStafford.Filtered.ReesGoodSubquotient

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

/-!
## A genuine affine-graded presentation

The preceding criterion is phrased in terms of homogeneous generators of each
actual ideal of the bounded Rees ring.  A different, useful way to discharge
that criterion is to give an actual affine commutative graded source and an
actual surjection onto the bounded Rees ring.  The surjection is essential:
the filtration alone does not construct it, and a completed or merely
associated-graded object cannot be substituted for its codomain.

`locallyFinite` records the finite-dimensional graded pieces needed for a
locally finite affine graded chart.  Noetherianity itself uses the affine
finite-type field; this is intentional, since finite type over a Noetherian
field is the precise Noetherian input.  `homogeneous_lift` records that the
surjection really respects the specified bounded homogeneous terms rather
than being an unrelated quotient map.
-/

structure LocallyFiniteAffineGradedRing
    (K : Type u) (G : Type v) [Field K] [CommRing G] [Algebra K G] where
  pieces : ℕ → Submodule K G
  graded : GradedAlgebra pieces
  locallyFinite : ∀ n : ℕ, Module.Finite K (pieces n)
  affine : Algebra.FiniteType K G

namespace LocallyFiniteAffineGradedRing

variable {K : Type u} {G : Type v} [Field K] [CommRing G] [Algebra K G]

theorem isNoetherianRing (C : LocallyFiniteAffineGradedRing K G) :
    IsNoetherianRing G := by
  letI : Algebra.FiniteType K G := C.affine
  exact Algebra.FiniteType.isNoetherianRing K G

end LocallyFiniteAffineGradedRing

section AffineGradedPresentation

variable {K : Type u} {G : Type v} [Field K] [CommRing G] [Algebra K G]
variable {R : Type w} [Ring R]

/-- An actual affine-graded presentation of the bounded Rees ring. -/
structure BoundedReesRingPresentation
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R) where
  toRingHom : G →+* ReesRing F
  surjective : Function.Surjective toRingHom
  /-- Every homogeneous source element has a bounded homogeneous lift. -/
  homogeneous_lift : ∀ n : ℕ, ∀ x : C.pieces n,
    ∃ (a : R) (ha : a ∈ F.carrier n),
      toRingHom (x : G) = ReesRing.homogeneousLift F n a ha

theorem BoundedReesRingPresentation.isNoetherianRing
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (P : BoundedReesRingPresentation C F) :
    IsNoetherianRing (ReesRing F) := by
  letI : IsNoetherianRing G := C.isNoetherianRing
  exact isNoetherianRing_of_surjective G (ReesRing F)
    P.toRingHom P.surjective

end AffineGradedPresentation

section AffineGradedModulePresentation

variable {K : Type u} {G : Type v} [Field K] [CommRing G] [Algebra K G]
variable {R : Type w} [Ring R]
variable {P M : Type w} [AddCommGroup P] [AddCommGroup M] [Module G P]

/--
Noetherianity transfer for an actual bounded-Rees module.  The target module
structure and the semilinear map are parameters because the current bounded
module-term construction has only a `ReesQuotient` action, not an action of
`ReesRing`.  An application must therefore supply the actual target module
and its surjective semilinear presentation.
-/
theorem isNoetherianModule_of_affineGraded_surjective
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (σ : G →+* ReesRing F) [RingHomSurjective σ]
    [Module (ReesRing F) M] [Module.Finite G P]
    (f : P →ₛₗ[σ] M) (hf : LinearMap.range f = ⊤) :
    IsNoetherian (ReesRing F) M := by
  letI : IsNoetherianRing G := C.isNoetherianRing
  exact isNoetherian_of_surjective f hf

theorem boundedReesModuleCertificate_of_affineGraded_surjective
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (σ : G →+* ReesRing F) [RingHomSurjective σ]
    [Module (ReesRing F) M] [Module.Finite G P]
    (f : P →ₛₗ[σ] M) (hf : LinearMap.range f = ⊤) :
    Nonempty (ReesModuleNoetherianCertificate (ReesRing F) M) := by
  letI : IsNoetherian (ReesRing F) M :=
    isNoetherianModule_of_affineGraded_surjective C F σ f hf
  exact ⟨noetherianModuleCertificate⟩

end AffineGradedModulePresentation

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.AdditiveFilteredRingData.ideal_eq_span_of_homogeneous_lifting
#print axioms SymplecticStafford.Filtered.AdditiveFilteredRingData.isNoetherianRing_of_homogeneous_lifting
