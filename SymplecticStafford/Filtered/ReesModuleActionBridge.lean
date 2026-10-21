module

public import SymplecticStafford.Filtered.ReesNoetherianTransfer

@[expose] public section

/-!
# An actual bounded-Rees module action

`ReesModule.lean` checks the action of a *single bounded term* on the
value-quotient of a filtered module.  A polynomial in the bounded Rees ring is
not itself a term, so that interface cannot be used as a `Module (ReesRing F)
M` instance.  This file records the smallest honest bridge for the action
which is available without constructing an associated graded module: evaluate
the central Rees variable at `1`.

The resulting action is the restriction of scalars along an actual ring
homomorphism `ReesRing F →+* R`.  It is therefore a genuine module action,
but it is deliberately not called the filtered/Rees module action.  The
latter needs a separate algebraic identification.  A second structure below
packages the exact semilinear and finite-source hypotheses needed by the
Noetherian transfer, with the evaluation action constructed rather than
silently assumed.
-/

namespace SymplecticStafford.Filtered

universe u v w

noncomputable section

variable {R : Type u} [Ring R]

namespace ReesRing

/- The monoid map sending every degree to the unit. -/
def degreeOneMonoidHom : Multiplicative ℕ →* R where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := by intro _ _; simp

theorem degreeOneMonoidHom_apply (n : Multiplicative ℕ) :
    degreeOneMonoidHom (R := R) n = 1 := rfl

/- Evaluation at the central value `1`.  The displayed commutation condition
   is discharged from the scoped trivial degree action used by ReesPolynomial.
-/
def polynomialEvaluationAtOne : ReesPolynomial R →+* R :=
  SkewMonoidAlgebra.liftNCRingHom (RingHom.id R)
    (degreeOneMonoidHom (R := R)) (by
    intro x y
    change x * 1 = 1 * x
    simp)

theorem polynomialEvaluationAtOne_single
    (n : Multiplicative ℕ) (a : R) :
    polynomialEvaluationAtOne (R := R)
        (SkewMonoidAlgebra.single n a) = a := by
  simp [polynomialEvaluationAtOne, SkewMonoidAlgebra.liftNCRingHom,
    SkewMonoidAlgebra.liftNC, degreeOneMonoidHom]

/- The action-relevant ring map on the actual bounded subring. -/
def evaluationAtOne (F : NegFiltrationData R) : ReesRing F →+* R :=
  (polynomialEvaluationAtOne (R := R)).comp (ReesRing.inclusion F)

@[simp] theorem evaluationAtOne_monomial
    (F : NegFiltrationData R) (n : ℕ) (a : R)
    (ha : a ∈ F.carrier n) :
    evaluationAtOne F (ReesRing.monomial F n a ha) = a := by
  rw [evaluationAtOne, RingHom.comp_apply]
  exact polynomialEvaluationAtOne_single (R := R)
    (Multiplicative.ofAdd n) a

@[simp] theorem evaluationAtOne_zero (F : NegFiltrationData R) :
    evaluationAtOne F 0 = 0 := by
  exact (evaluationAtOne F).map_zero

@[simp] theorem evaluationAtOne_one (F : NegFiltrationData R) :
    evaluationAtOne F 1 = 1 := by
  exact (evaluationAtOne F).map_one

/- Restriction of scalars gives an actual `Module (ReesRing F) M`. -/
abbrev moduleViaEvaluationAtOne (F : NegFiltrationData R) (M : Type v)
    [AddCommMonoid M] [Module R M] : Module (ReesRing F) M :=
  Module.compHom M (evaluationAtOne F)

theorem smul_viaEvaluationAtOne (F : NegFiltrationData R) (M : Type v)
    [AddCommMonoid M] [Module R M]
    (c : ReesRing F) (x : M) :
    letI : Module (ReesRing F) M := moduleViaEvaluationAtOne F M
    c • x = evaluationAtOne F c • x := rfl

end ReesRing

/-!
## Explicit finite-source semilinear bridge

The existing transfer theorem accepts a semilinear map after a target module
instance has been supplied.  The structure below states the same data before
that instance is installed, using the explicit evaluation action.  This
prevents an arbitrary, unrelated `Module (ReesRing F) M` instance from being
used accidentally.
-/

section EvaluationPresentation

variable {K : Type u} {G : Type v} [Field K] [CommRing G] [Algebra K G]
variable {Q : Type w} {M : Type u}
variable [AddCommGroup Q] [AddCommGroup M] [Module G Q] [Module R M]

structure EvaluationSemilinearPresentation
    (F : NegFiltrationData R) (σ : G →+* ReesRing F) where
  toFun : Q → M
  map_zero' : toFun 0 = 0
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : G) (x : Q),
    toFun (c • x) = ReesRing.evaluationAtOne F (σ c) • toFun x
  surjective : Function.Surjective toFun

theorem isNoetherianModule_of_affineGraded_surjective_via_evaluation
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (σ : G →+* ReesRing F) (hσ : Function.Surjective σ)
    (M : Type u)
    [AddCommGroup M] [Module R M]
    [Module.Finite G Q]
    (f : EvaluationSemilinearPresentation (R := R) (G := G) (Q := Q)
      (M := M) F σ) :
  letI : Module (ReesRing F) M := ReesRing.moduleViaEvaluationAtOne (R := R) F M;
    IsNoetherian (ReesRing F) M := by
  letI : IsNoetherianRing G := C.isNoetherianRing
  letI : RingHomSurjective σ := ⟨hσ⟩
  letI : Module (ReesRing F) M :=
    ReesRing.moduleViaEvaluationAtOne (R := R) F M
  let f' : Q →ₛₗ[σ] M :=
    { toFun := f.toFun
      map_add' := f.map_add'
      map_smul' := by
        intro c x
        exact f.map_smul' c x }
  exact isNoetherian_of_surjective f'
    (LinearMap.range_eq_top.mpr f.surjective)

theorem boundedReesModuleCertificate_of_affineGraded_surjective_via_evaluation
    (C : LocallyFiniteAffineGradedRing K G)
    (F : NegFiltrationData R)
    (σ : G →+* ReesRing F) (hσ : Function.Surjective σ)
    (M : Type u)
    [AddCommGroup M] [Module R M]
    [Module.Finite G Q]
    (f : EvaluationSemilinearPresentation (R := R) (G := G) (Q := Q)
      (M := M) F σ) :
    letI : Module (ReesRing F) M := ReesRing.moduleViaEvaluationAtOne (R := R) F M;
    Nonempty (ReesModuleNoetherianCertificate (ReesRing F) M) := by
  letI : Module (ReesRing F) M :=
    ReesRing.moduleViaEvaluationAtOne (R := R) F M
  letI : IsNoetherian (ReesRing F) M :=
    isNoetherianModule_of_affineGraded_surjective_via_evaluation
      C F σ hσ M f
  exact ⟨noetherianModuleCertificate⟩

end EvaluationPresentation

end

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.ReesRing.polynomialEvaluationAtOne
#print axioms SymplecticStafford.Filtered.ReesRing.evaluationAtOne_monomial
#print axioms
  SymplecticStafford.Filtered.isNoetherianModule_of_affineGraded_surjective_via_evaluation
